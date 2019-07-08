#include "simulator.hh"

#include <cassert>
#include <random>
#include <sstream>

//==============================================================================
// functions
//==============================================================================

// erases a given element from a STL container
//
template<class C, class T>
inline void erase (C & container, T & val)
{
  container.erase(find(container.begin(), container.end(), val));
}

//==============================================================================
// Simulator
//==============================================================================

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

Simulator::Simulator (const Program::List::ptr & p,
                      const bound_t b,
                      const uint64_t s) :
  programs(p),
  trace(std::make_unique<Trace>(p)),
  bound(b),
  seed(s)
{
  active.reserve(programs->size());
  threads.reserve(programs->size());

  for (const Program & program : *programs)
    create_thread(program);
}

//------------------------------------------------------------------------------
// member functions
//------------------------------------------------------------------------------

// Simulator::create_thread ----------------------------------------------------

word_t Simulator::create_thread (const Program & program)
{
  // determine thread id
  word_t id = threads.size();

  // add thread to queue
  threads.push_back({*this, id, program});

  // add to checkpoint sets
  for (const auto & it : program.checkpoints)
    threads_per_checkpoint[it.first].push_back(&threads.back());

  return id;
}

// Simulator::check_and_resume -------------------------------------------------

void Simulator::check_and_resume (word_t id)
{
  // all other threads already at this checkpoint?
  if (waiting_for_checkpoint[id] == threads_per_checkpoint[id].size())
    {
      // reset number of waiting threads
      waiting_for_checkpoint[id] = 0;

      // reactivate threads
      for (Thread * t : threads_per_checkpoint[id])
        {
          t->state = Thread::State::running;
          active.push_back(t);
        }
    }
}

// Simulator::run --------------------------------------------------------------

Trace::ptr Simulator::run (std::function<Thread *()> scheduler)
{
  assert(active.empty());

  // activate threads
  for (Thread & t : threads)
    {
      t.state = Thread::State::running;
      active.push_back(&t);
    }

  bool done = active.empty();

  while (!done && (!bound || trace->bound < bound))
    {
      Thread * thread = scheduler();

      // flush store buffer or execute instruction
      if (thread->state == Thread::State::flushing)
        thread->flush();
      else
        thread->execute();

      // handle state transitions
      switch (thread->state)
        {
        // keep 'em running
        case Thread::State::running: break;

        // checkpoint reached - release if all other threads are waiting
        case Thread::State::waiting:
          {
            // remove from active threads
            erase(active, thread);

            // increment number of waiting threads
            waiting_for_checkpoint[thread->check]++;

            // all other threads already waiting at this checkpoint?
            check_and_resume(thread->check);

            break;
          }

        // halted - quit if all the others also stopped
        case Thread::State::halted:
          {
            // remove from active threads
            erase(active, thread);

            // take care if last instruction was a CHECK (bypasses WAITING)
            if (&thread->program.back().symbol() == &Instruction::Check::symbol)
              {
                // remove from list of waiting threads
                erase(threads_per_checkpoint[thread->check], thread);

                // activate all waiting threads if this was the last one
                check_and_resume(thread->check);
              }

            // check if we were the last thread standing
            done = true;

            for (const Thread & t : threads)
              if (t.state != Thread::State::halted)
                done = false;

            break;
          }

        // exiting - return exit code
        case Thread::State::exited: done = true; break;

        default:
          {
            std::ostringstream m;
            m << "illegal thread state transition "
              << static_cast<char>(Thread::State::running)
              << " -> "
              << static_cast<char>(thread->state);
            throw std::runtime_error(m.str());
          }
        }
    }

  return move(trace);
}

// Simulator::simulate ---------------------------------------------------------

Trace::ptr Simulator::simulate (const Program::List::ptr & programs,
                                const bound_t bound,
                                const bound_t seed)
{
  Simulator simulator {programs, bound, seed};

  // Mersenne Twister pseudo-random number generator
  std::mt19937_64 random(seed);

  // random scheduler
  return simulator.run([&simulator, &random] {
    Thread * t = simulator.active[random() % simulator.active.size()];

    assert(t->state == Thread::State::running);

    // rule 2, 5, 7: store buffer may be flushed at any time or must be empty
    if (t->buffer.full)
      if (random() % 2 || t->program[t->pc].requires_flush())
        t->state = Thread::State::flushing;

    return t;
  });
}

// Simulator::replay -----------------------------------------------------------

Trace::ptr Simulator::replay (const Trace & trace, const bound_t bound)
{
  Simulator simulator {
    trace.programs,
    bound && bound < trace.bound ? bound : trace.bound
  };

  // replay scheduler
  Trace::iterator iterator = trace.begin();

  return simulator.run([&simulator, &iterator] {
    if (iterator->flush)
      simulator.threads[iterator->thread].state = Thread::State::flushing;

    return &simulator.threads[iterator++->thread];
  });
}

//==============================================================================
// Thread
//==============================================================================

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

Thread::Thread (Simulator & s, const word_t i, const Program & p) :
  id(i),
  pc(0),
  mem(0),
  accu(0),
  check(0),
  state(State::initial),
  simulator(s),
  program(p)
{}

//------------------------------------------------------------------------------
// member functions
//------------------------------------------------------------------------------

// Thread::load ----------------------------------------------------------------

word_t Thread::load (word_t address, const bool indirect)
{
  if (indirect)
    address =
      buffer.full && buffer.address == address
        ? buffer.value
        : simulator.heap[address];

  return
    buffer.full && buffer.address == address
      ? buffer.value
      : simulator.heap[address];
}

// Thread::store ---------------------------------------------------------------

void Thread::store (
                    word_t address,
                    const word_t value,
                    const bool indirect,
                    const bool atomic
                   )
{
  assert(!buffer.full);

  if (indirect)
    address = load(address);

  if (atomic)
    {
      simulator.heap[address] = value;
    }
  else
    {
      buffer.full = true;
      buffer.address = address;
      buffer.value = value;
    }
}

// Thread::flush ---------------------------------------------------------------

void Thread::flush ()
{
  assert(buffer.full);
  assert(state == Thread::State::flushing);

  buffer.full = false;
  state = Thread::State::running;
  simulator.heap[buffer.address] = buffer.value;

  simulator.trace->push_back(id, {buffer.address, buffer.value});
}

// Thread::execute -------------------------------------------------------------

void Thread::execute ()
{
  if (pc >= program.size())
    throw std::runtime_error("illegal pc [" + std::to_string(pc) + "]");

  // execute instruction
  program[pc].execute(*this);

  // set state to halted if it was the last command in the program
  if (pc >= program.size())
    state = State::halted;
}

#define PUSH_BACK_ATOMIC(pc, heap) \
  simulator.trace->push_back( \
    id, \
    pc, \
    accu, \
    mem, \
    buffer.address, \
    buffer.value, \
    buffer.full, \
    heap)

#define PUSH_BACK(pc) PUSH_BACK_ATOMIC(pc, {})

void Thread::execute (const Instruction::Load & l)
{
  accu = load(l.arg, l.indirect);

  PUSH_BACK(pc++);
}

void Thread::execute (const Instruction::Store & s)
{
  store(s.arg, accu, s.indirect);

  PUSH_BACK(pc++);
}

void Thread::execute (const Instruction::Fence & f [[maybe_unused]])
{
  PUSH_BACK(pc++);
}

void Thread::execute (const Instruction::Add & a)
{
  accu += load(a.arg, a.indirect);

  PUSH_BACK(pc++);
}

void Thread::execute (const Instruction::Addi & a)
{
  accu += a.arg;

  PUSH_BACK(pc++);
}

void Thread::execute (const Instruction::Sub & s)
{
  accu -= load(s.arg, s.indirect);

  PUSH_BACK(pc++);
}

void Thread::execute (const Instruction::Subi & s)
{
  accu -= s.arg;

  PUSH_BACK(pc++);
}

void Thread::execute (const Instruction::Mul & s)
{
  accu *= load(s.arg, s.indirect);

  PUSH_BACK(pc++);
}

void Thread::execute (const Instruction::Muli & s)
{
  accu *= s.arg;

  PUSH_BACK(pc++);
}

void Thread::execute (const Instruction::Cmp & c)
{
  accu -= load(c.arg, c.indirect);

  PUSH_BACK(pc++);
}

void Thread::execute (const Instruction::Jmp & j)
{
  PUSH_BACK(pc);

  pc = j.arg;
}

void Thread::execute (const Instruction::Jz & j)
{
  PUSH_BACK(pc);

  if (accu)
    pc++;
  else
    pc = j.arg;
}

void Thread::execute (const Instruction::Jnz & j)
{
  PUSH_BACK(pc);

  if (accu)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (const Instruction::Js & j)
{
  PUSH_BACK(pc);

  if (static_cast<sword_t>(accu) < 0)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (const Instruction::Jns & j)
{
  PUSH_BACK(pc);

  if (static_cast<sword_t>(accu) >= 0)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (const Instruction::Jnzns & j)
{
  PUSH_BACK(pc);

  if (static_cast<sword_t>(accu) > 0)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (const Instruction::Mem & m)
{
  mem = accu = load(m.arg, m.indirect);

  PUSH_BACK(pc++);
}

void Thread::execute (const Instruction::Cas & c)
{
  std::optional<Trace::Heap> heap;

  if (mem == load(c.arg, c.indirect))
    {
      heap = {c.indirect ? load(c.arg) : c.arg, accu};

      store(c.arg, accu, c.indirect, true);
      accu = 1;
    }
  else
    {
      accu = 0;
    }

  PUSH_BACK_ATOMIC(pc++, heap);
}

void Thread::execute (const Instruction::Check & c)
{
  check = c.arg;
  state = State::waiting;

  PUSH_BACK(pc++);
}

void Thread::execute (const Instruction::Halt & h [[maybe_unused]])
{
  state = State::halted;

  PUSH_BACK(pc);
}

void Thread::execute (const Instruction::Exit & e)
{
  simulator.trace->exit = e.arg;
  state = State::exited;

  PUSH_BACK(pc);
}

//==============================================================================
// non-member operators
//==============================================================================

std::ostream & operator << (std::ostream & os, Thread::State s)
{
    return os << static_cast<char>(s);
}
