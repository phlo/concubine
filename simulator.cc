#include "simulator.hh"

#include <cassert>
#include <random>
#include <sstream>

using namespace std;

/* erases a given element from a STL container ********************************/
template<typename C, typename T>
inline void erase (C & container, T & val)
{
  container.erase(find(container.begin(), container.end(), val));
}

/*******************************************************************************
 * Simulator
 ******************************************************************************/
Simulator::Simulator () :
  programs(
    make_shared<Program_list>(
      initializer_list<Program_ptr>({make_shared<Program>()}))),
  schedule(make_shared<Schedule>(programs)),
  bound(0)
{}

Simulator::Simulator (Program_list_ptr p, bound_t b, uint64_t s) :
  programs(p),
  schedule(make_shared<Schedule>(p)),
  bound(b),
  seed(s)
{
  active.reserve(programs->size());
  threads.reserve(programs->size());

  for (const Program_ptr & program : * p)
    create_thread(*program);
}

/* Simulator::create_thread ***************************************************/
word_t Simulator::create_thread (Program & program)
{
  /* determine thread id */
  word_t id = threads.size();

  /* add thread to queue */
  threads.push_back({*this, id, program});

  /* add to checkpoint sets */
  for (word_t i : program.check_ids)
    threads_per_checkpoint[i].push_back(&threads.back());

  return id;
}

/* Simulator::check_and_resume ************************************************/
void Simulator::check_and_resume (word_t id)
{
  /* all other threads already at this checkpoint? */
  if (waiting_for_checkpoint[id] == threads_per_checkpoint[id].size())
    {
      /* reset number of waiting threads */
      waiting_for_checkpoint[id] = 0;

      /* reactivate threads */
      for (Thread * t : threads_per_checkpoint[id])
        {
          t->state = Thread::State::running;
          active.push_back(t);
        }
    }
}

/* Simulator::run *************************************************************/
Schedule_ptr Simulator::run (function<Thread *()> scheduler)
{
  assert(active.empty());

  /* activate threads */
  for (Thread & t : threads)
    {
      t.state = Thread::State::running;
      active.push_back(&t);
    }

  bool done = active.empty();

  while (!done && (!bound || schedule->bound < bound))
    {
      Thread * thread = scheduler();

      /* flush store buffer or execute instruction */
      if (thread->state == Thread::State::flushing)
        thread->flush();
      else
        thread->execute();

      /* handle state transitions */
      switch (thread->state)
        {
        /* keep 'em running */
        case Thread::State::running: break;

        /* checkpoint reached - release if all other threads are waiting */
        case Thread::State::waiting:
          {
            /* remove from active threads */
            erase(active, thread);

            /* increment number of waiting threads */
            waiting_for_checkpoint[thread->check]++;

            /* all other threads already waiting at this checkpoint? */
            check_and_resume(thread->check);

            break;
          }

        /* halted - quit if all the others also stopped */
        case Thread::State::halted:
          {
            /* remove from active threads */
            erase(active, thread);

            /* take care if last instruction was a CHECK (bypasses WAITING) */
            if (dynamic_pointer_cast<Check>(thread->program.back()))
              {
                /* remove from list of waiting threads */
                erase(threads_per_checkpoint[thread->check], thread);

                /* activate all waiting threads if this was the last one */
                check_and_resume(thread->check);
              }

            /* check if we were the last thread standing */
            done = true;

            for (const Thread & t : threads)
              if (t.state != Thread::State::halted)
                done = false;

            break;
          }

        /* exiting - return exit code */
        case Thread::State::exited:
          {
            done = true;
            schedule->exit = static_cast<int>(thread->accu);
            break;
          }

        default:
          {
            ostringstream m;
            m << "illegal thread state transition "
              << static_cast<char>(Thread::State::running)
              << " -> "
              << static_cast<char>(thread->state);
            throw runtime_error(m.str());
          }
        }
    }

  return schedule;
}

/* Simulator::simulate ********************************************************/
Schedule_ptr Simulator::simulate (
                                  const Program_list_ptr programs,
                                  const bound_t bound,
                                  const bound_t seed
                                 )
{
  Simulator simulator {programs, bound, seed};

  /* Mersenne Twister pseudo-random number generator */
  mt19937_64 random(seed);

  /* random scheduler */
  return simulator.run([&simulator, &random] {
    Thread * t = simulator.active[random() % simulator.active.size()];

    assert(t->state == Thread::State::running);

    /* rule 2, 5, 7: store buffer may be flushed at any time or must be empty */
    if (t->buffer.full)
      if (random() % 2 || t->program[t->pc]->requires_flush())
        t->state = Thread::State::flushing;

    return t;
  });
}

/* Simulator::replay **********************************************************/
Schedule_ptr Simulator::replay (const Schedule & schedule, const bound_t bound)
{
  Simulator simulator {
    schedule.programs,
    bound && bound < schedule.bound ? bound : schedule.bound
  };

  /* replay scheduler */
  Schedule::iterator iterator = schedule.begin();

  return simulator.run([&simulator, &iterator] {
    if (iterator->flush)
      simulator.threads[iterator->thread].state = Thread::State::flushing;

    return &simulator.threads[iterator++->thread];
  });
}

/*******************************************************************************
 * Thread
 ******************************************************************************/
Thread::Thread (Simulator & s, word_t i, Program & p) :
  id(i),
  pc(0),
  mem(0),
  accu(0),
  check(0),
  state(State::initial),
  simulator(s),
  program(p)
{}

/* Thread::load ***************************************************************/
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

/* Thread::store **************************************************************/
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

/* Thread::flush **************************************************************/
void Thread::flush ()
{
  assert(buffer.full);
  assert(state == Thread::State::flushing);

  buffer.full = false;
  state = Thread::State::running;
  simulator.heap[buffer.address] = buffer.value;

  simulator.schedule->push_back(id, {buffer.address, buffer.value});
}

/* Thread::execute ************************************************************/
void Thread::execute ()
{
  if (pc >= program.size())
    throw runtime_error("illegal pc [" + to_string(pc) + "]");

  /* execute instruction */
  program.at(pc)->execute(*this);

  /* set state to halted if it was the last command in the program */
  if (pc >= program.size())
    state = State::halted;
}

#define PUSH_BACK_ATOMIC(pc, heap) \
  simulator.schedule->push_back( \
    id, \
    pc, \
    accu, \
    mem, \
    buffer.address, \
    buffer.value, \
    buffer.full, \
    heap)

#define PUSH_BACK(pc) PUSH_BACK_ATOMIC(pc, {})

void Thread::execute (Load & l)
{
  accu = load(l.arg, l.indirect);

  PUSH_BACK(pc++);
}

void Thread::execute (Store & s)
{
  store(s.arg, accu, s.indirect);

  PUSH_BACK(pc++);
}

void Thread::execute (Fence & f [[maybe_unused]])
{
  PUSH_BACK(pc++);
}

void Thread::execute (Add & a)
{
  accu += load(a.arg, a.indirect);

  PUSH_BACK(pc++);
}

void Thread::execute (Addi & a)
{
  accu += a.arg;

  PUSH_BACK(pc++);
}

void Thread::execute (Sub & s)
{
  accu -= load(s.arg, s.indirect);

  PUSH_BACK(pc++);
}

void Thread::execute (Subi & s)
{
  accu -= s.arg;

  PUSH_BACK(pc++);
}

void Thread::execute (Cmp & c)
{
  accu -= load(c.arg, c.indirect);

  PUSH_BACK(pc++);
}

void Thread::execute (Jmp & j)
{
  PUSH_BACK(pc);

  pc = j.arg;
}

void Thread::execute (Jz & j)
{
  PUSH_BACK(pc);

  if (accu)
    pc++;
  else
    pc = j.arg;
}

void Thread::execute (Jnz & j)
{
  PUSH_BACK(pc);

  if (accu)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (Js & j)
{
  PUSH_BACK(pc);

  if (static_cast<sword_t>(accu) < 0)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (Jns & j)
{
  PUSH_BACK(pc);

  if (static_cast<sword_t>(accu) >= 0)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (Jnzns & j)
{
  PUSH_BACK(pc);

  if (static_cast<sword_t>(accu) > 0)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (Mem & m)
{
  mem = accu = load(m.arg, m.indirect);

  PUSH_BACK(pc++);
}

void Thread::execute (Cas & c)
{
  optional<Schedule::Heap> heap;

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

void Thread::execute (Check & c)
{
  check = c.arg;
  state = State::waiting;

  PUSH_BACK(pc++);
}

// TODO
void Thread::execute (Halt & h [[maybe_unused]])
{
  PUSH_BACK(pc++);
}

void Thread::execute (Exit & e)
{
  accu = e.arg;
  state = State::exited;

  PUSH_BACK(pc);
}

std::ostream & operator << (std::ostream & os, Thread::State s)
{
    return os << static_cast<char>(s);
}
