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
Simulator::Simulator () : bound(0) {}

Simulator::Simulator (Program_list_ptr p, uint64_t b, uint64_t s) :
  programs(p),
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
  Schedule_ptr schedule = make_shared<Schedule>(programs);

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

      /* flush store buffer */
      if (thread->state == Thread::State::flushing)
        {
          thread->flush();

          /* append state update to schedule */
          schedule->push_back(
            thread->id,
            {thread->buffer.address, thread->buffer.value});
        }
      /* execute instruction */
      else
        {
          /* store current pc */
          word_t pc = thread->pc;

          thread->execute();

          /* pointer to an eventual CAS instruction */
          Cas_ptr cas = dynamic_pointer_cast<Cas>(thread->program[pc]);

          /* optional heap update */
          optional<Schedule::Heap> heap_update;

          /* mind indirect stores: save address in case it is overwritten */
          if (cas)
            {
              heap_update = {cas->indirect ? heap[cas->arg] : cas->arg, 0};

              /* get eventual heap update (ignore failed CAS) */
              if (thread->accu)
                heap_update->val = heap[heap_update->adr];
              else /* CAS failed */
                heap_update = {};
            }

          /* append state update to schedule */
          schedule->push_back(
            thread->id,
            pc,
            thread->accu,
            thread->mem,
            thread->buffer.address,
            thread->buffer.value,
            thread->buffer.full,
            heap_update);
        }

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
      {
        using Type = Instruction::Type;
        using Types = Instruction::Types;

        static const Type flush = Types::write | Types::barrier;

        if (random() % 2 || t->program[t->pc]->type() & flush)
          t->state = Thread::State::flushing;
      }

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

void Thread::execute (Load & l)
{
  pc++;
  accu = load(l.arg, l.indirect);
}

void Thread::execute (Store & s)
{
  pc++;
  store(s.arg, accu, s.indirect);
}

void Thread::execute (Fence & f [[maybe_unused]])
{
  pc++;
}

void Thread::execute (Add & a)
{
  pc++;
  accu += load(a.arg, a.indirect);
}

void Thread::execute (Addi & a)
{
  pc++;
  accu += a.arg;
}

void Thread::execute (Sub & s)
{
  pc++;
  accu -= load(s.arg, s.indirect);
}

void Thread::execute (Subi & s)
{
  pc++;
  accu -= s.arg;
}

void Thread::execute (Cmp & c)
{
  pc++;
  accu -= load(c.arg, c.indirect);
}

void Thread::execute (Jmp & j)
{
  pc = j.arg;
}

void Thread::execute (Jz & j)
{
  if (accu)
    pc++;
  else
    pc = j.arg;
}

void Thread::execute (Jnz & j)
{
  if (accu)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (Js & j)
{
  if (static_cast<sword_t>(accu) < 0)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (Jns & j)
{
  if (static_cast<sword_t>(accu) >= 0)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (Jnzns & j)
{
  if (static_cast<sword_t>(accu) > 0)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (Mem & m)
{
  pc++;
  mem = accu = load(m.arg, m.indirect);
}

void Thread::execute (Cas & c)
{
  pc++;

  if (mem == load(c.arg, c.indirect))
    {
      store(c.arg, accu, c.indirect, true);
      accu = 1;
    }
  else
    {
      accu = 0;
    }
}

void Thread::execute (Check & c)
{
  pc++;
  check = c.arg;
  state = State::waiting;
}

// TODO
void Thread::execute (Halt & h [[maybe_unused]])
{
  pc++;
}

void Thread::execute (Exit & e)
{
  accu = e.arg;
  state = State::exited;
}

std::ostream & operator << (std::ostream & os, Thread::State s)
{
    return os << static_cast<char>(s);
}
