#include "simulator.hh"

#include <cassert>
#include <random>
#include <sstream>

using namespace std;

/* erases a given element from a <deque> container ****************************/
template<typename C, typename T>
inline void erase (C & container, T & val)
{
  container.erase(find(container.begin(), container.end(), val));
}

/*******************************************************************************
 * Simulator
 ******************************************************************************/
Simulator::Simulator () : bound(0) {}

Simulator::Simulator (ProgramListPtr p, uint64_t b, uint64_t s) :
  programs(p),
  bound(b),
  seed(s)
{
  active.reserve(programs->size());
  threads.reserve(programs->size());

  for (const ProgramPtr & program : * p)
    create_thread(*program);
}

/* Simulator::create_thread (Program &) ***************************************/
word Simulator::create_thread (Program & program)
{
  /* determine thread id */
  word id = threads.size();

  /* add thread to queue */
  threads.push_back({*this, id, program});

  /* add to checkpoint sets */
  for (word i : program.check_ids)
    threads_per_checkpoint[i].push_back(&threads.back());

  return id;
}

/* Simulator::check_and_resume (word) *****************************************/
void Simulator::check_and_resume (word id)
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

/* Simulator::run (Scheduler *) ***********************************************/
SchedulePtr Simulator::run (function<Thread *()> scheduler)
{
  SchedulePtr schedule = make_shared<Schedule>(programs);

  assert(active.empty());

  /* activate threads */
  for (Thread & t : threads)
    {
      t.state = Thread::State::running;
      active.push_back(&t);
    }

  bool done = active.empty();

  unsigned long step = 0; // TODO: remove (debug)
  while (!done && (!bound || schedule->bound < bound))
    {
      step++;

      Thread * thread = scheduler();

      assert(thread->state == Thread::State::running);

      /* store current pc */
      word pc = thread->pc;

      /* pointer to an eventual store instruction */
      Store_ptr store = dynamic_pointer_cast<Store>(thread->program[pc]);

      /* optional heap update */
      optional<Schedule::Heap_Cell> heap_cell;

      /* mind indirect stores: save address in case it is overwritten */
      if (store)
        heap_cell = {store->indirect ? heap[store->arg] : store->arg, 0};

      /* execute thread */
      thread->execute();

      /* get eventual heap update (ignore failed CAS) */
      if (store)
        {
          if (!(store->type() & Instruction::Types::atomic) || thread->accu)
            heap_cell->val = heap[heap_cell->idx];
          else /* CAS failed */
            heap_cell = {};
        }

      /* append state update to schedule */
      schedule->push_back(thread->id, pc, thread->accu, thread->mem, heap_cell);

      /* handle state transitions */
      switch (thread->state)
        {
        /* keep 'em running */
        case Thread::State::running: break;

        /* checkpoint reached - release if all other threads are waiting already */
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
          ostringstream msg;
          msg
            << "illegal thread state transition "
            << static_cast<char>(Thread::State::running)
            << " -> "
            << static_cast<char>(thread->state);
          throw runtime_error(msg.str());
        }
    }

  return schedule;
}

/* Simulator::simulate (unsigned long, unsigned long) *************************/
SchedulePtr Simulator::simulate (
                                 ProgramListPtr programs,
                                 unsigned long bound,
                                 unsigned long seed
                                )
{
  Simulator simulator {programs, bound, seed};

  /* Mersenne Twister pseudo-random number generator */
  mt19937_64 random(seed);

  /* random scheduler */
  return simulator.run([&simulator, &random] {
    return simulator.active[random() % simulator.active.size()];
  });
}

/* Simulator::replay (Schedule &, unsigned long) ******************************/
SchedulePtr Simulator::replay (Schedule & schedule, unsigned long bound)
{
  Simulator simulator {
    schedule.programs,
    bound && bound < schedule.bound ? bound : schedule.bound
  };

  /* replay scheduler */
  Schedule::iterator iterator = schedule.begin();

  return simulator.run([&simulator, &iterator] {
    return &simulator.threads[iterator++->thread];
  });
}

/*******************************************************************************
 * Thread
 ******************************************************************************/
Thread::Thread (Simulator & s, word i, Program & p) :
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
word Thread::load (word addr, bool indirect)
{
  return
    indirect
      ? simulator.heap[simulator.heap[addr]]
      : simulator.heap[addr];
}

/* Thread::store **************************************************************/
void Thread::store (word addr, word val, bool indirect)
{
  simulator.heap[indirect ? simulator.heap[addr] : addr] = val;
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

// TODO
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
  accu =
    static_cast<word>(
      static_cast<signed_word>(accu) -
      static_cast<signed_word>(load(c.arg, c.indirect))
  );
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
  if (static_cast<signed_word>(accu) < 0)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (Jns & j)
{
  if (static_cast<signed_word>(accu) >= 0)
    pc = j.arg;
  else
    pc++;
}

void Thread::execute (Jnzns & j)
{
  if (static_cast<signed_word>(accu) > 0)
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
      store(c.arg, accu, c.indirect);
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
