#include "simulator.hh"

#include <cassert>
#include <random>
#include <sstream>

using namespace std;

/* erases a given element from a <deque> container ****************************/
template<typename T>
inline void erase (vector<T> & vec, T & val)
{
  vec.erase(find(vec.begin(), vec.end(), val));
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
Thread::Thread (Simulator & _simulator, word _id, Program & _program) :
  id(_id),
  pc(0),
  mem(0),
  accu(0),
  check(0),
  state(State::initial),
  simulator(_simulator),
  program(_program)
{}

/* Thread::load (word) ********************************************************/
word Thread::load (word addr, bool indirect)
{
  return
    indirect
      ? simulator.heap[simulator.heap[addr]]
      : simulator.heap[addr];
}

/* Thread::store (word, word) *************************************************/
void Thread::store (word addr, word val, bool indirect)
{
  simulator.heap[indirect ? simulator.heap[addr] : addr] = val;
}

/* Thread::execute (void) *****************************************************/
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
void Load::execute (Thread & thread)
{
  thread.pc++;
  thread.accu = thread.load(arg, indirect);
}

void Store::execute (Thread & thread)
{
  thread.pc++;
  thread.store(arg, thread.accu, indirect);
}

// TODO
void Fence::execute (Thread & thread)
{
  thread.pc++;
}

void Add::execute (Thread & thread)
{
  thread.pc++;
  thread.accu += thread.load(arg, indirect);
}

void Addi::execute (Thread & thread)
{
  thread.pc++;
  thread.accu += arg;
}

void Sub::execute (Thread & thread)
{
  thread.pc++;
  thread.accu -= thread.load(arg, indirect);
}

void Subi::execute (Thread & thread)
{
  thread.pc++;
  thread.accu -= arg;
}

void Cmp::execute (Thread & thread)
{
  thread.pc++;
  thread.accu = static_cast<word>(
    static_cast<signed_word>(thread.accu) -
    static_cast<signed_word>(thread.load(arg, indirect))
  );
}

void Jmp::execute (Thread & thread)
{
  thread.pc = arg;
}

void Jz::execute (Thread & thread)
{
  if (thread.accu == 0)
    thread.pc = arg;
  else
    thread.pc++;
}

void Jnz::execute (Thread & thread)
{
  if (thread.accu != 0)
    thread.pc = arg;
  else
    thread.pc++;
}

void Js::execute (Thread & thread)
{
  if (static_cast<signed_word>(thread.accu) < 0)
    thread.pc = arg;
  else
    thread.pc++;
}

void Jns::execute (Thread & thread)
{
  if (static_cast<signed_word>(thread.accu) >= 0)
    thread.pc = arg;
  else
    thread.pc++;
}

void Jnzns::execute (Thread & thread)
{
  if (static_cast<signed_word>(thread.accu) > 0)
    thread.pc = arg;
  else
    thread.pc++;
}

void Mem::execute (Thread & thread)
{
  Load::execute(thread);
  thread.mem = thread.accu;
}

void Cas::execute (Thread & thread)
{
  thread.pc++;

  word acutal = thread.load(arg, indirect);
  word expected = thread.mem;

  if (acutal == expected)
    {
      thread.store(arg, thread.accu, indirect);
      thread.accu = 1;
    }
  else
    {
      thread.accu = 0;
    }
}

void Check::execute (Thread & thread)
{
  thread.pc++;
  thread.check = arg;
  thread.state = Thread::State::waiting;
}

// TODO
void Halt::execute (Thread & thread)
{
  thread.pc++;
}

void Exit::execute (Thread & thread)
{
  thread.accu = arg;
  thread.state = Thread::State::exited;
}
