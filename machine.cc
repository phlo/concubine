#include "machine.hh"

#include <random>
#include <cassert>
#include <iostream>
#include <algorithm>

#include "schedule.hh"

using namespace std;

/* erases a given element from a <deque> container ****************************/
template<typename T>
inline void erase (deque<T> & lst, T & val)
{
  lst.erase(remove(lst.begin(), lst.end(), val));
}

/*******************************************************************************
 * Machine
 ******************************************************************************/
Machine::Machine (unsigned long s, unsigned long b) :
  seed(s),
  bound(b),
  active(),
  threads(),
  memory({{0}}), // initialize with zeros ffs ..
  threads_per_sync_id(),
  waiting_per_sync_id()
{}

/* Machine::create_thread (Program &) *****************************************/
ThreadID Machine::create_thread (Program & program)
{
  /* determine thread id */
  ThreadID id = threads.size();

  /* add thread to queue */
  threads.push_back(ThreadPtr(new Thread(*this, id, program)));

  /* add to sync id list */
  for (word i : program.sync_ids)
    threads_per_sync_id[i].push_back(threads[id]);

  return id;
}

/* Machine::activate_threads (ThreadList &) ***********************************/
void Machine::activate_threads (ThreadList & queue)
{
  for (ThreadPtr i : queue)
    {
      i->state = Thread::State::RUNNING;
      active.push_back(i);
    }
}

/* Machine::check_and_resume_waiting (word) ***********************************/
void Machine::check_and_resume_waiting (word sync_id)
{
  /* all other threads already synced to this barrier? */
  if (waiting_per_sync_id[sync_id] == threads_per_sync_id[sync_id].size())
    {
      /* reset number of threads waiting for this barrier */
      waiting_per_sync_id[sync_id] = 0;

      /* reactivate threads */
      activate_threads(threads_per_sync_id[sync_id]);
    }
}

/* Machine::run (Scheduler *) *************************************************/
int Machine::run (function<ThreadPtr(void)> scheduler)
{
  /* print schedule header */
  for (auto t : threads)
    cout << t->id << " = " << t->program.path << endl;
  cout << "seed = " << seed << endl;
  cout << "# tid";
  if (verbose)
    cout << "\tpc\tcmd\targ\taccu";
  cout << endl;

  assert(active.empty());
  activate_threads(threads);

  bool done = active.empty();
  unsigned long steps = 0;
  while (!done && (steps++ < bound || !bound))
    {
      ThreadPtr thread = scheduler();

      assert(thread->state == Thread::State::RUNNING);

      thread->execute();

      /* handle state transitions */
      switch (thread->state)
        {
        /* keep 'em running */
        case Thread::State::RUNNING: break;

        /* sync issued - check if all other threads are waiting already */
        case Thread::State::WAITING:
            {
              /* remove from active threads */
              erase(active, thread);

              /* increment number of waiting threads */
              waiting_per_sync_id[thread->sync]++;

              /* all other threads already synced to this barrier? */
              check_and_resume_waiting(thread->sync);

              break;
            }

        /* halted - quit if all the others also stopped */
        case Thread::State::STOPPED:
            {
              /* remove from active threads */
              erase(active, thread);

              /* take care if last instruction was a SYNC (bypasses WAITING) */
              if (dynamic_pointer_cast<Sync>(thread->program.back()))
                  {
                    /* remove from list of threads waiting for this barrier */
                    erase(threads_per_sync_id[thread->sync], thread);

                    /* activate all waiting threads if this was the last one */
                    check_and_resume_waiting(thread->sync);
                  }

              /* check if we were the last thread standing */
              done = accumulate(threads.begin(), threads.end(), true,
                [](const bool & d, const ThreadPtr & t)
                {
                  return d && t->state == Thread::State::STOPPED;
                });

              break;
            }

        /* exiting - return exit code */
        case Thread::State::EXITING: return static_cast<int>(thread->accu);

        default:
          cout << "warning: illegal thread state transition " <<
            static_cast<int>(Thread::State::RUNNING) << " -> " <<
            static_cast<int>(thread->state) << endl;
          assert(0);
        }
    }

  return 0;
}

/* Machine::simulate (void) ***************************************************/
int Machine::simulate ()
{
  /* Mersenne Twister pseudo-random number generator */
  mt19937_64 random(seed);

  /* random scheduler */
  function<ThreadPtr(void)> scheduler = [this, &random]
    {
      return this->active[random() % this->active.size()];
    };

  return run(scheduler);
}

/* Machine::replay (Schedule &) ***********************************************/
int Machine::replay (Schedule & schedule)
{
  /* set bound */
  bound = schedule.size();

  /* create threads */
  for (ProgramPtr p : schedule.programs)
    create_thread(*p);

  /* index variable for iterating the Schedule */
  unsigned long step = 0;

  /* replay scheduler */
  function<ThreadPtr(void)> scheduler = [this, &schedule, &step]
    {
      return this->threads[schedule[step++]];
    };

  return run(scheduler);
}
