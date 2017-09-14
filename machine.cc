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
  threadsPerSyncID(),
  waitingPerSyncID()
{}

/* Machine::createThread (Program &) ******************************************/
ThreadID Machine::createThread (Program & program)
{
  /* determine thread id */
  ThreadID id = threads.size();

  /* add thread to queue */
  threads.push_back(ThreadPtr(new Thread(*this, id, program)));

  /* add to sync id list */
  for (word i : program.syncIDs)
    threadsPerSyncID[i].push_back(threads[id]);

  return id;
}

/* Machine::activateThreads (ThreadList &) ************************************/
void Machine::activateThreads (ThreadList & queue)
{
  for (ThreadPtr i : queue)
    {
      i->state = Thread::State::RUNNING;
      active.push_back(i);
    }
}

/* Machine::checkAndResumeWaiting (word) **************************************/
void Machine::checkAndResumeWaiting (word syncID)
{
  /* all other threads already synced to this barrier? */
  if (waitingPerSyncID[syncID] == threadsPerSyncID[syncID].size())
    {
      /* reset number of threads waiting for this barrier */
      waitingPerSyncID[syncID] = 0;

      /* reactivate threads */
      activateThreads(threadsPerSyncID[syncID]);
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
  activateThreads(threads);

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
              waitingPerSyncID[thread->sync]++;

              /* all other threads already synced to this barrier? */
              checkAndResumeWaiting(thread->sync);

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
                    erase(threadsPerSyncID[thread->sync], thread);

                    /* activate all waiting threads if this was the last one */
                    checkAndResumeWaiting(thread->sync);
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
  /* create threads */
  for (ProgramPtr p : schedule.programs)
    createThread(*p);

  /* index variable for iterating the Schedule */
  unsigned long step = 0;

  /* replay scheduler */
  function<ThreadPtr(void)> scheduler = [this, &schedule, &step]
    {
      return this->threads[schedule[step++]];
    };

  return run(scheduler);
}
