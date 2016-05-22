#include "machine.hh"

#include <iostream>

#include "program.hh"

/* constructor ****************************************************************/
Machine::Machine (unsigned long s, unsigned long b = 0) :
  memory({}), // initialize with zeros ffs ..
  threads(),
  active(),
  threadsPerSyncID(),
  waitingPerSyncID(),
  bound(b),
  seed(s),
  randomGenerator(s)
{}

/* Machine::createThread (Program &) ******************************************/
unsigned int Machine::createThread (Program & program)
{
  /* determine thread id */
  unsigned int id = threads.size();

  /* add thread to queue */
  threads.push_back(ThreadPtr(new Thread(*this, id, program)));

  /* add to sync id list */
  for (auto i : program.getSyncIDs())
    threadsPerSyncID[i].push_back(threads[id]);

  return id;
}

/* Machine::activateThreads (deque<ThreadPtr> &) ******************************/
void Machine::activateThreads (deque<ThreadPtr> & queue)
{
  for (auto i : queue)
    {
      i->state = Thread::State::RUNNING;
      active.push_back(i);
    }
}

/* Machine::run (void) ********************************************************/
int Machine::run ()
{
  unsigned int numThreads = threads.size();

  uniform_int_distribution<unsigned long> scheduler(0, numThreads - 1);

  for (auto t : threads)
    cout << "# T" << t->id << " = " << t->program.getPath() << endl;
  cout << "# STARTED [seed = " << seed << "]" << endl;
  cout << "# tid\tpc\tcmd\targ" << endl;

  activateThreads(threads);

  bool done = active.empty();
  unsigned long steps = 0;
  while (!done && (!bound || steps++ < bound))
    {
      unsigned int id = scheduler(randomGenerator) % active.size();

      ThreadPtr thread = active[id];

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
              active.erase(active.begin() + id);

              /* current sync barrier id */
              word s = thread->sync;

              /* add to waiting map */
              waitingPerSyncID[s].push_back(thread);

              /* all other threads already synced to this barrier? */
              if (waitingPerSyncID[s].size() == threadsPerSyncID[s].size())
                {
                  /* reactivate threads */
                  activateThreads(threadsPerSyncID[s]);
                }
              break;
            }

        /* halted - check if all the others also finished without an exit */
        case Thread::State::STOPPED:
            {
              /* remove from active threads */
              active.erase(active.begin() + id);

              /* check if we were the last thread standing */
              done = true;
              for (unsigned int i = 0; i < numThreads; i++)
                {
                  if (threads[i]->state != Thread::State::STOPPED)
                    {
                      done = false;
                      break;
                    }
                }
              break;
            }

        /* exiting - return exit code */
        case Thread::State::EXITING:
            {
              cout << "# EXIT " << thread->accu << endl;
              return static_cast<int>(thread->accu);
            }

        default:
          cout << "warning: illegal thread state transition " <<
            Thread::State::RUNNING << " -> " << active[id]->state << endl;
          assert(0);
        }
    }

  cout << "# HALT" << endl;

  return 0;
}
