#include "machine.hh"

#include <iostream>
#include <algorithm>

/*******************************************************************************
 * Schedulers
 ******************************************************************************/
struct Scheduler
{
  Machine & machine;

  virtual ThreadPtr next (void) = 0;

  Scheduler (Machine & m) : machine(m) {};
};

class RandomScheduler : public Scheduler
{
  mt19937_64                          random;
  uniform_int_distribution<ThreadID>  distribution;

public:
  RandomScheduler (Machine & m) :
    Scheduler(m),
    random(m.seed),
    distribution(0, machine.threads.size() - 1)
  {};

  ThreadPtr next (void)
    {
      return machine.active[distribution(random) % machine.active.size()];
    };
};

class PredefinedScheduler : public Scheduler
{
  Schedule &    schedule;
  unsigned long step;

public:
  PredefinedScheduler (Machine & m, Schedule & s) :
    Scheduler(m),
    schedule(s),
    step(0)
  {};

  ThreadPtr next (void) { return machine.threads[schedule[step++]]; };
};


/*******************************************************************************
 * Machine
 ******************************************************************************/

/* constructor ****************************************************************/
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
  for (auto i : program.getSyncIDs())
    threadsPerSyncID[i].push_back(threads[id]);

  return id;
}

/* Machine::activateThreads (deque<ThreadPtr> &) ******************************/
void Machine::activateThreads (deque<ThreadPtr> & queue)
{
  for (ThreadPtr i : queue)
    {
      i->state = Thread::State::RUNNING;
      active.push_back(i);
    }
}

/* Machine::run (Scheduler *) *************************************************/
int Machine::run (Scheduler * scheduler)
{
  /* print schedule header */
  for (auto t : threads)
    cout << t->id << " = " << t->program.getPath() << endl;
  cout << "seed = " << seed << endl;
  cout << "# tid";
  if (verbose)
    cout << "\tpc\tcmd\targ\taccu";
  cout << endl;

  assert(active.empty());
  activateThreads(threads);

  bool done = active.empty();
  unsigned long steps = 0;
  while (!done && (!bound || steps++ < bound))
    {
      ThreadPtr thread = scheduler->next();

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
              active.erase(find(active.begin(), active.end(), thread));

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
              active.erase(find(active.begin(), active.end(), thread));

              /* check if we were the last thread standing */
              done = true;
              for (ThreadID i = 0; i < threads.size(); i++)
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
              return static_cast<int>(thread->accu);
            }

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
  RandomScheduler scheduler(*this);

  return run(&scheduler);
}

/* Machine::replay (Schedule &) ***********************************************/
int Machine::replay (Schedule & schedule)
{
  for (ProgramPtr p : schedule.getPrograms())
    createThread(*p);

  PredefinedScheduler scheduler(*this, schedule);

  return run(&scheduler);
}
