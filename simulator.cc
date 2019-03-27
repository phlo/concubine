#include "simulator.hh"

#include <random>
#include <cassert>
#include <iostream>

using namespace std;

/* erases a given element from a <deque> container ****************************/
template<typename T>
inline void erase (deque<T> & lst, T & val)
{
  lst.erase(remove(lst.begin(), lst.end(), val));
}

/*******************************************************************************
 * Simulator
 ******************************************************************************/
Simulator::Simulator () : bound(0) {}

Simulator::Simulator (ProgramListPtr _programs) :
  programs(_programs)
{
  for (const ProgramPtr & program : *_programs)
    create_thread(*program);
}

/* Simulator::create_thread (Program &) ***************************************/
ThreadID Simulator::create_thread (Program & program)
{
  /* determine thread id */
  ThreadID id = threads.size();

  /* add thread to queue */
  threads.push_back(ThreadPtr(new Thread(*this, id, program)));

  /* add to sync id list */
  for (word i : program.sync_ids)
    threads_per_sync_id[i].push_back(threads.back());

  return id;
}

/* Simulator::activate_threads (ThreadList &) *********************************/
void Simulator::activate_threads (ThreadList & queue)
{
  for (ThreadPtr i : queue)
    {
      i->state = Thread::State::RUNNING;
      active.push_back(i);
    }
}

/* Simulator::check_and_resume_waiting (word) *********************************/
void Simulator::check_and_resume_waiting (word sync_id)
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

/* Simulator::run (Scheduler *) ***********************************************/
SchedulePtr Simulator::run (function<ThreadPtr(void)> scheduler)
{
  SchedulePtr schedule = SchedulePtr(new Schedule(programs, bound));

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
  for (unsigned long step = 1; !done && (step <= bound || !bound); step++)
    {
      ThreadPtr thread = scheduler();

      assert(thread->state == Thread::State::RUNNING);

      /* store current pc */
      word pc = thread->pc;

      /* execute thread */
      thread->execute();

      /* append thread state to schedule */
      schedule->push_back(step, thread->id, pc, thread->accu, thread->mem);

      /* append heap state to schedule (ignore failed CAS) */
      if (StorePtr s = dynamic_pointer_cast<Store>(thread->program[pc]))
        if (s->get_opcode() == Instruction::OPCode::Store || thread->accu)
          schedule->push_back(step, make_pair(s->arg, thread->accu));

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
        case Thread::State::EXITING:
            {
              schedule->exit = static_cast<int>(thread->accu);
              return schedule;
            }

        default:
          cout << "warning: illegal thread state transition " <<
            static_cast<int>(Thread::State::RUNNING) << " -> " <<
            static_cast<int>(thread->state) << endl;
          assert(0);
        }
    }

  return schedule;
}

/* Simulator::simulate (unsigned long, unsigned long) *************************/
SchedulePtr Simulator::simulate (unsigned long _bound, unsigned long _seed)
{
  /* set bound */
  bound = _bound;

  /* set seed */
  seed = _seed;

  /* Mersenne Twister pseudo-random number generator */
  mt19937_64 random(seed);

  /* random scheduler */
  function<ThreadPtr(void)> scheduler = [this, &random]
    {
      return this->active[random() % this->active.size()];
    };

  return run(scheduler);
}

/* Simulator::replay (Schedule &, unsigned long) ******************************/
SchedulePtr Simulator::replay (Schedule & _schedule, unsigned long _bound)
{
  /* check programs */
  if (programs->size() != _schedule.programs->size())
    throw runtime_error(
      "number of programs differ [" +
      to_string(programs->size()) +
      ", " +
      to_string(_schedule.programs->size()) +
      "]");

  for (size_t i = 0; i < programs->size(); i++)
    if (*programs->at(i) != *_schedule.programs->at(i))
      throw runtime_error(
        "program #" +
        to_string(i) +
        " differs: " +
        programs->at(i)->path +
        " != " +
        _schedule.programs->at(i)->path);

  /* set bound */
  bound = _bound && _bound < _schedule.bound ? _bound : _schedule.bound;

  /* index variable for iterating the Schedule */
  unsigned long step = 0;

  /* replay scheduler */
  function<ThreadPtr(void)> scheduler = [this, &_schedule, &step]
    {
      return threads[_schedule.threads.at(step++)];
    };

  return run(scheduler);
}
