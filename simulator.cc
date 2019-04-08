#include "simulator.hh"

#include <random>
#include <cassert>

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
  SchedulePtr schedule = make_shared<Schedule>(programs);

  assert(active.empty());

  activate_threads(threads);

  bool done = active.empty();

  while (!done && (!bound || schedule->bound < bound))
    {
      ThreadPtr thread = scheduler();

      assert(thread->state == Thread::State::RUNNING);

      /* store current pc */
      word pc = thread->pc;

      /* pointer to an eventual store instruction */
      StorePtr store = dynamic_pointer_cast<Store>(thread->program[pc]);

      /* optional heap update */
      optional<pair<word, word>> heap_cell;

      /* mind indirect stores: save address in case it is overwritten */
      if (store)
        heap_cell =
          make_pair(store->indirect ? heap[store->arg] : store->arg, 0);

      /* execute thread */
      thread->execute();

      /* get heap update (ignore failed CAS) */
      if (store)
        {
          if (store->get_opcode() == Instruction::OPCode::Store || thread->accu)
            heap_cell->second = heap[heap_cell->first];
          else /* CAS failed */
            heap_cell = {};
        }

      /* append state update to schedule */
      schedule->push_back(thread->id, pc, thread->accu, thread->mem, heap_cell);

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
              done = true;
              schedule->exit = static_cast<int>(thread->accu);
              break;
            }

        default:
          throw runtime_error(
            "illegal thread state transition " +
            to_string(Thread::State::RUNNING) + " -> " +
            to_string(thread->state));
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
SchedulePtr Simulator::replay (Schedule & schedule, unsigned long _bound)
{
  /* check programs */
  if (programs->size() != schedule.programs->size())
    throw runtime_error(
      "number of programs differ [" +
      to_string(programs->size()) +
      ", " +
      to_string(schedule.programs->size()) +
      "]");

  for (size_t i = 0; i < programs->size(); i++)
    if (*programs->at(i) != *schedule.programs->at(i))
      throw runtime_error(
        "program #" +
        to_string(i) +
        " differs: " +
        programs->at(i)->path +
        " != " +
        schedule.programs->at(i)->path);

  /* set bound */
  bound = _bound && _bound < schedule.bound ? _bound : schedule.bound;

  /* index variable for iterating the Schedule */
  unsigned long step = 0;

  /* replay scheduler */
  function<ThreadPtr(void)> scheduler = [this, &schedule, &step]
    {
      return threads[schedule.at(step++)];
    };

  return run(scheduler);
}
