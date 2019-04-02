#ifndef SCHEDULE_HH_
#define SCHEDULE_HH_

#include <string>
#include <unordered_map>
#include <vector>

#include "program.hh"
#include "thread.hh"

/*******************************************************************************
 * Schedule
 ******************************************************************************/
struct Schedule : public std::vector<word>
{
  /* default constructor (for testing) */
  Schedule (void);

  /* construct from simulator/solver */
  Schedule (ProgramListPtr);

  /* construct from file */
  Schedule (std::istream &, std::string &);

  /* path to schedule file */
  std::string           path;

  /* bound used == size() */
  unsigned long         bound;

  /* programs used to generate the schedule */
  ProgramListPtr        programs;

  /* exit code */
  word                  exit;

  /* thread states */
  std::vector<
    std::vector<
      std::pair<
        unsigned long,
        word>>>         pc_updates,
                        accu_updates,
                        mem_updates;

  /* heap state updates (idx -> [(step, val), ...]) */
  std::unordered_map<
    word,
    std::vector<
      std::pair<
        unsigned long,
        word>>>         heap_updates;

  /* initialize thread state update lists */
  void                  init_state_update_lists (void);

  /* append thread state update */
  void                  push_back (
                                   const unsigned long step,
                                   const unsigned long tid,
                                   const word pc,
                                   const word accu,
                                   const word mem
                                  );

  /* append heap state update */
  void                  push_back (
                                   const unsigned long step,
                                   const word idx,
                                   const word val
                                  );

  /* add thread state */
  // void                  add (
                             // const unsigned long tid,
                             // const word pc,
                             // const word accu,
                             // const word mem
                            // );

  /* add heap state */
  // void                  add (const std::unordered_map<word, word> & heap);

  /* print schedule */
  std::string           print (void);

  struct step_t
    {
      word thread;
      word pc;
      word accu;
      word mem;
      std::optional<std::pair<word, word>> heap;
    };

  class iterator
    {
    private:

      Schedule *    schedule;

      unsigned long step;

      step_t        update;

      typedef
        std::vector<std::pair<unsigned long, word>>::const_iterator
        update_it_t;

      typedef
        std::pair<update_it_t, update_it_t>
        update_pair_t;

      typedef
        std::vector<update_pair_t>
        thread_state_t;

      typedef
        std::unordered_map<word, update_pair_t>
        heap_state_t;

      thread_state_t  cur_pc,
                      cur_accu,
                      cur_mem;

      heap_state_t    cur_heap;

      /* advance and return current thread state */
      word advance (update_pair_t & state)
        {
          update_it_t next = state.first + 1;

          while (next != state.second && next->first <= step)
            state.first = next++;

          return state.first->second;
        }

      /* advance and return current heap state */
      std::optional<std::pair<word, word>> advance (word tid, word pc)
        {
          std::cout
            << "thread = " << tid << eol
            << "pc     = " << pc << eol
            << "size   = " << schedule->programs->at(tid)->size() << eol;

          if (
              StorePtr store =
                std::dynamic_pointer_cast<Store>(
                  schedule->programs->at(tid)->at(pc))
             )
            {
              word idx =
                store->indirect
                  ? schedule->heap_updates[store->arg].back().second
                  : store->arg;

              update_pair_t & heap = cur_heap[idx];

              if (heap.first->first == step)
                return
                  std::make_optional(
                    std::make_pair(idx, heap.first++->second));
            }

          return {};
        }

      /* advance step */
      void advance (void)
        {
          if (++step > schedule->bound)
            return;

          word tid = schedule->at(step - 1);

          update.thread = tid;
          update.pc = advance(cur_pc[tid]);
          update.accu = advance(cur_accu[tid]);
          update.mem = advance(cur_mem[tid]);
          update.heap = advance(tid, update.pc);
        }

    public:
      typedef std::ptrdiff_t            difference_type; // size_t ?
      typedef step_t                    value_type;
      typedef const step_t *            pointer;
      typedef const step_t &            reference;
      typedef std::forward_iterator_tag iterator_category;

      iterator (Schedule * _schedule, unsigned long _step = 0) :
        schedule(_schedule),
        step(_step)
      {
        if (step > schedule->bound)
          return;

        size_t num_threads = schedule->programs->size();

        /* initialize state update iterators */
        cur_pc.reserve(num_threads);
        for (const auto & updates : schedule->pc_updates)
          cur_pc.push_back(make_pair(updates.begin(), updates.end()));

        cur_accu.reserve(num_threads);
        for (const auto & updates : schedule->accu_updates)
          cur_accu.push_back(make_pair(updates.begin(), updates.end()));

        cur_mem.reserve(num_threads);
        for (const auto & updates : schedule->mem_updates)
          cur_mem.push_back(make_pair(updates.begin(), updates.end()));

        cur_heap.reserve(schedule->heap_updates.size());
        for (const auto & [idx, updates] : schedule->heap_updates)
          cur_heap[idx] = make_pair(updates.begin(), updates.cend());

        /* advance to first step */
        advance();
      };

      iterator &  operator ++ ()
        {
          advance();
          return *this;
        }
      iterator    operator ++ (int)
        {
          iterator retval = *this;
          ++(*this);
          return retval;
        }

      bool        operator == (const iterator & other)
        {
          return schedule == other.schedule && step == other.step;
        }
      bool        operator != (const iterator & other)
        {
          return !(*this == other);
        }

      reference   operator * () const
        {
          return update;
        }
      pointer     operator -> ()
        {
          return &update;
        }
    };

  iterator begin (void);
  iterator end (void);
};

/*******************************************************************************
 * Operators
 ******************************************************************************/
bool operator == (const Schedule &, const Schedule &);
bool operator != (const Schedule &, const Schedule &);

/*******************************************************************************
 * SchedulePtr
 ******************************************************************************/
typedef std::shared_ptr<Schedule> SchedulePtr;

#endif
