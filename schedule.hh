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
      word            get_thread_state (update_pair_t & state);

      /* advance and return heap state update */
      std::optional<
        std::pair<
          word,
          word>>      get_heap_state (void);

      /* advance step */
      void            advance (void);

    public:
      typedef std::ptrdiff_t            difference_type; // size_t ?
      typedef step_t                    value_type;
      typedef const step_t *            pointer;
      typedef const step_t &            reference;
      typedef std::forward_iterator_tag iterator_category;

      iterator (Schedule * _schedule, unsigned long _step = 0);

      iterator &  operator ++ (void);
      iterator    operator ++ (int);

      bool        operator == (const iterator &);
      bool        operator != (const iterator &);

      reference   operator * () const;
      pointer     operator -> () const;
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
