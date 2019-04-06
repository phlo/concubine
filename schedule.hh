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
struct Schedule
{
  typedef std::vector<word>                       thread_list_t;
  typedef std::pair<unsigned long, word>          update_t;
  typedef std::vector<update_t>                   update_list_t;
  typedef std::vector<update_list_t>              thread_updates_t;
  typedef std::unordered_map<word, update_list_t> heap_updates_t;
  typedef std::optional<std::pair<word, word>>    heap_cell_t;

  /* struct containing the state update at a specific step */
  struct step_t
    {
      word thread;
      word pc;
      word accu;
      word mem;
      std::optional<std::pair<word, word>> heap;
    };

  /* schedule iterator */
  class iterator
    {
    private:
      typedef update_list_t::const_iterator               update_it_t;
      typedef std::pair<update_it_t, update_it_t>         update_it_pair_t;
      typedef std::vector<update_it_pair_t>               update_it_list_t;
      typedef std::unordered_map<word, update_it_pair_t>  update_it_map_t;

      Schedule *        schedule;

      unsigned long     step;

      step_t            update;

      update_it_list_t  pc,
                        accu,
                        mem;

      update_it_map_t   heap;

      /* return current thread state and advance */
      word              next_thread_state (update_it_pair_t & state);

      /* return heap state update and advance */
      heap_cell_t       next_heap_state (void);

      /* assign state update */
      void              assign (void);

    public:
      typedef std::ptrdiff_t            difference_type; // size_t ?
      typedef step_t                    value_type;
      typedef const step_t *            pointer;
      typedef const step_t &            reference;
      typedef std::forward_iterator_tag iterator_category;

      iterator (Schedule *, unsigned long = 1);

      iterator &  operator ++ (void);
      iterator    operator ++ (int);

      bool        operator == (const iterator &) const;
      bool        operator != (const iterator &) const;

      reference   operator * () const;
      pointer     operator -> () const;
    };

  /* default constructor (for testing) */
  Schedule (void);

  /* construct from simulator/solver */
  Schedule (ProgramListPtr);

  /* construct from file */
  Schedule (std::istream &, std::string &);

  /* path to schedule file */
  std::string       path;

  /* bound used == size() */
  unsigned long     bound;

  /* programs used to generate the schedule */
  ProgramListPtr    programs;

  /* exit code */
  word              exit;

  /* thread sequence */
  thread_list_t     scheduled;

  /* thread states */
  thread_updates_t  pc_updates,
                    accu_updates,
                    mem_updates;

  /* heap state updates (idx -> [(step, val), ...]) */
  heap_updates_t    heap_updates;

  /* initialize thread state update lists */
  void              init_state_update_lists (void);

  /* return schedule size (bound) */
  size_t            size (void);

  /* append state update */
  void              push_back (
                               const unsigned long,
                               const word,
                               const word,
                               const word,
                               const heap_cell_t
                              );

  /* return thread id scheduled at the given step */
  word              at (unsigned long);

  /* return an iterator to the beginning */
  iterator          begin (void);

  /* return an iterator to the end */
  iterator          end (void);

  /* print schedule */
  std::string       print (void);
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
