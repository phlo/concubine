#ifndef SCHEDULE_HH_
#define SCHEDULE_HH_

#include <map>
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
  using Update_Map      = std::map<unsigned long, word>; /* step -> state */

  using Thread_Updates  = std::vector<Update_Map>;
  using Heap_Updates    = std::unordered_map<word, Update_Map>;

  struct Heap_Cell
    {
      word idx;
      word val;
    };

  /* state at a specific step */
  struct Step
    {
      word thread {0};
      word pc {0};
      word accu {0};
      word mem {0};
      std::optional<Heap_Cell> heap;
    };

  /* schedule iterator */
  class iterator
    {
    private:
      struct Update_Iterators
        {
          Update_Map::const_iterator cur;
          Update_Map::const_iterator end;
        };
      using Thread_Iterators  = std::vector<Update_Iterators>;
      using Heap_Iterators    = std::unordered_map<word, Update_Iterators>;

      Schedule *        schedule;

      unsigned long     step;

      Step              update;

      Thread_Iterators  pc,
                        accu,
                        mem;

      Heap_Iterators    heap;

      /* return current thread state and advance */
      word              next_thread_state (Update_Iterators & state);

      /* return current heap state update and advance */
      std::optional<Heap_Cell> next_heap_state (void);

      /* assign state update */
      void              assign (void);

    public:
      using difference_type   = std::ptrdiff_t; // size_t ?
      using value_type        = Step;
      using pointer           = const Step *;
      using reference         = const Step &;
      using iterator_category = std::forward_iterator_tag;

      iterator (Schedule *, unsigned long = 1);

      iterator &  operator ++ (void);
      iterator    operator ++ (int);

      bool        operator == (const iterator &) const;
      bool        operator != (const iterator &) const;

      reference   operator * () const;
      pointer     operator -> () const;
    };

  /* initialize with given bound */
  explicit Schedule (unsigned long bound);

  /* construct from simulator/solver */
  Schedule (ProgramListPtr programs);

  /* construct from file */
  Schedule (std::istream & file, std::string & path);

  /* bound used == size() */
  // NOTE: remove?
  unsigned long     bound;

  /* programs used to generate the schedule */
  ProgramListPtr    programs;

  /* exit code */
  word              exit;

  /* thread sequence */
  std::vector<word> scheduled;

  /* thread states */
  Thread_Updates    pc_updates,
                    accu_updates,
                    mem_updates;

  /* heap state updates (idx -> [(step, val), ...]) */
  Heap_Updates      heap_updates;

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
                               const std::optional<Heap_Cell>
                              );

  void              insert (Update_Map & updates, const unsigned long step, const word val);
  void              insert_thread (const unsigned long step, const word thread);
  void              insert_pc (const unsigned long step, const word thread, const word pc);
  void              insert_accu (const unsigned long step, const word thread, const word accu);
  void              insert_mem (const unsigned long step, const word thread, const word mem);
  void              insert_heap (const unsigned long step, const Heap_Cell cell);

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
