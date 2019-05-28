#ifndef SCHEDULE_HH_
#define SCHEDULE_HH_

#include <map>
#include <string>
#include <unordered_map>
#include <vector>

#include "program.hh"

struct Schedule
{
  using Flushes         = std::unordered_set<unsigned long>; // steps
  using Updates         = std::map<unsigned long, word>; // step -> state
  using Thread_Updates  = std::vector<Updates>;
  using Heap_Updates    = std::unordered_map<word, Updates>;

  struct Heap_Cell
    {
      word idx;
      word val;
    };

  /* state at a specific step */
  struct Step
    {
      bool flush {false};
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
      struct Iterators
        {
          Updates::const_iterator cur;
          Updates::const_iterator end;
        };
      using Thread_Iterators  = std::vector<Iterators>;
      using Heap_Iterators    = std::unordered_map<word, Iterators>;

      Schedule *        schedule;

      unsigned long     step;

      Step              update;

      Iterators         thread;
      Thread_Iterators  pc,
                        accu,
                        mem;
      Heap_Iterators    heap;

      /* return current thread state and advance */
      word              next_thread_state (Iterators & state);

      /* return current heap state update and advance */
      std::optional<Heap_Cell> next_heap_state ();

      /* assign state update */
      void              assign ();

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
  Schedule (Program_list_ptr programs);

  /* construct from file */
  Schedule (std::istream & file, std::string & path);

  /* bound used == size() */
  unsigned long     bound;

  /* programs used to generate the schedule */
  Program_list_ptr  programs;

  /* exit code */
  word              exit;

  /* store buffer flushes */
  Flushes           flushes;

  /* thread sequence */
  Updates           thread_updates;

  /* register states */
  Thread_Updates    pc_updates,
                    accu_updates,
                    mem_updates;

  /* heap state updates (idx -> [(step, val), ...]) */
  Heap_Updates      heap_updates;

  /* initialize thread state update lists */
  void              init_state_update_lists ();

  /* append state update helper */
  void              push_back (
                               Updates & updates,
                               const unsigned long step,
                               const word val
                              );

  /* append state update after executing an instruction */
  void              push_back (
                               const unsigned long thread,
                               const word pc,
                               const word accu,
                               const word mem,
                               const std::optional<Heap_Cell> & heap
                              );

  /* append state update after flushing the store buffer */
  void              push_back (
                               const unsigned long thread,
                               const Heap_Cell & heap
                              );

  /* insert individual state updates */
  /* NOTE: expects step to increase monotonically */
  void              insert_thread (
                                   const unsigned long step,
                                   const word thread
                                  );
  void              insert_pc (
                               const unsigned long step,
                               const word thread,
                               const word pc
                              );
  void              insert_accu (
                                 const unsigned long step,
                                 const word thread,
                                 const word accu
                                );
  void              insert_mem (
                                const unsigned long step,
                                const word thread,
                                const word mem
                               );
  void              insert_heap (
                                 const unsigned long step,
                                 const Heap_Cell & cell
                                );
  void              insert_flush (const unsigned long step);

  /* return schedule size (bound) */
  size_t            size ();

  /* return an iterator to the beginning */
  iterator          begin ();

  /* return an iterator to the end */
  iterator          end ();

  /* print schedule */
  std::string       print ();
};

/*******************************************************************************
 * Operators
 ******************************************************************************/
bool operator == (const Schedule &, const Schedule &);
bool operator != (const Schedule &, const Schedule &);

/*******************************************************************************
 * Schedule_ptr
 ******************************************************************************/
using Schedule_ptr = std::shared_ptr<Schedule>;

#endif
