#ifndef SCHEDULE_HH_
#define SCHEDULE_HH_

#include <map>
#include <string>
#include <unordered_map>
#include <vector>

#include "program.hh"

struct Schedule
{
  template <typename T>
  using Updates = std::map<bound_t, T>; // step -> state

  template <typename T>
  using Thread_Updates = std::vector<Updates<T>>;

  using Heap_Updates = std::unordered_map<word_t, Updates<word_t>>;

  using Flushes = std::unordered_set<bound_t>; // steps

  struct Heap
    {
      word_t adr;
      word_t val;
    };

  /* state at a specific step */
  struct Step
    {
      bound_t step;
      word_t thread;
      word_t pc;
      word_t accu;
      word_t mem;
      word_t sb_adr;
      word_t sb_val;
      bool sb_full;
      bool flush;
      std::optional<Heap> heap;

      Step () = default;
      Step (bound_t step);

      operator bound_t () const;

      Step & operator ++ ();
    };

  /* schedule iterator */
  class iterator
    {
    private:
      template <typename T>
      struct Iterators
        {
          typename Updates<T>::const_iterator cur;
          typename Updates<T>::const_iterator end;
        };

      template <typename T>
      using Thread_Iterators  = std::vector<Iterators<T>>;

      using Heap_Iterators    = std::unordered_map<word_t, Iterators<word_t>>;

      const Schedule *          schedule;

      Step                      step;

      Iterators<word_t>         thread;
      Thread_Iterators<word_t>  pc,
                                accu,
                                mem,
                                sb_adr,
                                sb_val;
      Thread_Iterators<bool>    sb_full;
      Heap_Iterators            heap;

      /* helper for initializing thread update iterators */
      template <typename T>
      void init_iterators (
                           Thread_Iterators<T> & iterators,
                           const Thread_Updates<T> & updates
                          );

      /* return current thread state and advance */
      template <typename T>
      const T & next_thread_state (Iterators<T> & state);

      /* return current heap state update and advance */
      const std::optional<Heap> next_heap_state ();

      /* assign state update */
      void assign ();

    public:
      using difference_type   = std::ptrdiff_t; // size_t ?
      using value_type        = Step;
      using pointer           = const Step *;
      using reference         = const Step &;
      using iterator_category = std::forward_iterator_tag;

      iterator (const Schedule * schedule, bound_t step = 1);

      iterator &  operator ++ ();
      iterator    operator ++ (int);

      bool        operator == (const iterator &) const;
      bool        operator != (const iterator &) const;

      reference   operator * () const;
      pointer     operator -> () const;
    };

  /* initialize with given bound */
  explicit Schedule (bound_t bound);

  /* construct from simulator/solver */
  Schedule (Program_list_ptr programs);

  /* construct from file */
  Schedule (std::istream & file, std::string & path);

  /* bound used == size() */
  bound_t                 bound;

  /* programs used to generate the schedule */
  Program_list_ptr        programs;

  /* exit code */
  word_t                  exit;

  /* store buffer flushes */
  Flushes                 flushes;

  /* thread sequence */
  Updates<word_t>         thread_updates;

  /* thread state updates */
  Thread_Updates<word_t>  pc_updates,
                          accu_updates,
                          mem_updates,
                          sb_adr_updates,
                          sb_val_updates;
  Thread_Updates<bool>    sb_full_updates;

  /* heap state updates (idx -> [(step, val), ...]) */
  Heap_Updates            heap_updates;

  /* initialize thread state update lists */
  void                    init_state_update_lists ();

  /* append state update helper */
  template <typename T>
  void push_back (Updates<T> & updates, const bound_t step, const T val);

  /* append state update after executing an instruction */
  void push_back (
                  const word_t thread,
                  const word_t pc,
                  const word_t accu,
                  const word_t mem,
                  const word_t sb_adr,
                  const word_t sb_val,
                  const word_t sb_full,
                  const std::optional<Heap> & heap
                 );

  /* append state update after flushing the store buffer */
  void push_back (const word_t thread, const Heap & heap);

  /* insert individual state updates */
  /* NOTE: expects step to increase monotonically */
  void insert_thread (const bound_t step, const word_t thread);
  void insert_pc (
                  const bound_t step,
                  const word_t thread,
                  const word_t pc
                 );
  void insert_accu (
                    const bound_t step,
                    const word_t thread,
                    const word_t accu
                   );
  void insert_mem (
                   const bound_t step,
                   const word_t thread,
                   const word_t mem
                  );
  void insert_sb_adr (
                      const bound_t step,
                      const word_t thread,
                      const word_t adr
                     );
  void insert_sb_val (
                      const bound_t step,
                      const word_t thread,
                      const word_t val
                     );
  void insert_sb_full (
                       const bound_t step,
                       const word_t thread,
                       const bool full
                      );
  void insert_heap (
                    const bound_t step,
                    const Heap & heap
                   );
  void insert_flush (const bound_t step);

  /* return schedule size (bound) */
  size_t size () const;

  /* return an iterator to the beginning */
  iterator begin () const;

  /* return an iterator to the end */
  iterator end () const;

  /* print schedule */
  std::string print () const;
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
