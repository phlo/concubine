#ifndef TRACE_HH_
#define TRACE_HH_

#include <map>
#include <unordered_map>
#include <vector>

#include "program.hh"

//==============================================================================
// Trace class
//==============================================================================

struct Trace
{
  //----------------------------------------------------------------------------
  // member types
  //----------------------------------------------------------------------------

  using ptr = std::unique_ptr<Trace>;

  // update maps ---------------------------------------------------------------

  template <typename T>
  using Updates = std::map<bound_t, T>; // step -> state

  template <typename T>
  using Thread_Updates = std::vector<Updates<T>>;

  using Heap_Updates = std::unordered_map<word_t, Updates<word_t>>;

  using Flushes = std::unordered_set<bound_t>; // steps

  // heap cell -----------------------------------------------------------------

  struct Heap
    {
      word_t adr;
      word_t val;
    };

  // state at a specific step --------------------------------------------------

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

  // trace iterator ------------------------------------------------------------

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
      using Thread_Iterators = std::vector<Iterators<T>>;

      using Heap_Iterators = std::unordered_map<word_t, Iterators<word_t>>;

      const Trace * trace;

      Step step;

      Iterators<word_t> thread;
      Thread_Iterators<word_t> pc,
                               accu,
                               mem,
                               sb_adr,
                               sb_val;
      Thread_Iterators<bool> sb_full;
      Heap_Iterators heap;

      // helper for initializing thread update iterators
      //
      template <typename T>
      void init_iterators (Thread_Iterators<T> & iterators,
                           const Thread_Updates<T> & updates);

      // return current thread state and advance
      //
      template <typename T>
      const T & next_thread_state (Iterators<T> & state);

      // return current heap state update and advance
      //
      const std::optional<Heap> next_heap_state ();

      // assign state update
      //
      void assign ();

    public:
      using difference_type   = std::ptrdiff_t; // size_t ?
      using value_type        = Step;
      using pointer           = const Step *;
      using reference         = const Step &;
      using iterator_category = std::forward_iterator_tag;

      iterator (const Trace * trace, bound_t step = 1);

      iterator &  operator ++ ();
      iterator    operator ++ (int);

      bool        operator == (const iterator &) const;
      bool        operator != (const iterator &) const;

      reference   operator * () const;
      pointer     operator -> () const;
    };

  //----------------------------------------------------------------------------
  // members
  //----------------------------------------------------------------------------

  // programs used to generate the trace
  //
  // might be copied to another Trace during replay
  //
  Program::List::ptr programs;

  // bound used == size()
  //
  bound_t bound;

  // exit code
  //
  word_t exit;

  // store buffer flushes
  //
  Flushes flushes;

  // thread sequence
  //
  // step -> thread
  //
  Updates<word_t> thread_updates;

  // thread state updates
  //
  // thread -> step -> val
  //
  Thread_Updates<word_t> pc_updates;
  Thread_Updates<word_t> accu_updates;
  Thread_Updates<word_t> mem_updates;
  Thread_Updates<word_t> sb_adr_updates;
  Thread_Updates<word_t> sb_val_updates;
  Thread_Updates<bool> sb_full_updates;

  // heap state updates
  //
  // address -> list of (step, val) pairs
  //
  Heap_Updates heap_updates;

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  // initialize with given bound
  //
  explicit Trace (bound_t bound);

  // construct from simulator/solver
  //
  Trace (const Program::List::ptr & programs);

  // construct from file
  //
  Trace (std::istream & file, const std::string & path);

  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

  // initialize thread state update lists
  //
  void init_state_update_lists ();

  // append state update helper
  //
  template <typename T>
  void push_back (Updates<T> & updates, const bound_t step, const T val);

  // append state update after executing an instruction
  //
  void push_back (word_t thread,
                  word_t pc,
                  word_t accu,
                  word_t mem,
                  word_t sb_adr,
                  word_t sb_val,
                  word_t sb_full,
                  const std::optional<Heap> & heap);

  // append state update after flushing the store buffer
  //
  void push_back (word_t thread, const Heap & heap);

  // insert individual state updates
  //
  // NOTE: expects step to increase monotonically
  //
  void insert_thread (bound_t step, word_t thread);
  void insert_pc (bound_t step, word_t thread, word_t pc);
  void insert_accu (bound_t step, word_t thread, word_t accu);
  void insert_mem (bound_t step, word_t thread, word_t mem);
  void insert_sb_adr (bound_t step, word_t thread, word_t adr);
  void insert_sb_val (bound_t step, word_t thread, word_t val);
  void insert_sb_full (bound_t step, word_t thread, bool full);
  void insert_heap (bound_t step, const Heap & heap);
  void insert_flush (const bound_t step);

  // return trace size (bound)
  //
  size_t size () const;

  // return an iterator to the beginning
  //
  iterator begin () const;

  // return an iterator to the end
  //
  iterator end () const;

  // print trace
  //
  std::string print () const;
};

//==============================================================================
// non-member operators
//==============================================================================

// equality
//
bool operator == (const Trace &, const Trace &);
bool operator != (const Trace &, const Trace &);

#endif
