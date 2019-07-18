#ifndef TRACE_HH_
#define TRACE_HH_

#include <map>
#include <unordered_map>
#include <vector>

#include "program.hh"

namespace ConcuBinE {

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

  // step -> state
  //
  template <class T>
  using update_map = std::map<size_t, T>;

  // thread -> step -> state
  //
  template <class T>
  using thread_map = std::vector<update_map<T>>;

  // address -> step -> state
  //
  using heap_val_map = std::unordered_map<word_t, update_map<word_t>>;

  // heap cell -----------------------------------------------------------------
  //
  struct cell_t
    {
      word_t adr;
      word_t val;
    };

  // state at a specific step --------------------------------------------------
  //
  struct Step
    {
      size_t step;
      word_t thread;
      word_t pc;
      word_t accu;
      word_t mem;
      word_t sb_adr;
      word_t sb_val;
      bool sb_full;
      bool flush;
      std::optional<cell_t> heap;

      Step () = default;
      Step (size_t step);

      operator size_t () const;

      Step & operator ++ ();
    };

  // trace iterator ------------------------------------------------------------
  //
  class iterator
    {
    private: //-----------------------------------------------------------------

      //------------------------------------------------------------------------
      // member types
      //------------------------------------------------------------------------

      template <typename T>
      struct update_map_iterator
        {
          typename update_map<T>::const_iterator cur;
          typename update_map<T>::const_iterator end;
        };

      template <typename T>
      using thread_state_iterators = std::vector<update_map_iterator<T>>;

      //------------------------------------------------------------------------
      // members
      //------------------------------------------------------------------------

      // trace being iterated
      //
      const Trace * trace;

      // current step's state
      //
      Step step;

      // schedule iterator
      //
      update_map_iterator<word_t> thread;

      // thread state update iterators
      //
      thread_state_iterators<word_t> pc;
      thread_state_iterators<word_t> accu;
      thread_state_iterators<word_t> mem;
      thread_state_iterators<word_t> sb_adr;
      thread_state_iterators<word_t> sb_val;
      thread_state_iterators<bool> sb_full;

      // heap update iterator
      //
      update_map_iterator<word_t> heap_adr;

      // heap value update iterator
      //
      std::unordered_map<word_t, update_map_iterator<word_t>> heap_val;

      //------------------------------------------------------------------------
      // private member functions
      //------------------------------------------------------------------------

      // helper for initializing thread update iterators
      //
      template <typename T>
      void init_iterators (thread_state_iterators<T> & iterators,
                           const thread_map<T> & updates);

      // return current thread state and advance
      //
      template <typename T>
      const T & next_state (update_map_iterator<T> & updates);

      // return current heap state update and advance
      //
      const std::optional<cell_t> next_heap_state ();

      // assign next state
      //
      void assign ();

    public: //------------------------------------------------------------------

      //------------------------------------------------------------------------
      // iterator traits
      //------------------------------------------------------------------------

      using difference_type   = std::ptrdiff_t; // size_t ?
      using value_type        = Step;
      using pointer           = const Step *;
      using reference         = const Step &;
      using iterator_category = std::forward_iterator_tag;

      //------------------------------------------------------------------------
      // constructors
      //------------------------------------------------------------------------

      iterator (const Trace * trace, size_t step = 0);

      //------------------------------------------------------------------------
      // member operators
      //------------------------------------------------------------------------

      iterator & operator ++ ();
      iterator   operator ++ (int);

      bool operator == (const iterator &) const;
      bool operator != (const iterator &) const;

      reference operator * () const;
      pointer   operator -> () const;
    };

  //----------------------------------------------------------------------------
  // members
  //----------------------------------------------------------------------------

  // programs used to generate the trace
  //
  // might be copied to another Trace during replay
  //
  Program::List::ptr programs;

  // trace length
  //
  size_t length;

  // exit code
  //
  word_t exit;

  // store buffer flushes
  //
  std::unordered_set<size_t> flushes;

  // thread sequence
  //
  // step -> thread
  //
  update_map<word_t> thread_updates;

  // thread state updates
  //
  // thread -> step -> val
  //
  thread_map<word_t> pc_updates;
  thread_map<word_t> accu_updates;
  thread_map<word_t> mem_updates;
  thread_map<word_t> sb_adr_updates;
  thread_map<word_t> sb_val_updates;
  thread_map<bool> sb_full_updates;

  // heap state updates
  //
  // step -> address
  //
  update_map<word_t> heap_adr_updates;

  // heap value updates
  //
  // address -> step -> value
  //
  heap_val_map heap_val_updates;

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  // initialize with given length
  //
  explicit Trace (size_t length);

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
  template <typename T>
  void init_register_states (thread_map<T> & updates);
  void init_register_states ();

  // append state update helper
  //
  template <typename T>
  void push_back (update_map<T> & updates, const size_t step, const T val);

  // append state update after executing an instruction
  //
  void push_back (word_t thread,
                  word_t pc,
                  word_t accu,
                  word_t mem,
                  word_t sb_adr,
                  word_t sb_val,
                  word_t sb_full,
                  std::optional<cell_t> & heap,
                  bool flush = false);

  // append individual state updates
  //
  void push_back_thread (size_t step, word_t thread);
  void push_back_pc (size_t step, word_t thread, word_t pc);
  void push_back_accu (size_t step, word_t thread, word_t accu);
  void push_back_mem (size_t step, word_t thread, word_t mem);
  void push_back_sb_adr (size_t step, word_t thread, word_t adr);
  void push_back_sb_val (size_t step, word_t thread, word_t val);
  void push_back_sb_full (size_t step, word_t thread, bool full);
  void push_back_heap (size_t step, const cell_t & heap);
  void push_back_flush (size_t step);

  // return most recently scheduled thread's id
  //
  word_t thread () const;

  // return most recent register states
  //
  word_t pc (word_t thread) const;
  word_t accu (word_t thread) const;
  word_t mem (word_t thread) const;
  word_t sb_adr (word_t thread) const;
  word_t sb_val (word_t thread) const;
  bool sb_full (word_t thread) const;

  // return most recent heap state
  //
  word_t heap (word_t address) const;

  // return trace size (length)
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

} // namespace ConcuBinE

#endif
