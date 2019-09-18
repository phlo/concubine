#ifndef TRACE_HH_
#define TRACE_HH_

#include <map>
#include <unordered_map>
#include <vector>

#include "program.hh"

namespace ConcuBinE {

//==============================================================================
// forward declarations
//==============================================================================

class MMap;

//==============================================================================
// Trace class
//==============================================================================

struct Trace
{
  //----------------------------------------------------------------------------
  // member types
  //----------------------------------------------------------------------------

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

  // state at a specific step --------------------------------------------------
  //
  struct Step
    {
      size_t number;
      word_t thread;
      word_t pc;
      word_t accu;
      word_t mem;
      word_t sb_adr;
      word_t sb_val;
      bool sb_full;
      bool flush;
      std::optional<std::pair<word_t, word_t>> heap;

      Step () = default;
      Step (size_t k);

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
      T next_state (update_map_iterator<T> & updates);

      // return current heap state update and advance
      //
      std::optional<std::pair<word_t, word_t>> next_heap_state ();

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

  // programs used to produce the trace
  //
  // NOTE: copied during replay
  //
  std::shared_ptr<Program::List> programs;

  // memory map used to produce the trace
  //
  // NOTE: copied during replay
  //
  std::shared_ptr<MMap> mmap;

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
  Trace (const std::shared_ptr<Program::List> & programs,
         const std::shared_ptr<MMap> & mmap = {});

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

  // initialize heap state (and add to memory map)
  //
  void init_heap (word_t address, word_t value);

  // append state update helper
  //
  template <class T>
  bool push_back (update_map<T> & updates, size_t step, T value);

  // append state update after executing an instruction
  //
  void push_back (word_t thread,
                  word_t pc,
                  word_t accu,
                  word_t mem,
                  word_t sb_adr,
                  word_t sb_val,
                  word_t sb_full,
                  std::optional<std::pair<word_t, word_t>> & heap,
                  bool flush = false);

  // append individual state updates
  //
  void push_back_thread (size_t step, word_t thread);
  void push_back_pc (size_t step, word_t thread, word_t pc);
  void push_back_accu (size_t step, word_t thread, word_t accu);
  void push_back_mem (size_t step, word_t thread, word_t mem);
  void push_back_sb_adr (size_t step, word_t thread, word_t address);
  void push_back_sb_val (size_t step, word_t thread, word_t value);
  void push_back_sb_full (size_t step, word_t thread, bool full);
  void push_back_heap (size_t step, const word_t address, const word_t value);
  void push_back_flush (size_t step);

  // return most recently scheduled thread's id
  //
  word_t thread () const;

  // return thread scheduled at a given step k
  word_t thread (size_t k) const;

  // return true if a store buffer has been flushed in the given step
  //
  bool flush (word_t step) const;

  // return most recent register states
  //
  word_t pc (word_t thread) const;
  word_t accu (word_t thread) const;
  word_t mem (word_t thread) const;
  word_t sb_adr (word_t thread) const;
  word_t sb_val (word_t thread) const;
  bool sb_full (word_t thread) const;

  // return register state at a given step k
  //
  word_t pc (size_t k, word_t thread) const;
  word_t accu (size_t k, word_t thread) const;
  word_t mem (size_t k, word_t thread) const;
  word_t sb_adr (size_t k, word_t thread) const;
  word_t sb_val (size_t k, word_t thread) const;
  bool sb_full (size_t k, word_t thread) const;

  // return most recent heap state
  //
  std::optional<word_t> heap (word_t address) const;

  // return heap state for a given step k
  //
  std::optional<word_t> heap (size_t k, word_t address) const;

  // return trace size (length)
  //
  size_t size () const;

  // true if trace is empty
  //
  bool empty () const;

  // return an iterator to the beginning
  //
  iterator begin () const;

  // return an iterator to the end
  //
  iterator end () const;

  // print individual step
  //
  std::string print (const Step & step) const;

  // print whole trace
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

bool operator == (const Trace::Step &, const Trace::Step &);
bool operator != (const Trace::Step &, const Trace::Step &);

} // namespace ConcuBinE

#endif
