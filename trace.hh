#ifndef TRACE_HH_
#define TRACE_HH_

#include <map>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "program.hh"

namespace ConcuBinE {

//==============================================================================
// forward declarations
//==============================================================================

class MMap;

//==============================================================================
// Trace
//==============================================================================

class Trace
{
public: //======================================================================

  //----------------------------------------------------------------------------
  // public member types
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

      friend bool operator == (const Step &, const Step &);
      friend bool operator != (const Step &, const Step &);
    };

  // trace iterator ------------------------------------------------------------
  //
  class iterator
    {
    public: //==================================================================

      //------------------------------------------------------------------------
      // public member types
      //------------------------------------------------------------------------

      // iterator traits
      //
      using difference_type   = std::ptrdiff_t; // size_t ?
      using value_type        = Step;
      using pointer           = const Step *;
      using reference         = const Step &;
      using iterator_category = std::forward_iterator_tag;

      //------------------------------------------------------------------------
      // public constructors
      //------------------------------------------------------------------------

      iterator (const Trace * trace, size_t step = 0);

      //------------------------------------------------------------------------
      // public member operators
      //------------------------------------------------------------------------

      iterator & operator ++ ();
      iterator   operator ++ (int);

      bool operator == (const iterator &) const;
      bool operator != (const iterator &) const;

      reference operator * () const;
      pointer   operator -> () const;

    private: //=================================================================

      //------------------------------------------------------------------------
      // private member types
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
      // private member functions
      //------------------------------------------------------------------------

      // helper for initializing thread update iterators
      //
      template <typename T>
      void init_iterators (thread_state_iterators<T> & iterators,
                           const thread_map<T> & updates);

      // get current thread state and advance
      //
      template <typename T>
      T next_state (update_map_iterator<T> & updates);

      // get current heap state update and advance
      //
      std::optional<std::pair<word_t, word_t>> next_heap_state ();

      // assign next state
      //
      void assign ();

      //------------------------------------------------------------------------
      // private data members
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
    };

  //----------------------------------------------------------------------------
  // public constructors
  //----------------------------------------------------------------------------

  // construct empty trace
  //
  Trace (const std::shared_ptr<Program::List> & programs,
         const std::shared_ptr<MMap> & mmap = {});

  // parse input stream
  //
  Trace (std::istream & file, const std::string & path);

  //----------------------------------------------------------------------------
  // public member functions
  //----------------------------------------------------------------------------

  // initialize heap state (and add to memory map)
  //
  void init_heap (word_t address, word_t value);

  // append state update
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

  // get most recently scheduled thread's id
  //
  word_t thread () const;

  // get thread scheduled at a given step
  //
  word_t thread (size_t step) const;

  // check if a store buffer has been flushed in the given step
  //
  bool flush (size_t step) const;

  // get most recent register state
  //
  word_t pc (word_t thread) const;
  word_t accu (word_t thread) const;
  word_t mem (word_t thread) const;
  word_t sb_adr (word_t thread) const;
  word_t sb_val (word_t thread) const;
  bool sb_full (word_t thread) const;

  // get register state at a given step
  //
  word_t pc (size_t k, word_t thread) const;
  word_t accu (size_t k, word_t thread) const;
  word_t mem (size_t k, word_t thread) const;
  word_t sb_adr (size_t k, word_t thread) const;
  word_t sb_val (size_t k, word_t thread) const;
  bool sb_full (size_t k, word_t thread) const;

  // get most recent heap state
  //
  std::optional<word_t> heap (word_t address) const;

  // get heap state at a given step and address
  //
  std::optional<word_t> heap (size_t k, word_t address) const;

  // get iterator to the beginning
  //
  iterator begin () const;

  // get iterator to the end
  //
  iterator end () const;

  // check trace is empty
  //
  bool empty () const;

  // get trace size (length)
  //
  size_t size () const;

  // print individual step
  //
  std::string print (const Step & step) const;

  // print whole trace
  //
  std::string print () const;

  //----------------------------------------------------------------------------
  // public data members
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

  // exit code
  //
  word_t exit;

private: //=====================================================================

  //----------------------------------------------------------------------------
  // private member functions
  //----------------------------------------------------------------------------

  // initialize thread state update lists
  //
  template <typename T>
  void init_register_states (thread_map<T> & updates);
  void init_register_states ();

  // append state update helper
  //
  template <class T>
  bool push_back (update_map<T> & updates, size_t step, T value);

  //----------------------------------------------------------------------------
  // private data members
  //----------------------------------------------------------------------------

  // trace length
  //
  size_t length;

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
  // friend operators
  //----------------------------------------------------------------------------

  // equality
  //
  friend bool operator == (const Trace &, const Trace &);
  friend bool operator != (const Trace &, const Trace &);
};

} // namespace ConcuBinE

#endif
