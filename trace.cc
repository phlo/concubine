#include "trace.hh"

#include <cassert>
#include <sstream>

#include "instruction.hh"
#include "mmap.hh"
#include "parser.hh"

namespace ConcuBinE {

//==============================================================================
// Trace
//==============================================================================

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

Trace::Trace (const Program::List::ptr & p,
              const std::shared_ptr<MMap> & m) :
  programs(p),
  mmap(m),
  length(0),
  exit(0)
{
  init_register_states();
}

Trace::Trace(std::istream & file, const std::string & path) :
  programs(std::make_shared<Program::List>()),
  length(0),
  exit(0)
{
  std::string token;

  size_t line_num = 1;

  // parse programs
  for (std::string line_buf; std::getline(file, line_buf); ++line_num)
    {
      // skip empty lines
      if (line_buf.empty())
        continue;

      std::istringstream line(line_buf);

      // skip comments
      if (line >> token && token.front() == '#')
        continue;

      // check for memory map (all programs have been parsed)
      if (token == ".")
        {
          if ((line >> token))
            mmap = std::make_shared<MMap>(create_from_file<MMap>(token));

          break;
        }

      try { programs->push_back(create_from_file<Program>(token)); }
      catch (const std::exception & e)
        {
          parser_error(
            path,
            line_num,
            e.what());
        }
    }

  // check header
  if (programs->empty())
    parser_error(path, line_num, "missing threads");

  // initialize thread state update lists
  init_register_states();

  // parse body
  line_num++;
  for (std::string line_buf; std::getline(file, line_buf); line_num++)
    {
      // skip empty lines
      if (line_buf.empty())
        continue;

      std::istringstream line(line_buf);

      // skip comments
      if (line_buf[line_buf.find_first_not_of(" \t")] == '#')
        continue;

      // parse thread id
      word_t thread;

      if (!(line >> thread))
        {
          line.clear();
          line >> token;
          parser_error(path, line_num, "illegal thread id [" + token + "]");
        }

      if (thread >= programs->size())
          parser_error(
            path,
            line_num,
            "unknown thread id [" + std::to_string(thread) + "]");

      const Program & program = (*programs)[thread];

      // parse pc
      word_t pc;

      if (!(line >> pc))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing program counter");

          try { pc = program.get_pc(token); }
          catch (...)
            {
              parser_error(path, line_num, "unknown label [" + token + "]");
            }
        }

      if (pc >= program.size())
          parser_error(
            path,
            line_num,
            "illegal program counter [" + std::to_string(pc) + "]");

      const Instruction & op = program[pc];

      // parse instruction symbol
      std::string symbol;

      if (!(line >> symbol))
        parser_error(path, line_num, "missing instruction symbol");

      bool flush = symbol == "FLUSH";

      if (!flush && !Instruction::contains(symbol))
        parser_error(path, line_num, "unknown instruction [" + symbol + "]");

      if (!flush && symbol != op.symbol())
        parser_error(
          path,
          line_num,
          "unexpected instruction [" + symbol + " != " + op.symbol() + "]");

      // parse instruction argument
      word_t arg;

      if (flush || Instruction::is_nullary(symbol))
        {
          if (!(line >> token))
            parser_error(path, line_num, "missing instruction argument");

          if (token != "-")
            parser_error(
              path,
              line_num,
              "illegal instruction argument [" + token + "]");
        }
      else if (!(line >> arg))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing instruction argument");

          // arg is an indirect memory address
          if (token.front() == '[')
            {
              if (op.is_memory())
                {
                  std::istringstream addr(token.substr(1, token.size() - 2));

                  // check if address is a number
                  if (!(addr >> arg))
                    parser_error(
                      path,
                      line_num,
                      "indirect addressing does not support labels");
                }
              else
                parser_error(
                  path,
                  line_num,
                  symbol + " does not support indirect addressing");
            }
          // arg is a label
          else if (op.is_jump())
            {
              try { arg = program.get_pc(token); }
              catch (...)
                {
                  parser_error(path, line_num, "unknown label [" + token + "]");
                }
            }
          else
            parser_error(
              path,
              line_num,
              symbol + " does not support labels [" + token + "]");
        }

      // parse accu
      word_t accu;

      if (!(line >> accu))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing accumulator register value");

          parser_error(
            path,
            line_num,
            "illegal accumulator register value [" + token + "]");
        }

      // parse mem
      word_t mem;

      if (!(line >> mem))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing CAS memory register value");

          parser_error(
            path,
            line_num,
            "illegal CAS memory register value [" + token + "]");
        }

      // parse store buffer address
      word_t sb_adr;

      if (!(line >> sb_adr))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing store buffer address");

          parser_error(
            path,
            line_num,
            "illegal store buffer address [" + token + "]");
        }

      // parse store buffer value
      word_t sb_val;

      if (!(line >> sb_val))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing store buffer value");

          parser_error(
            path,
            line_num,
            "illegal store buffer value [" + token + "]");
        }

      // parse store buffer full flag
      bool sb_full;

      if (!(line >> sb_full))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing store buffer full flag");

          parser_error(
            path,
            line_num,
            "illegal store buffer full flag [" + token + "]");
        }

      // parse heap cell
      std::optional<std::pair<word_t, word_t>> heap;

      if (!(line >> token))
        parser_error(path, line_num, "missing heap update");

      std::string cell = token.substr(1, token.size() - 2);

      if (!cell.empty())
        {
          try
            {
              cell = cell.substr(1, cell.size() - 2);
              size_t split = cell.find(',');
              word_t adr = stoul(cell.substr(0, split));
              word_t val = stoul(cell.substr(split + 1));

              // heap cell update
              heap = {adr, val};
            }
          catch (const std::exception & e)
            {
              parser_error(
                path,
                line_num,
                "illegal heap update [" + token + "]");
            }
        }

      // append to trace
      push_back(thread, pc, accu, mem, sb_adr, sb_val, sb_full, heap, flush);
    }

  if (!length)
    parser_error(path, line_num, "empty trace");
}

//------------------------------------------------------------------------------
// member functions
//------------------------------------------------------------------------------

// Trace::init_register_states -------------------------------------------------

void Trace::init_register_states ()
{
  const size_t num_threads = programs->size();

  pc_updates.resize(num_threads);
  accu_updates.resize(num_threads);
  mem_updates.resize(num_threads);
  sb_adr_updates.resize(num_threads);
  sb_val_updates.resize(num_threads);
  sb_full_updates.resize(num_threads);
}

// Trace::init_heap ------------------------------------------------------------

void Trace::init_heap (const word_t address, const word_t value)
{
  if (!mmap)
    mmap = std::make_shared<MMap>();

  (*mmap)[address] = value;
}

// Trace::push_back ------------------------------------------------------------

template <class T>
bool Trace::push_back (Trace::update_map<T> & updates,
                       const size_t step,
                       const T value)
{
  if (updates.empty())
    {
      updates[step] = value;
      return true;
    }
  else
    {
      auto end = updates.cend();
      auto prev = updates.crbegin();

      // ensure that no update exists for this step
      if (prev->first == step)
        throw std::runtime_error("update already exists");

      // insert if value doesn't change
      if (prev->second != value)
        {
          updates.emplace_hint(end, step, value);
          return true;
        }
    }

  return false;
}

void Trace::push_back (const word_t thread,
                       const word_t pc,
                       const word_t accu,
                       const word_t mem,
                       const word_t buffer_adr,
                       const word_t buffer_val,
                       const word_t buffer_full,
                       std::optional<std::pair<word_t, word_t>> & heap,
                       const bool flush)
{
  push_back<word_t>(thread_updates, length, thread);
  push_back<word_t>(pc_updates[thread], length, pc);
  push_back<word_t>(accu_updates[thread], length, accu);
  push_back<word_t>(mem_updates[thread], length, mem);
  push_back<word_t>(sb_adr_updates[thread], length, buffer_adr);
  push_back<word_t>(sb_val_updates[thread], length, buffer_val);
  push_back<bool>(sb_full_updates[thread], length, buffer_full);

  if (heap)
    {
      heap_adr_updates.emplace_hint(
        heap_adr_updates.end(),
        length,
        heap->first);
      push_back(heap_val_updates[heap->first], length, heap->second);
    }

  if (flush)
    flushes.insert(length);

  length++;
}

// Trace::push_back_thread -----------------------------------------------------

void Trace::push_back_thread (size_t step, const word_t thread)
{
  push_back<word_t>(thread_updates, step, thread);

  if (step >= length)
    length = ++step;
}

// Trace::push_back_pc ---------------------------------------------------------

void Trace::push_back_pc (size_t step, const word_t thread, const word_t pc)
{
  if (push_back<word_t>(pc_updates[thread], step, pc) && step >= length)
    length = ++step;
}

// Trace::push_back_accu -------------------------------------------------------

void Trace::push_back_accu (size_t step, const word_t thread, const word_t accu)
{
  if (push_back<word_t>(accu_updates[thread], step, accu) && step >= length)
    length = ++step;
}

// Trace::push_back_mem --------------------------------------------------------

void Trace::push_back_mem (size_t step, const word_t thread, const word_t mem)
{
  if (push_back<word_t>(mem_updates[thread], step, mem) && step >= length)
    length = ++step;
}

// Trace::push_back_sb_adr -----------------------------------------------------

void Trace::push_back_sb_adr (size_t step,
                              const word_t thread,
                              const word_t adr)
{
  if (push_back<word_t>(sb_adr_updates[thread], step, adr) && step >= length)
    length = ++step;
}

// Trace::push_back_sb_val -----------------------------------------------------

void Trace::push_back_sb_val (size_t step,
                              const word_t thread,
                              const word_t val)
{
  if (push_back<word_t>(sb_val_updates[thread], step, val) && step >= length)
    length = ++step;
}

// Trace::push_back_sb_full ----------------------------------------------------

void Trace::push_back_sb_full (size_t step,
                               const word_t thread,
                               const bool full)
{
  if (push_back<bool>(sb_full_updates[thread], step, full) && step >= length)
    length = ++step;
}

// Trace::push_back_heap -------------------------------------------------------

void Trace::push_back_heap (size_t step, const word_t adr, const word_t val)
{
  heap_adr_updates.emplace_hint(heap_adr_updates.end(), step, adr);
  push_back<word_t>(heap_val_updates[adr], step, val);

  if (step >= length)
    length = ++step;
}

// Trace::push_back_flush ------------------------------------------------------

void Trace::push_back_flush (size_t step)
{
  flushes.insert(step);

  if (step >= length)
    length = ++step;
}

// Trace::thread ---------------------------------------------------------------

word_t Trace::thread () const
{
  assert(!thread_updates.empty());

  return thread_updates.crbegin()->second;
}

#define RETURN_STATE(update_map, k) \
  do { \
    auto rit = update_map.crbegin(); \
    while (rit != update_map.crend() && rit->first > k) ++rit; \
    return rit->second; \
  } while (0)

word_t Trace::thread (const size_t k) const
{
  assert(k < length);

  RETURN_STATE(thread_updates, k);
}

// Trace::flush ----------------------------------------------------------------

bool Trace::flush (const word_t step) const
{
  return flushes.find(step) != flushes.end();
}

// Trace::pc -------------------------------------------------------------------

word_t Trace::pc (const word_t thread) const
{
  assert(!pc_updates[thread].empty());

  return pc_updates[thread].crbegin()->second;
}

word_t Trace::pc (const size_t k, const word_t thread) const
{
  assert(k < length);
  assert(thread < pc_updates.size());

  RETURN_STATE(pc_updates[thread], k);
}

// Trace::accu -----------------------------------------------------------------

word_t Trace::accu (const word_t thread) const
{
  assert(!accu_updates[thread].empty());

  return accu_updates[thread].crbegin()->second;
}

word_t Trace::accu (const size_t k, const word_t thread) const
{
  assert(k < length);
  assert(thread < accu_updates.size());

  RETURN_STATE(accu_updates[thread], k);
}

// Trace::mem ------------------------------------------------------------------

word_t Trace::mem (const word_t thread) const
{
  assert(!mem_updates[thread].empty());

  return mem_updates[thread].crbegin()->second;
}

word_t Trace::mem (const size_t k, const word_t thread) const
{
  assert(k < length);
  assert(thread < mem_updates.size());

  RETURN_STATE(mem_updates[thread], k);
}

// Trace::sb_adr ---------------------------------------------------------------

word_t Trace::sb_adr (const word_t thread) const
{
  assert(!sb_adr_updates[thread].empty());

  return sb_adr_updates[thread].crbegin()->second;
}

word_t Trace::sb_adr (const size_t k, const word_t thread) const
{
  assert(k < length);
  assert(thread < sb_adr_updates.size());

  RETURN_STATE(sb_adr_updates[thread], k);
}

// Trace::sb_val ---------------------------------------------------------------

word_t Trace::sb_val (const word_t thread) const
{
  assert(!sb_val_updates[thread].empty());

  return sb_val_updates[thread].crbegin()->second;
}

word_t Trace::sb_val (const size_t k, const word_t thread) const
{
  assert(k < length);
  assert(thread < sb_val_updates.size());

  RETURN_STATE(sb_val_updates[thread], k);
}

// Trace::sb_full --------------------------------------------------------------

bool Trace::sb_full (const word_t thread) const
{
  assert(!sb_full_updates[thread].empty());

  return sb_full_updates[thread].crbegin()->second;
}

bool Trace::sb_full (const size_t k, const word_t thread) const
{
  assert(k < length);
  assert(thread < sb_full_updates.size());

  RETURN_STATE(sb_full_updates[thread], k);
}

// Trace::heap -----------------------------------------------------------------

std::optional<word_t> Trace::heap (const word_t address) const
{
  if (heap_val_updates.find(address) != heap_val_updates.end())
    return heap_val_updates.at(address).crbegin()->second;

  if (mmap && mmap->find(address) != mmap->end())
    return (*mmap)[address];

  return {};
}

std::optional<word_t> Trace::heap (const size_t k, const word_t address) const
{
  if (heap_val_updates.find(address) != heap_val_updates.end())
    RETURN_STATE(heap_val_updates.at(address), k);

  if (mmap && mmap->find(address) != mmap->end())
    return (*mmap)[address];

  return {};
}

// Trace::size -----------------------------------------------------------------

size_t Trace::size () const { return length; }

// Trace::begin ----------------------------------------------------------------

Trace::iterator Trace::begin () const
{
  return iterator(this);
}

// Trace::end ------------------------------------------------------------------

Trace::iterator Trace::end () const
{
  return iterator(this, size());
}

// Trace::print ----------------------------------------------------------------

std::string Trace::print (const Step & step) const
{
  constexpr char sep = '\t';

  std::ostringstream ss;

  // thread id
  ss << step.thread << sep;

  // reference to program
  const Program & program = (*programs)[step.thread];

  // reference to current instruction
  const Instruction & op = program[step.pc];

  // program counter
  try
    {
      ss << program.get_label(step.pc) << sep;
    }
  catch (...)
    {
      ss << step.pc << sep;
    }

  // instruction symbol / argument
  if (step.flush)
    {
      ss << "FLUSH" << sep << '-' << sep;
    }
  else
    {
      ss << op.symbol() << sep;

      std::string arg {'-'};

      if (op.is_unary())
        {
          arg = std::to_string(op.arg());

          if (op.is_memory())
            {
              if (op.indirect())
                arg = '[' + arg + ']';
            }
          else if (op.is_jump())
            try { arg = program.get_label(op.arg()); } catch (...) {}
        }

      ss << arg << sep;
    }

  // accumulator / CAS memory register
  ss << step.accu << sep << step.mem << sep;

  // store buffer
  ss << step.sb_adr << sep << step.sb_val << sep << step.sb_full << sep;

  // heap update
  ss << '{';

  if (step.heap)
    ss << '(' << step.heap->first << ',' << step.heap->second << ')';

  ss << '}';

  // step number
  if (verbose)
    ss << sep << "# " << std::to_string(step);

  ss << eol;

  return ss.str();
}

std::string Trace::print () const
{
  std::ostringstream ss;

  // trace metadata
  for (const Program & program : *programs)
    ss << program.path << eol;

  // separator + mmap
  ss << '.';

  if (mmap)
    ss << ' ' << mmap->path;

  ss << eol;

  // column headers
  ss << "# tid\tpc\tcmd\targ\taccu\tmem\tadr\tval\tfull\theap" << eol;

  for (const auto & step : *this)
    ss << print(step);

  return ss.str();
}

//==============================================================================
// Trace::Step
//==============================================================================

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

Trace::Step::Step (size_t k) : number(k) {}

//------------------------------------------------------------------------------
// member operators
//------------------------------------------------------------------------------

// conversion to size_t
//
Trace::Step::operator size_t () const { return number; }

// increment
//
Trace::Step & Trace::Step::operator ++ () { number++; return *this; }

//==============================================================================
// Trace::iterator
//==============================================================================

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

Trace::iterator::iterator (const Trace * t, const size_t s) :
  trace(t),
  thread({trace->thread_updates.begin(), trace->thread_updates.end()})
{
  if ((step = s) > trace->length)
    return;

  // initialize register state update iterator lists
  init_iterators(pc, trace->pc_updates);
  init_iterators(accu, trace->accu_updates);
  init_iterators(mem, trace->mem_updates);
  init_iterators(sb_adr, trace->sb_adr_updates);
  init_iterators(sb_val, trace->sb_val_updates);
  init_iterators(sb_full, trace->sb_full_updates);

  // initialize heap state update iterators
  heap_adr = {trace->heap_adr_updates.begin(), trace->heap_adr_updates.end()};
  for (const auto & [idx, updates] : trace->heap_val_updates)
    heap_val[idx] = {updates.begin(), updates.end()};

  assign();
}

//------------------------------------------------------------------------------
// member functions
//------------------------------------------------------------------------------

// Trace::iterator::init_iterators ---------------------------------------------

template <typename T>
void Trace::iterator::init_iterators (thread_state_iterators<T> & iterators,
                                      const thread_map<T> & updates)
{
  iterators.reserve(trace->programs->size());
  for (const auto & u: updates)
    iterators.push_back({u.begin(), u.end()});
}

// Trace::iterator::next_state -------------------------------------------------

template <typename T>
T Trace::iterator::next_state (update_map_iterator<T> & state)
{
  if (state.cur == state.end)
    return 0;

  auto next = std::next(state.cur);

  while (next != state.end && next->first <= step)
    state.cur = next++;

  return state.cur->second;
}

// Trace::iterator::next_heap_state --------------------------------------------

std::optional<std::pair<word_t, word_t>> Trace::iterator::next_heap_state ()
{
  if (heap_adr.cur != heap_adr.end)
    {
      const word_t adr = next_state(heap_adr);

      if (heap_adr.cur->first == step.number)
        return {{adr, next_state(heap_val[adr])}};
    }

  return {};
}

// Trace::iterator::assign -----------------------------------------------------

void Trace::iterator::assign ()
{
  step.thread  = next_state(thread);
  step.pc      = next_state(pc[step.thread]);
  step.accu    = next_state(accu[step.thread]);
  step.mem     = next_state(mem[step.thread]);
  step.sb_adr  = next_state(sb_adr[step.thread]);
  step.sb_val  = next_state(sb_val[step.thread]);
  step.sb_full = next_state(sb_full[step.thread]);
  step.flush   = trace->flushes.find(step) != trace->flushes.end();
  step.heap    = next_heap_state();
}

//------------------------------------------------------------------------------
// member operators
//------------------------------------------------------------------------------

// increment -------------------------------------------------------------------

Trace::iterator & Trace::iterator::operator ++ ()
{
  // prevent increments beyond end()
  if (step < trace->length)
    if (++step < trace->length)
      assign();

  return *this;
}

Trace::iterator Trace::iterator::operator ++ (int)
{
  iterator retval = *this;
  ++(*this);
  return retval;
}

// equality --------------------------------------------------------------------

bool Trace::iterator::operator == (const iterator & other) const
{
  return trace == other.trace && step.number == other.step.number;
}

bool Trace::iterator::operator != (const iterator & other) const
{
  return !(*this == other);
}

// dereference -----------------------------------------------------------------

Trace::iterator::reference Trace::iterator::operator * () const
{
  return step;
}

Trace::iterator::pointer Trace::iterator::operator -> () const
{
  return &step;
}

//==============================================================================
// non-member operators
//==============================================================================

// equality --------------------------------------------------------------------

bool operator == (const Trace & a, const Trace & b)
{
  if (a.length != b.length)
    return false;

  if (a.exit != b.exit)
    return false;

  if (a.programs->size() != b.programs->size())
    return false;

  for (size_t i = 0; i < a.programs->size(); i++)
    if ((*a.programs)[i] != (*b.programs)[i])
      return false;

  return
    a.flushes == b.flushes &&
    a.thread_updates == b.thread_updates &&
    a.pc_updates == b.pc_updates &&
    a.accu_updates == b.accu_updates &&
    a.mem_updates == b.mem_updates &&
    a.sb_adr_updates == b.sb_adr_updates &&
    a.sb_val_updates == b.sb_val_updates &&
    a.sb_full_updates == b.sb_full_updates &&
    a.heap_adr_updates == b.heap_adr_updates &&
    a.heap_val_updates == b.heap_val_updates;
}

bool operator != (const Trace & a, const Trace & b)
{
  return !(a == b);
}

bool operator == (const Trace::Step & a, const Trace::Step & b)
{
  return
    a.number == b.number &&
    a.thread == b.thread &&
    a.pc == b.pc &&
    a.accu == b.accu &&
    a.mem == b.mem &&
    a.sb_adr == b.sb_adr &&
    a.sb_val == b.sb_val &&
    a.sb_full == b.sb_full &&
    a.flush == b.flush &&
    a.heap == b.heap;
}

bool operator != (const Trace::Step & a, const Trace::Step & b)
{
  return !(a == b);
}

} // namespace ConcuBinE
