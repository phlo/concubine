#include "schedule.hh"

#include <cassert>
#include <sstream>

#include "instructionset.hh"
#include "parser.hh"

using namespace std;

Schedule::Schedule (Program_list_ptr p) :
  bound(0),
  programs(p),
  exit(0)
{
  init_state_update_lists();
}

Schedule::Schedule(istream & file, string & path) :
  bound(0),
  programs(make_shared<Program_list>()),
  exit(0)
{
  string token;

  unsigned long line_num = 1;

  /* parse programs */
  for (string line_buf; getline(file, line_buf); ++line_num)
    {
      /* skip empty lines */
      if (line_buf.empty())
        continue;

      istringstream line(line_buf);

      /* skip comments */
      if (line >> token && token.front() == '#')
        continue;

      /* check if all programs have been parsed */
      if (token == ".")
        break;

      try
        {
          programs->push_back(create_from_file<Program>(token));
        }
      catch (const exception & e)
        {
          parser_error(
            path,
            line_num,
            e.what());
        }
    }

  /* check header */
  if (programs->empty())
    parser_error(path, line_num, "missing threads");

  /* initialize thread state update lists */
  init_state_update_lists();

  /* parse body */
  line_num++;
  unsigned long step = 0;
  for (string line_buf; getline(file, line_buf); ++line_num)
    {
      /* skip empty lines */
      if (line_buf.empty())
        continue;

      istringstream line(line_buf);

      /* skip comments */
      if (line_buf[line_buf.find_first_not_of(" \t")] == '#')
        continue;

      step++;

      /* parse thread id */
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
            "unknown thread id [" + to_string(thread) + "]");

      const Program & program = *programs->at(thread);

      /* parse pc */
      word_t pc;

      if (!(line >> pc))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing program counter");

          try
            {
              pc = program.get_pc(token);
            }
          catch (...)
            {
              parser_error(path, line_num, "unknown label [" + token + "]");
            }
        }

      if (pc >= program.size())
          parser_error(
            path,
            line_num,
            "illegal program counter [" + to_string(pc) + "]");

      /* parse instruction symbol */
      string symbol;

      if (!(line >> symbol))
        parser_error(path, line_num, "missing instruction symbol");

      bool flush = symbol == "FLUSH";

      if (!flush && !Instruction::Set::contains(symbol))
        parser_error(path, line_num, "unknown instruction [" + symbol + "]");

      /* parse instruction argument */
      word_t arg;

      if (flush)
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

          const Instruction_ptr cmd = program.at(pc);

          /* arg is an indirect memory address */
          if (flush && token == "-")
            ;
          else if (token.front() == '[')
            {
              if (dynamic_pointer_cast<Memory>(cmd))
                {
                  istringstream addr(token.substr(1, token.size() - 2));

                  /* check if address is a number */
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
          /* arg is a label */
          else if (dynamic_pointer_cast<Jmp>(cmd))
            {
              try
                {
                  arg = program.get_pc(token);
                }
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

      /* parse accu */
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

      /* parse mem */
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

      /* parse store buffer address */
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

      /* parse store buffer value */
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

      /* parse store buffer full flag */
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

      /* parse heap cell */
      optional<Heap> heap;

      if (!(line >> token))
        parser_error(path, line_num, "missing heap update");

      string cell = token.substr(1, token.size() - 2);

      if (!cell.empty())
        {
          try
            {
              cell = cell.substr(1, cell.size() - 2);
              size_t split = cell.find(',');
              word_t adr = stoul(cell.substr(0, split));
              word_t val = stoul(cell.substr(split + 1));

              /* heap cell update */
              heap = {adr, val};
            }
          catch (const exception & e)
            {
              parser_error(
                path,
                line_num,
                "illegal heap update [" + token + "]");
            }

          /* only flushes and atomic operations may write to memory */
          if (!flush && !(program[pc]->type() & Instruction::Types::atomic))
            parser_error(
              path,
              line_num,
              symbol + " can't perform heap updates");
        }

      /* append to schedule */
      if (flush)
        {
          if (!heap)
            parser_error(path, line_num, "missing heap update");

          push_back(thread, *heap);
        }
      else
        push_back(thread, pc, accu, mem, sb_adr, sb_val, sb_full, heap);
    }

  if (!bound)
    parser_error(path, line_num, "empty schedule");
}

void Schedule::init_state_update_lists ()
{
  size_t num_threads = programs->size();

  pc_updates.resize(num_threads);
  accu_updates.resize(num_threads);
  mem_updates.resize(num_threads);
  sb_adr_updates.resize(num_threads);
  sb_val_updates.resize(num_threads);
  sb_full_updates.resize(num_threads);
}

template <typename T>
void Schedule::push_back (
                          Schedule::Updates<T> & updates,
                          const unsigned long step,
                          const T val
                         )
{
  if (updates.empty())
    {
      updates.insert({step, val});
    }
  else
    {
      auto end = updates.end();
      auto prev = std::prev(end);

      /* ensure that no update exists for this step */
      if (prev->first == step)
        throw runtime_error("update already exists");

      /* insert if value doesn't change */
      if (prev->second != val)
        updates.insert(end, {step, val});
    }
}

void Schedule::push_back (
                          const unsigned long thread,
                          const word_t pc,
                          const word_t accu,
                          const word_t mem,
                          const word_t buffer_adr,
                          const word_t buffer_val,
                          const word_t buffer_full,
                          const optional<Heap> & heap
                         )
{
  ++bound;

  push_back<word_t>(thread_updates, bound, thread);
  push_back<word_t>(pc_updates[thread], bound, pc);
  push_back<word_t>(accu_updates[thread], bound, accu);
  push_back<word_t>(mem_updates[thread], bound, mem);
  push_back<word_t>(sb_adr_updates[thread], bound, buffer_adr);
  push_back<word_t>(sb_val_updates[thread], bound, buffer_val);
  push_back<bool>(sb_full_updates[thread], bound, buffer_full);

  if (heap)
    push_back(heap_updates[heap->adr], bound, heap->val);
}

void Schedule::push_back (const unsigned long thread, const Heap & heap)
{
  ++bound;

  flushes.insert(bound);
  push_back<word_t>(thread_updates, bound, thread);
  push_back<bool>(sb_full_updates[thread], bound, false);
  push_back<word_t>(heap_updates[heap.adr], bound, heap.val);
}

void Schedule::insert_thread (const unsigned long step, const word_t thread)
{
  push_back<word_t>(thread_updates, step, thread);

  if (step > bound)
    bound = step;
}

void Schedule::insert_pc (
                          const unsigned long step,
                          const word_t thread,
                          const word_t pc
                         )
{
  push_back<word_t>(pc_updates.at(thread), step, pc);

  if (step > bound)
    bound = step;
}

void Schedule::insert_accu (
                            const unsigned long step,
                            const word_t thread,
                            const word_t accu
                           )
{
  push_back<word_t>(accu_updates.at(thread), step, accu);

  if (step > bound)
    bound = step;
}

void Schedule::insert_mem (
                           const unsigned long step,
                           const word_t thread,
                           const word_t mem
                          )
{
  push_back<word_t>(mem_updates.at(thread), step, mem);

  if (step > bound)
    bound = step;
}

void Schedule::insert_sb_adr (
                              const unsigned long step,
                              const word_t thread,
                              const word_t adr
                             )
{
  push_back<word_t>(sb_adr_updates.at(thread), step, adr);

  if (step > bound)
    bound = step;
}

void Schedule::insert_sb_val (
                              const unsigned long step,
                              const word_t thread,
                              const word_t val
                             )
{
  push_back<word_t>(sb_val_updates.at(thread), step, val);

  if (step > bound)
    bound = step;
}

void Schedule::insert_sb_full (
                               const unsigned long step,
                               const word_t thread,
                               const bool full
                              )
{
  push_back<bool>(sb_full_updates.at(thread), step, full);

  if (step > bound)
    bound = step;
}

void Schedule::insert_heap (const unsigned long step, const Heap & heap)
{
  push_back<word_t>(heap_updates[heap.adr], step, heap.val);

  if (step > bound)
    bound = step;
}

void Schedule::insert_flush (const unsigned long step)
{
  flushes.insert(step);

  if (step > bound)
    bound = step;
}

size_t Schedule::size () const { return bound; }

Schedule::iterator Schedule::begin () const
{
  return iterator(this);
}

Schedule::iterator Schedule::end () const
{
  return iterator(this, bound + 1);
}

std::string Schedule::print () const
{
  ostringstream ss;

  const char sep = '\t';

  /* schedule metadata */
  for (const Program_ptr & program : *programs)
    ss << program->path << eol;

  /* separator */
  ss << '.' << eol;

  /* column headers */
  ss << "# tid\tpc\tcmd\targ\taccu\tmem\tadr\tval\tfull\theap" << eol;

  for (const auto & step : *this)
    {
      /* thread id */
      ss << step.thread << sep;

      /* reference to program */
      const Program & program = *programs->at(step.thread);

      /* reference to current instruction */
      const Instruction_ptr & op = program[step.pc];

      /* program counter */
      try
        {
          ss << program.get_label(step.pc) << sep;
        }
      catch (...)
        {
          ss << step.pc << sep;
        }

      /* instruction symbol / argument */
      if (step.flush)
        {
          ss << "FLUSH" << sep << '-' << sep;
        }
      else
        {
          ss << op->symbol() << sep;

          string arg {'-'};

          if (auto u = dynamic_pointer_cast<Unary>(op))
            {
              arg = to_string(u->arg);

              if (auto m = dynamic_pointer_cast<Memory>(u))
                {
                  if (m->indirect)
                    arg = '[' + arg + ']';
                }
              else if (dynamic_pointer_cast<Jmp>(u))
                try
                  {
                    arg = program.get_label(u->arg);
                  }
              catch (...) {}
            }

          ss << arg << sep;
        }

      /* accumulator / CAS memory register */
      ss << step.accu << sep << step.mem << sep;

      /* store buffer */
      ss << step.sb_adr << sep << step.sb_val << sep << step.sb_full << sep;

      /* heap update */
      ss << '{';

      if (step.heap)
        ss << '(' << step.heap->adr << ',' << step.heap->val << ')';

      ss << '}' << eol;
    }

  return ss.str();
}

Schedule::Step::Step (unsigned long s) : step(s) {}

Schedule::Step::operator unsigned long () const { return step; }

Schedule::Step & Schedule::Step::operator ++ () { step++; return *this; }

Schedule::iterator::iterator (const Schedule * sc, unsigned long st) :
  schedule(sc),
  thread({schedule->thread_updates.begin(), schedule->thread_updates.end()})
{
  if ((step = st) > schedule->bound)
    return;

  /* initialize state update iterator lists */
  init_iterators(pc, schedule->pc_updates);
  init_iterators(accu, schedule->accu_updates);
  init_iterators(mem, schedule->mem_updates);
  init_iterators(sb_adr, schedule->sb_adr_updates);
  init_iterators(sb_val, schedule->sb_val_updates);
  init_iterators(sb_full, schedule->sb_full_updates);

  heap.reserve(schedule->heap_updates.size());
  for (const auto & [idx, updates] : schedule->heap_updates)
    heap[idx] = {updates.begin(), updates.cend()};

  assign();
}

template <typename T>
void Schedule::iterator::init_iterators (
                                         Thread_Iterators<T> & iterators,
                                         const Thread_Updates<T> & updates
                                        )
{
  iterators.reserve(schedule->programs->size());
  for (const auto & u: updates)
    iterators.push_back({u.begin(), u.end()});
}

template <typename T>
const T & Schedule::iterator::next_thread_state (Iterators<T> & state)
{
  auto next {std::next(state.cur)};

  while (next != state.end && next->first <= step)
    state.cur = next++;

  return state.cur->second;
}

const optional<Schedule::Heap> Schedule::iterator::next_heap_state ()
{
  if (step.flush)
    {
      auto & cell = heap.at(step.sb_adr);

      /* mind subsequent writes of an equal value to the same address */
      if (cell.cur->first == step)
        {
          assert(cell.cur->second == step.sb_val);
          cell.cur++;
        }

      return {{step.sb_adr, step.sb_val}};
    }

  const Instruction_ptr & op =
    schedule->programs->at(step.thread)->at(step.pc);

  if (op->type() & Instruction::Types::atomic)
    if (Memory_ptr atomic = dynamic_pointer_cast<Cas>(op))
      {
        word_t address = atomic->indirect
          ? schedule->heap_updates.at(atomic->arg).rend()->second
          : atomic->arg;

        auto & cell = heap.at(address);

        /* mind subsequent writes of an equal value to the same address */
        word_t value = cell.cur->first == step
          ? cell.cur++->second
          : (--cell.cur)++->second;

        return {{address, value}};
      }

  return {};
}

void Schedule::iterator::assign ()
{
  step.thread   = next_thread_state(thread);
  step.pc       = next_thread_state(pc[step.thread]);
  step.accu     = next_thread_state(accu[step.thread]);
  step.mem      = next_thread_state(mem[step.thread]);
  step.sb_adr   = next_thread_state(sb_adr[step.thread]);
  step.sb_val   = next_thread_state(sb_val[step.thread]);
  step.sb_full  = next_thread_state(sb_full[step.thread]);
  step.flush    = schedule->flushes.find(step) != schedule->flushes.end();
  step.heap     = next_heap_state();
}

Schedule::iterator & Schedule::iterator::operator ++ ()
{
  /* prevent increments beyond end() */
  if (step <= schedule->bound)
    if (++step <= schedule->bound)
      assign();

  return *this;
}

Schedule::iterator Schedule::iterator::operator ++ (int)
{
  iterator retval = *this;
  ++(*this);
  return retval;
}

bool Schedule::iterator::operator == (const iterator & other) const
{
  return schedule == other.schedule && step == other.step;
}

bool Schedule::iterator::operator != (const iterator & other) const
{
  return !(*this == other);
}

Schedule::iterator::reference Schedule::iterator::operator * () const
{
  return step;
}

Schedule::iterator::pointer Schedule::iterator::operator -> () const
{
  return &step;
}

bool operator == (const Schedule & a, const Schedule & b)
{
  if (a.bound != b.bound)
    return false;

  if (a.exit != b.exit)
    return false;

  if (a.programs->size() != b.programs->size())
    return false;

  for (size_t i = 0; i < a.programs->size(); i++)
    if (*a.programs->at(i) != *b.programs->at(i))
      return false;

  return
    a.flushes == b.flushes &&
    a.thread_updates == b.thread_updates &&
    a.pc_updates == b.pc_updates &&
    a.accu_updates == b.accu_updates &&
    a.mem_updates == b.mem_updates &&
    a.heap_updates == b.heap_updates;
}

bool operator != (const Schedule & a, const Schedule & b)
{
  return !(a == b);
}
