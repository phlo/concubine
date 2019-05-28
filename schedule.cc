#include "schedule.hh"

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
      word thread;

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
      word pc;

      if (line >> pc)
        {
          if (pc >= program.size())
              parser_error(
                path,
                line_num,
                "illegal program counter [" + to_string(pc) + "]");
        }
      else
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing program counter");

          if (token != "-")
            try
              {
                pc = program.get_pc(token);
              }
            catch (...)
              {
                parser_error(path, line_num, "unknown label [" + token + "]");
              }
        }

      /* parse instruction symbol */
      string symbol;

      if (!(line >> symbol))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing instruction symbol");

          parser_error(path, line_num, "unable to parse instruction symbol");
        }

      bool flush = symbol == "FLUSH";

      if (!flush && !Instruction::Set::contains(symbol))
        parser_error(path, line_num, "unknown instruction [" + symbol + "]");

      /* parse instruction argument */
      word arg;

      if (!(line >> arg))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing instruction argument");

          if (flush && token != "-")
            parser_error(
              path,
              line_num,
              "illegal accumulator register value [" + token + "]");

          const Instruction_ptr cmd = program.at(pc);

          /* arg is an indirect memory address */
          if (token.front() == '[')
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
            parser_error(path, line_num, symbol + " does not support labels");
        }

      /* parse accu */
      word accu;

      if (!(line >> accu))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing accumulator register value");

          if (!flush || token != "-")
            parser_error(
              path,
              line_num,
              "illegal accumulator register value [" + token + "]");
        }

      /* parse mem */
      word mem;

      if (!(line >> mem))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing CAS memory register value");

          if (!flush || token != "-")
            parser_error(
              path,
              line_num,
              "illegal CAS memory register value [" + token + "]");
        }

      /* parse heap cell */
      optional<Heap_Cell> heap;

      if (!(line >> token))
        parser_error(path, line_num, "missing heap update");

      string cell = token.substr(1, token.size() - 2);

      if (!cell.empty())
        {
          try
            {
              cell = cell.substr(1, cell.size() - 2);
              size_t split = cell.find(',');
              word idx = stoul(cell.substr(0, split));
              word val = stoul(cell.substr(split + 1));

              /* heap cell update */
              heap = {idx, val};
            }
          catch (const exception & e)
            {
              parser_error(
                path,
                line_num,
                "illegal heap update [" + token + "]");
            }

          /* only flushes and atomic operations may write to memory */
          /* TODO: uncomment when updated
          if (!flush && !(program[pc]->type() & Instruction::Types::atomic))
            parser_error(
              path,
              line_num,
              "illegal heap update [" + symbol + "]");
          */
        }

      /* append to schedule */
      if (flush)
        {
          if (!heap)
            parser_error(path, line_num, "missing heap update");

          push_back(thread, *heap);
        }
      else
        push_back(thread, pc, accu, mem, heap);
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
}

void Schedule::push_back (
                          Schedule::Updates & updates,
                          const unsigned long step,
                          const word val
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
                          const word pc,
                          const word accu,
                          const word mem,
                          const optional<Heap_Cell> & heap
                         )
{
  ++bound;

  push_back(thread_updates, bound, thread);
  push_back(pc_updates[thread], bound, pc);
  push_back(accu_updates[thread], bound, accu);
  push_back(mem_updates[thread], bound, mem);

  if (heap)
    push_back(heap_updates[heap->idx], bound, heap->val);
}

void Schedule::push_back (const unsigned long thread, const Heap_Cell & heap)
{
  ++bound;

  flushes.insert(bound);
  push_back(thread_updates, bound, thread);
  push_back(heap_updates[heap.idx], bound, heap.val);
}

void Schedule::insert_thread (const unsigned long step, const word thread)
{
  push_back(thread_updates, step, thread);

  if (step > bound)
    bound = step;
}

void Schedule::insert_pc (
                          const unsigned long step,
                          const word thread,
                          const word pc
                         )
{
  push_back(pc_updates.at(thread), step, pc);

  if (step > bound)
    bound = step;
}

void Schedule::insert_accu (
                            const unsigned long step,
                            const word thread,
                            const word accu
                           )
{
  push_back(accu_updates.at(thread), step, accu);

  if (step > bound)
    bound = step;
}

void Schedule::insert_mem (
                           const unsigned long step,
                           const word thread,
                           const word mem
                          )
{
  push_back(mem_updates.at(thread), step, mem);

  if (step > bound)
    bound = step;
}

void Schedule::insert_heap (const unsigned long step, const Heap_Cell & heap)
{
  push_back(heap_updates[heap.idx], step, heap.val);

  if (step > bound)
    bound = step;
}

void Schedule::insert_flush (const unsigned long step)
{
  flushes.insert(step);

  if (step > bound)
    bound = step;
}

size_t Schedule::size () { return bound; }

Schedule::iterator Schedule::begin ()
{
  return iterator(this);
}

Schedule::iterator Schedule::end ()
{
  return iterator(this, bound + 1);
}

std::string Schedule::print ()
{
  ostringstream ss;

  const char sep = '\t';

  /* schedule metadata */
  for (const Program_ptr & program : *programs)
    ss << program->path << eol;

  /* separator */
  ss << '.' << eol;

  /* column headers */
  ss << "# tid\tpc\tcmd\targ\taccu\tmem\theap" << eol;

  for (const auto & step : *this)
    {
      /* thread id */
      ss << step.thread << sep;

      if (step.flush)
        {
          ss
            << '-' << sep // program counter
            << "FLUSH" << sep // instruction symbol
            << '-' << sep // instruction argument
            << '-' << sep // accumulator
            << '-' << sep; // CAS memory register
        }
      else
        {
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

          /* instruction symbol */
          ss << op->symbol() << sep;

          /* instruction argument */
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

          /* accumulator / CAS memory register */
          ss << step.accu << sep << step.mem << sep;
        }

      /* heap update */
      ss << '{';

      if (step.heap)
        ss << '(' << step.heap->idx << ',' << step.heap->val << ')';

      ss << '}' << eol;
    }

  return ss.str();
}

Schedule::iterator::iterator (Schedule * _schedule, unsigned long _step) :
  schedule(_schedule),
  step(_step),
  thread({schedule->thread_updates.begin(), schedule->thread_updates.end()})
{
  if (step > schedule->bound)
    return;

  size_t num_threads = schedule->programs->size();

  /* initialize state update iterator lists */
  pc.reserve(num_threads);
  for (const auto & updates : schedule->pc_updates)
    pc.push_back({updates.begin(), updates.end()});

  accu.reserve(num_threads);
  for (const auto & updates : schedule->accu_updates)
    accu.push_back({updates.begin(), updates.end()});

  mem.reserve(num_threads);
  for (const auto & updates : schedule->mem_updates)
    mem.push_back({updates.begin(), updates.end()});

  heap.reserve(schedule->heap_updates.size());
  for (const auto & [idx, updates] : schedule->heap_updates)
    heap[idx] = {updates.begin(), updates.cend()};

  assign();
}

word Schedule::iterator::next_thread_state (Iterators & state)
{
  auto next {std::next(state.cur)};

  while (next != state.end && next->first <= step)
    state.cur = next++;

  return state.cur->second;
}

optional<Schedule::Heap_Cell> Schedule::iterator::next_heap_state ()
{
  if (
      Store_ptr store =
        dynamic_pointer_cast<Store>(
          schedule->programs->at(update.thread)->at(update.pc))
     )
    {
      word idx =
        store->indirect
          ? schedule->heap_updates[store->arg].rend()->second
          : store->arg;

      auto & cell = heap.at(idx);

      if (cell.cur->first == step)
        return {{idx, cell.cur++->second}};
    }

  return {};
}

void Schedule::iterator::assign ()
{
  update.flush  = schedule->flushes.find(step) != schedule->flushes.end();
  update.thread = next_thread_state(thread);
  update.pc     = next_thread_state(pc[update.thread]);
  update.accu   = next_thread_state(accu[update.thread]);
  update.mem    = next_thread_state(mem[update.thread]);
  update.heap   = next_heap_state();
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
  return update;
}

Schedule::iterator::pointer Schedule::iterator::operator -> () const
{
  return &update;
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
