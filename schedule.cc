#include "schedule.hh"

#include <sstream>

#include "parser.hh"

using namespace std;

/* default constructor ********************************************************/
/*
Schedule::Schedule () :
  bound(0),
  programs(new ProgramList()),
  exit(0)
{}
*/

Schedule::Schedule (ProgramListPtr _programs) :
  bound(0),
  programs(_programs),
  exit(0)
{
  /* initialize thread state update lists */
  init_state_update_lists();
}

/* construct from file ********************************************************/
Schedule::Schedule(istream & file, string & path) :
  bound(0),
  programs(new ProgramList()),
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
      string symbol;
      word thread, pc, arg, accu, mem;

      /* skip empty lines */
      if (line_buf.empty())
        continue;

      istringstream line(line_buf);

      /* skip comments */
      if (line_buf[line_buf.find_first_not_of(" \t")] == '#')
        continue;

      step++;

      /* parse thread id */
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

      insert_thread(step, thread);

      const Program & program = *programs->at(thread);

      /* parse pc */
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

      insert_pc(step, thread, pc);

      /* parse instruction symbol */
      if (!(line >> symbol))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing instruction symbol");

          parser_error(path, line_num, "unable to parse instruction symbol");
        }

      if (!Instruction::Set::contains(symbol))
        parser_error(path, line_num, "unknown instruction [" + symbol + "]");

      /* parse instruction argument */
      if (!(line >> arg))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing instruction argument");

          const InstructionPtr cmd = program.at(pc);

          /* arg is an indirect memory address */
          if (token.front() == '[')
            {
              if (dynamic_pointer_cast<MemoryInstruction>(cmd))
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

      insert_accu(step, thread, accu);

      /* parse mem */
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

      insert_mem(step, thread, mem);

      /* parse heap cell */
      if (!(line >> token))
        parser_error(path, line_num, "missing heap update");

      string cell = token.substr(1, token.size() - 2);

      if (!cell.empty())
        try
          {
            cell = cell.substr(1, cell.size() - 2);
            size_t split = cell.find(',');
            word idx = stoul(cell.substr(0, split));
            word val = stoul(cell.substr(split + 1));

            /* heap cell update */
            insert_heap(step, {idx, val});
          }
        catch (const exception & e)
          {
            parser_error(path, line_num, "illegal heap update [" + token + "]");
          }
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

size_t Schedule::size ()
{
  return bound;
}

void Schedule::push_back (
                          const unsigned long tid,
                          const word pc,
                          const word accu,
                          const word mem,
                          const optional<Heap_Cell> heap
                         )
{
  /* append thread id */
  scheduled.push_back(tid);

  unsigned long step = scheduled.size();

  /* append pc state update */
  // update_list_t * updates = &pc_updates[tid];
  // if (updates->empty() || updates->back().second != pc)
    // updates->push_back(make_pair(step, pc));
  insert_pc(step, tid, pc);

  /* append accu state update */
  // updates = &accu_updates[tid];
  // if (updates->empty() || updates->back().second != accu)
    // updates->push_back(make_pair(step, accu));
  insert_accu(step, tid, accu);

  /* append mem state update */
  // updates = &mem_updates[tid];
  // if (updates->empty() || updates->back().second != mem)
    // updates->push_back(make_pair(step, mem));
  insert_mem(step, tid, mem);

  /* append heap state update */
  // if (heap)
    // {
      // updates = &heap_updates[heap->idx];
      // if (updates->empty() || updates->back().second != heap->val)
        // updates->push_back(make_pair(step, heap->val));
    // }
  if (heap)
    insert_heap(step, heap.value());

  /* raise bound */
  bound++;
}

void Schedule::insert_thread (const unsigned long step, const word thread)
{
  // HACK: try to preallocate using known bound!
  if (scheduled.size() < step)
    scheduled.resize(step);

  scheduled.at(step - 1) = thread;

  // NOTE: find a better way to update bound
  if (bound < step)
    bound = step;
}

// state update map inserter
// * insert iff previous value is different
// * erase next iff value is equal
void Schedule::insert (
                       Schedule::Update_Map & updates,
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
      auto hint {updates.lower_bound(step)};
      bool valid {hint != updates.end()};

      /* ensure that no update exists for this step */
      if (valid && hint->first == step)
        throw runtime_error("update already exists");

      /* return if value doesn't change */
      if (hint != updates.begin() && prev(hint)->second == val)
        return;

      updates.insert(hint, {step, val});

      /* erase next if value doesn't change */
      if (valid && hint->second == val)
        updates.erase(hint);
    }
}

void Schedule::insert_pc (const unsigned long step, const word thread, const word pc)
{
  insert(pc_updates.at(thread), step, pc);
}

void Schedule::insert_accu (const unsigned long step, const word thread, const word accu)
{
  insert(accu_updates.at(thread), step, accu);
}

void Schedule::insert_mem (const unsigned long step, const word thread, const word mem)
{
  insert(mem_updates.at(thread), step, mem);
}

void Schedule::insert_heap (const unsigned long step, const Heap_Cell heap)
{
  insert(heap_updates[heap.idx], step, heap.val);
}

/* Schedule::at (unsigned long) ***********************************************/
word Schedule::at (unsigned long step)
{
  return scheduled.at(step);
}

/* Schedule::begin (void) *****************************************************/
Schedule::iterator Schedule::begin ()
{
  return iterator(this);
}

/* Schedule::end (void) *******************************************************/
Schedule::iterator Schedule::end ()
{
  return iterator(this, bound + 1);
}

/* Schedule::print (void) *****************************************************/
std::string Schedule::print ()
{
  ostringstream ss;

  const char sep = '\t';

  /* schedule metadata */
  for (const ProgramPtr & program : *programs)
    ss << program->path << eol;

  /* separator */
  ss << '.' << eol;

  /* column headers */
  ss << "# tid\tpc\tcmd\targ\taccu\tmem\theap" << eol;

  for (const auto & step : *this)
    {
      /* reference to program */
      const Program & program = *programs->at(step.thread);

      /* reference to current instruction */
      const UnaryInstructionPtr cmd =
        dynamic_pointer_cast<UnaryInstruction>(
          program.at(step.pc));

      /* thread id */
      ss << step.thread << sep;

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
      ss << cmd->get_symbol() << sep;

      /* instruction argument */
      string arg(to_string(cmd->arg));

      if (auto m = dynamic_pointer_cast<MemoryInstruction>(cmd))
        {
          if (m->indirect)
            arg = '[' + arg + ']';
        }
      else if (dynamic_pointer_cast<Jmp>(cmd))
        try
          {
            arg = program.get_label(cmd->arg);
          }
        catch (...) {}

      ss << arg << sep;

      /* accumulator / CAS memory register */
      ss << step.accu << sep << step.mem << sep;

      /* heap update */
      ss << '{';

      if (step.heap)
        ss << '(' << step.heap->idx << ',' << step.heap->val << ')';

      ss << '}' << eol;
    }

  return ss.str();
}

/* Schedule::iterator (Schedule *, unsigned long) *****************************/
Schedule::iterator::iterator (Schedule * _schedule, unsigned long _step) :
  schedule(_schedule),
  step(_step)
{
  if (step > schedule->bound)
    return;

  size_t num_threads = schedule->programs->size();

  /* initialize state update iterators */
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

/* Schedule::iterator::next_thread_state (void) *******************************/
word Schedule::iterator::next_thread_state (Update_Iterators & state)
{
  auto next {std::next(state.cur)};

  while (next != state.end && next->first <= step)
    state.cur = next++;

  return state.cur->second;
}

/* Schedule::iterator::next_heap_state (void) *********************************/
optional<Schedule::Heap_Cell> Schedule::iterator::next_heap_state ()
{
  if (
      StorePtr store =
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

/* Schedule::iterator::assign (void) ******************************************/
void Schedule::iterator::assign ()
{
  update.thread = schedule->at(step - 1);
  update.pc     = next_thread_state(pc[update.thread]);
  update.accu   = next_thread_state(accu[update.thread]);
  update.mem    = next_thread_state(mem[update.thread]);
  update.heap   = next_heap_state();
}

/* Schedule::iterator::operator ++ (void) - prefix ****************************/
Schedule::iterator & Schedule::iterator::operator ++ ()
{
  /* prevent increments beyond end() */
  if (step <= schedule->bound)
    if (++step <= schedule->bound)
      assign();

  return *this;
}

/* Schedule::iterator::operator ++ (int) - postfix ****************************/
Schedule::iterator Schedule::iterator::operator ++ (int)
{
  iterator retval = *this;
  ++(*this);
  return retval;
}

/* Schedule::iterator::operator == (const Schedule::iterator &) ***************/
bool Schedule::iterator::operator == (const iterator & other) const
{
  return schedule == other.schedule && step == other.step;
}

/* Schedule::iterator::operator != (const Schedule::iterator &) ***************/
bool Schedule::iterator::operator != (const iterator & other) const
{
  return !(*this == other);
}

/* Schedule::iterator::operator * (void) **************************************/
Schedule::iterator::reference Schedule::iterator::operator * () const
{
  return update;
}

/* Schedule::iterator::operator -> (void) *************************************/
Schedule::iterator::pointer Schedule::iterator::operator -> () const
{
  return &update;
}

/* operator == (const Schedule &, const Schedule &) ***************************/
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

  if (a.scheduled != b.scheduled)
    return false;

  return
    a.pc_updates == b.pc_updates &&
    a.accu_updates == b.accu_updates &&
    a.mem_updates == b.mem_updates &&
    a.heap_updates == b.heap_updates;
}

/* operator != (const Schedule &, const Schedule &) ***************************/
bool operator != (const Schedule & a, const Schedule & b)
{
  return !(a == b);
}
