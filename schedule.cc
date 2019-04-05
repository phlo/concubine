#include "schedule.hh"

#include <sstream>

#include "parser.hh"

using namespace std;

/* default constructor ********************************************************/
Schedule::Schedule () :
  path(""),
  bound(0),
  programs(new ProgramList()),
  exit(0)
{}

Schedule::Schedule (ProgramListPtr _programs) :
  path(""),
  bound(0),
  programs(_programs),
  exit(0)
{
  /* initialize thread state update lists */
  init_state_update_lists();
}

/* construct from file ********************************************************/
Schedule::Schedule(istream & file, string & name) :
  path(name),
  programs(new ProgramList()),
  exit(0)
{
  string token;

  unsigned long line_num = 1;

  /* parse programs */
  for (string line_buf; getline(file, line_buf); line_num++)
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
  for (string line_buf; getline(file, line_buf); line_num++)
    {
      string cmd;
      word tid, pc, arg, accu, mem;

      /* skip empty lines */
      if (line_buf.empty())
        continue;

      istringstream line(line_buf);

      /* skip comments */
      if (line_buf[line_buf.find_first_not_of(" \t")] == '#')
        continue;

      /* parse thread id */
      if (!(line >> tid))
        {
          line.clear();
          line >> token;
          parser_error(path, line_num, "illegal thread id [" + token + "]");
        }

      if (tid >= programs->size())
          parser_error(
            path,
            line_num,
            "unknown thread id [" + to_string(tid) + "]");

      /* parse pc */
      if (!(line >> pc))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing program counter");

          try
            {
              pc = programs->at(tid)->get_pc(token);
            }
          catch (...)
            {
              parser_error(path, line_num, "unknown label [" + token + "]");
            }
        }

      if (pc >= programs->at(tid)->size())
          parser_error(
            path,
            line_num,
            "illegal program counter [" + to_string(pc) + "]");

      /* parse instruction symbol */
      if (!(line >> cmd))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing instruction symbol");

          parser_error(path, line_num, "unable to parse instruction symbol");
        }

      if (!Instruction::Set::contains(cmd))
        parser_error(path, line_num, "unknown instruction [" + cmd + "]");

      /* parse instruction argument */
      if (!(line >> arg))
        {
          line.clear();

          if (!(line >> token))
            parser_error(path, line_num, "missing instruction argument");

          if (!dynamic_pointer_cast<Jmp>(programs->at(tid)->at(pc)))
              parser_error(
                path,
                line_num,
                programs->at(tid)->at(pc)->get_symbol() +
                " does not support labels");

          try
            {
              arg = programs->at(tid)->get_pc(token);
            }
          catch (...)
            {
              parser_error(
                path,
                line_num,
                "unknown label [" + token + "]");
            }
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

      /* parse heap cell */
      if (!(line >> token))
        parser_error(path, line_num, "missing heap update");

      optional<pair<word, word>> heap;

      string cell = token.substr(1, token.size() - 2);

      if (!cell.empty())
        try
          {
            cell = cell.substr(1, cell.size() - 2);
            size_t split = cell.find(',');
            word idx = stoul(cell.substr(0, split));
            word val = stoul(cell.substr(split + 1));

            /* heap cell update */
            heap = make_pair(idx, val);
          }
        catch (const exception & e)
          {
            parser_error(path, line_num, "illegal heap update [" + token + "]");
          }

      /* append state update */
      push_back(tid, pc, accu, mem, heap);
    }

  /* set bound */
  bound = scheduled.size();

  if (!bound)
    parser_error(path, line_num, "empty schedule");
}

void Schedule::init_state_update_lists ()
{
  size_t num_threads = programs->size();

  /* append pc states */
  pc_updates.resize(num_threads);

  /* append accu states */
  accu_updates.resize(num_threads);

  /* append mem states */
  mem_updates.resize(num_threads);
}

void Schedule::push_back (
                          const unsigned long tid,
                          const word pc,
                          const word accu,
                          const word mem,
                          const optional<pair<word, word>> heap
                         )
{
  /* append thread id */
  scheduled.push_back(tid);

  unsigned long step = scheduled.size();

  /* append pc state update */
  vector<pair<unsigned long, word>> * updates = &pc_updates[tid];
  if (updates->empty() || updates->back().second != pc)
    updates->push_back(make_pair(step, pc));

  /* append accu state update */
  updates = &accu_updates[tid];
  if (updates->empty() || updates->back().second != accu)
    updates->push_back(make_pair(step, accu));

  /* append mem state update */
  updates = &mem_updates[tid];
  if (updates->empty() || updates->back().second != mem)
    updates->push_back(make_pair(step, mem));

  /* append heap state update */
  if (heap)
    {
      updates = &heap_updates[heap->first];
      if (updates->empty() || updates->back().second != heap->second)
        updates->push_back(make_pair(step, heap->second));
    }
}

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

  for (iterator step = begin(); step != end(); ++step)
    {
      /* reference to program */
      const Program & program = *programs->at(step->pc);

      /* reference to the current instruction */
      UnaryInstructionPtr cmd =
        dynamic_pointer_cast<UnaryInstruction>(
          program.at(step->pc));

      /* thread id */
      ss << step->thread << sep;

      /* program counter */
      try
        {
          ss << program.get_label(step->pc) << sep;
        }
      catch (...)
        {
          ss << step->pc << sep;
        }

      /* instruction symbol */
      ss << cmd->get_symbol() << sep;

      /* instruction argument */
      try
        {
          if (dynamic_pointer_cast<Jmp>(cmd))
            ss << program.get_label(cmd->arg) << sep;
          else
            throw runtime_error("");
        }
      catch (...)
        {
          ss << cmd->arg << sep;
        }

      /* accumulator / CAS memory register */
      ss << step->accu << sep << step->mem << sep;

      /* heap update */
      ss << '{';

      if (step->heap)
        ss << step->heap->first + ',' + step->heap->second;

      ss << '}' << eol;
    }

  return ss.str();
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

/* Schedule::iterator (Schedule *, unsigned long) *****************************/
Schedule::iterator::iterator (Schedule * _schedule, unsigned long _step) :
  schedule(_schedule),
  step(_step)
{
  if (step > schedule->bound)
    return;

  size_t num_threads = schedule->programs->size();

  /* initialize scheduled thread id iterator */
  cur_thread = schedule->scheduled.begin();

  /* initialize state update iterators */
  cur_pc.reserve(num_threads);
  for (const auto & updates : schedule->pc_updates)
    cur_pc.push_back(make_pair(updates.begin(), updates.end()));

  cur_accu.reserve(num_threads);
  for (const auto & updates : schedule->accu_updates)
    cur_accu.push_back(make_pair(updates.begin(), updates.end()));

  cur_mem.reserve(num_threads);
  for (const auto & updates : schedule->mem_updates)
    cur_mem.push_back(make_pair(updates.begin(), updates.end()));

  cur_heap.reserve(schedule->heap_updates.size());
  for (const auto & [idx, updates] : schedule->heap_updates)
    cur_heap[idx] = make_pair(updates.begin(), updates.cend());

  /* advance to first step */
  advance();
}

/* Schedule::iterator::get_thread_state (void) ********************************/
word Schedule::iterator::get_thread_state (update_pair_t & state)
{
  update_it_t next = state.first + 1;

  while (next != state.second && next->first <= step)
    state.first = next++;

  return state.first->second;
}

/* Schedule::iterator::get_heap_state (void) **********************************/
optional<pair<word, word>> Schedule::iterator::get_heap_state ()
{
  if (
      StorePtr store =
        dynamic_pointer_cast<Store>(
          schedule->programs->at(update.thread)->at(update.pc))
     )
    {
      word idx =
        store->indirect
          ? schedule->heap_updates[store->arg].back().second
          : store->arg;

      update_pair_t & heap = cur_heap[idx];

      if (heap.first->first == step)
        return make_optional(make_pair(idx, heap.first++->second));
    }

  return {};
}

/* Schedule::iterator::advance (void) *****************************************/
void Schedule::iterator::advance ()
{
  if (step > schedule->bound)
    return;

  word tid = *cur_thread++;

  update.thread = tid;
  update.pc   = get_thread_state(cur_pc[tid]);
  update.accu = get_thread_state(cur_accu[tid]);
  update.mem  = get_thread_state(cur_mem[tid]);
  update.heap = get_heap_state();
}

/* Schedule::iterator::operator ++ (void) - prefix ****************************/
Schedule::iterator & Schedule::iterator::operator ++ ()
{
  advance();
  step++;
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
bool Schedule::iterator::operator == (const iterator & other)
{
  return schedule == other.schedule && step == other.step;
}

/* Schedule::iterator::operator != (const Schedule::iterator &) ***************/
bool Schedule::iterator::operator != (const iterator & other)
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
