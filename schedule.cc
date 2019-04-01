#include "schedule.hh"

#include <sstream>

#include "parser.hh"

using namespace std;

/* default constructor ********************************************************/
Schedule::Schedule () :
  vector<word>(),
  path(""),
  bound(0),
  programs(new ProgramList()),
  exit(0),
  pc_updates(),
  accu_updates(),
  mem_updates(),
  heap_updates()
{}

Schedule::Schedule (ProgramListPtr _programs) :
  vector<word>(),
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
  vector<word>(),
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
  unsigned long step = 1;
  for (string line_buf; getline(file, line_buf); line_num++)
    {
      string cmd, heap;
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

      /* append thread state update */
      push_back(step, tid, pc, accu, mem);

      if (!(line >> token))
        parser_error(path, line_num, "missing heap update");

      heap = token.substr(1, token.size() - 2);
      if (!heap.empty())
        try
          {
            heap = heap.substr(1, heap.size() - 2);
            size_t split = heap.find(',');
            word idx = stoul(heap.substr(0, split));
            word val = stoul(heap.substr(split + 1));

            /* append heap state update */
            push_back(step, idx, val);
          }
        catch (const exception & e)
          {
            parser_error(path, line_num, "illegal heap update [" + token + "]");
          }

      step++;
    }

  /* set bound */
  bound = size();

  if (!bound)
    parser_error(path, line_num, "empty schedule");
}

void Schedule::init_state_update_lists ()
{
  size_t num_threads = programs->size();

  /* append pc states */
  pc_updates.resize(num_threads);
  for (auto & updates : pc_updates)
    updates.push_back(make_pair(0, 0));

  /* append accu states */
  accu_updates.resize(num_threads);
  for (auto & updates : accu_updates)
    updates.push_back(make_pair(0, 0));

  /* append mem states */
  mem_updates.resize(num_threads);
  for (auto & updates : mem_updates)
    updates.push_back(make_pair(0, 0));
}

void Schedule::push_back (
                          const unsigned long step,
                          const unsigned long tid,
                          const word pc,
                          const word accu,
                          const word mem
                         )
{
  if (step != size() + 1)
    throw runtime_error("illegal step [" + to_string(step) + "]");

  /* append thread id */
  vector<word>::push_back(tid);

  /* append pc state update */
  vector<pair<unsigned long, word>> * updates = &pc_updates[tid];
  if (updates->back().second != pc)
    updates->push_back(make_pair(step, pc));

  /* append accu state update */
  updates = &accu_updates[tid];
  if (updates->back().second != accu)
    updates->push_back(make_pair(step, accu));

  /* append mem state update */
  updates = &mem_updates[tid];
  if (updates->back().second != mem)
    updates->push_back(make_pair(step, mem));
}

void Schedule::push_back (
                          const unsigned long step,
                          const word idx,
                          const word val
                         )
{
  auto & updates = heap_updates[idx];
  if (updates.empty() || updates.back().second != val)
    updates.push_back(make_pair(step, val));
}

std::string Schedule::print ()
{
  ostringstream ss;

  /* schedule metadata */
  for (const ProgramPtr & program : *programs)
    ss << program->path << eol;

  /* separator */
  ss << '.' << eol;

  /* column headers */
  ss << "# tid\tpc\tcmd\targ\taccu\tmem\theap" << eol;

  unsigned long num_threads = programs->size();

  /* initialize thread state update iterators */
  typedef vector<pair<unsigned long, word>>::const_iterator update_it_t;

  vector<pair<update_it_t, update_it_t>> pcs;
  pcs.reserve(num_threads);
  for (const auto & v : pc_updates)
    pcs.push_back(make_pair(v.begin(), v.end()));

  vector<pair<update_it_t, const update_it_t>> accus;
  accus.reserve(num_threads);
  for (const auto & v : accu_updates)
    accus.push_back(make_pair(v.begin(), v.end()));

  vector<pair<update_it_t, const update_it_t>> mems;
  mems.reserve(num_threads);
  for (const auto & v : mem_updates)
    mems.push_back(make_pair(v.begin(), v.end()));

  /* references to the heap update iterators of a given index */
  unordered_map<word, pair<update_it_t, update_it_t>> heaps;
  heaps.reserve(heap_updates.size());
  for (const auto & [idx, updates] : heap_updates)
    heaps[idx] = make_pair(updates.begin(), updates.cend());

  /* print schedule data */
  for (size_t step = 1; step <= bound; step++)
    {
      char sep = '\t';

      unsigned long tid = at(step - 1);

      /* references to thread state update iterators */
      auto & pc_it = pcs[tid];
      auto & accu_it = accus[tid];
      auto & mem_it = mems[tid];

      /* reference to program */
      const Program & program = *programs->at(tid);

      // cout << "# step = " << step << " #################################" << eol;
      // cout << "thread = " << tid << eol;

      /* thread id */
      ss << tid << sep;

      /* program counter */
      auto next_pc_it = pc_it.first + 1;
      if (next_pc_it != pc_it.second && next_pc_it->first <= step)
        pc_it.first = next_pc_it;

      string pc = to_string(pc_it.first->second);
      try { pc = program.get_label(pc_it.first->second); } catch (...) {}

      ss << pc << sep;

      // cout << "pc->first == " << pc_it.first->first << eol;
      // if (pc_it.first->first == step)
        // cout << "advancing pc iterator" << eol;

      /* instruction pointer */
      const auto cmd =
        dynamic_pointer_cast<UnaryInstruction>(
          program.at(pc_it.first->second));

      /* instruction symbol */
      ss << cmd->get_symbol() << sep;

      /* instruction argument */
      string arg = to_string(cmd->arg);

      if (dynamic_pointer_cast<Jmp>(cmd))
        try { arg = program.get_label(cmd->arg); } catch (...) {}

      ss << arg << sep;

      /* accumulator */
      auto next_accu_it = accu_it.first + 1;
      if (next_accu_it != accu_it.second && next_accu_it->first <= step)
        accu_it.first = next_accu_it;

      ss << accu_it.first->second << sep;

      // cout << "accu->first == " << accu_it.first->first << eol;
      // if (accu_it.first->first == step)
        // cout << "advancing accu iterator" << eol;

      /* CAS memory register */
      auto next_mem_it = mem_it.first + 1;
      if (next_mem_it != mem_it.second && next_mem_it->first <= step)
        mem_it.first = next_mem_it;

      ss << mem_it.first->second << sep;

      // cout << "mem->first == " << mem_it.first->first << eol;
      // if (mem_it.first->first == step)
        // cout << "advancing mem iterator" << eol;

      /* heap state update */
      ss << "{";
      if (StorePtr s = dynamic_pointer_cast<Store>(cmd))
        {
          word idx = s->indirect ? heap_updates[s->arg].back().second : s->arg;

          /* reference to the heap update iterator for the current index */
          auto & heap_it = heaps[idx];

          if (heap_it.first->first == step)
            {
              ss << "(" << idx << "," << heap_it.first->second << ")";
              heap_it.first++;
            }
        }
      ss << "}" << eol;
    }

  return ss.str();
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

  typedef const vector<word> * pointer;

  if (*dynamic_cast<pointer>(&a) != *dynamic_cast<pointer>(&b))
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
