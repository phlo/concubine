#include "schedule.hh"

#include <sstream>

#include "parser.hh"

using namespace std;

/* default constructor ********************************************************/
Schedule::Schedule () :
  path(""),
  bound(0),
  programs(),
  exit(0),
  threads(),
  pc_updates(),
  accu_updates(),
  mem_updates(),
  heap_updates()
{}

Schedule::Schedule (
                    ProgramListPtr _programs,
                    unsigned long _bound
                   ) :
  path(""),
  bound(_bound),
  programs(_programs),
  exit(0)
{}

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

  /* initialize thread state update vectors */
  size_t num_threads = programs->size();
  pc_updates.resize(num_threads);
  accu_updates.resize(num_threads);
  mem_updates.resize(num_threads);

  /* parse body */
  line_num++;
  unsigned long step = 0;
  for (string line_buf; getline(file, line_buf); line_num++, step++)
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
          parser_error(path, line_num, "unknown thread id [" + token + "]");

      /* parse pc */
      if (!(line >> pc))
        {
          // TODO labels
          line.clear();
          line >> token;
          parser_error(
            path,
            line_num,
            "illegal program counter [" + token + "]");
        }

      /* parse instruction symbol */
      if (!(line >> cmd))
        {
          line.clear();
          line >> token;
          parser_error(path, line_num, "illegal instruction [" + token + "]");
        }

      /* parse instruction argument */
      if (!(line >> arg))
        {
          line.clear();
          line >> token;
          parser_error(
            path,
            line_num,
            "illegal instruction argument [" + token + "]");
        }

      /* parse accu */
      if (!(line >> accu))
        {
          line.clear();
          line >> token;
          parser_error(
            path,
            line_num,
            "illegal accumulator register value [" + token + "]");
        }

      /* parse mem */
      if (!(line >> mem))
        {
          line.clear();
          line >> token;
          parser_error(
            path,
            line_num,
            "illegal CAS memory register value [" + token + "]");
        }

      // if (!(line >> tid >> pc >> cmd >> arg >> accu >> mem >> heap))
        // parser_error(path, line_num, "illegal record");

      push_back(step, tid, pc, accu, mem);

      if (!(line >> heap))
        parser_error(path, line_num, "illegal heap cell");

      cout << "heap = " << heap << eol;
      heap = heap.substr(1, heap.size() - 2);
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
            parser_error(path, line_num, "illegal thread id [" + token + "]");
          }

      /* append thread state update */
      push_back(step, tid, pc, accu, mem);
    }

  /* set bound */
  bound = threads.size();
}

void Schedule::push_back (
                          const unsigned long step,
                          const unsigned long tid,
                          const word pc,
                          const word accu,
                          const word mem
                         )
{
  /* append thread id */
  threads.push_back(tid);

  /* append accu state update */
  auto & updates = pc_updates[tid];
  if (updates.empty() || updates.back().second != pc)
    updates.push_back(make_pair(step, pc));

  /* append accu state update */
  updates = accu_updates[tid];
  if (updates.empty() || updates.back().second != accu)
    updates.push_back(make_pair(step, accu));

  /* append mem state update */
  updates = mem_updates[tid];
  if (updates.empty() || updates.back().second != mem)
    updates.push_back(make_pair(step, mem));
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

  /* column headers */
  ss << "# tid\tpc\tcmd\targ\taccu\tmem\theap" << eol;

  unsigned long num_threads = programs->size();

  /* initialize thread state update iterators */
  vector<vector<pair<unsigned long, word>>::const_iterator> pcs;
  pcs.reserve(num_threads);
  for (const auto & v : pc_updates)
    pcs.push_back(v.begin());

  vector<vector<pair<unsigned long, word>>::const_iterator> accus;
  accus.reserve(num_threads);
  for (const auto & v : accu_updates)
    accus.push_back(v.begin());

  vector<vector<pair<unsigned long, word>>::const_iterator> mems;
  mems.reserve(num_threads);
  for (const auto & v : mem_updates)
    mems.push_back(v.begin());

  /* references to the heap update iterators of a given index */
  unordered_map<word, vector<pair<unsigned long, word>>::const_iterator> heaps;
  heaps.reserve(heap_updates.size());
  for (const auto & [idx, updates] : heap_updates)
    heaps[idx] = updates.begin();

  /* print schedule data */
  for (size_t step = 0; step < bound; step++)
    {
      char sep = '\t';

      unsigned long tid = threads[step];

      /* references to thread state update iterators */
      auto & pc = pcs[tid];
      auto & accu = accus[tid];
      auto & mem = mems[tid];

      /* instruction pointer */
      auto cmd =
        dynamic_pointer_cast<UnaryInstruction>(
          programs->at(tid)->at(pc->second));

      /* thread id */
      ss << tid << sep;

      /* program counter */
      ss << pc->second << sep;

      if (pc->first == step)
        pc++;

      /* instruction symbol */
      ss << cmd->get_symbol() << sep;

      /* instruction argument */
      ss << cmd->arg << sep;

      /* accumulator */
      ss << accu->second << sep;

      if (accu->first == step)
        accu++;

      /* CAS memory register */
      ss << mem->second << sep;

      if (mem->first == step)
        mem++;

      /* heap state update */
      ss << "{";
      if (StorePtr s = dynamic_pointer_cast<Store>(cmd))
        {
          word idx = s->indirect ? heap_updates[s->arg].back().second : s->arg;

          /* reference to the heap update iterator for the current index */
          auto & heap = heaps[idx];

          if (heap->first == step)
            {
              ss << "(" << idx << "," << heap->second << ")";
              heap++;
            }
        }
      ss << "}" << eol;
    }

  return ss.str();
}
