#include "encoder.hh"

using namespace std;

const string Encoder::accu_sym      = "accu";
const string Encoder::mem_sym       = "mem";

const string Encoder::sb_adr_sym    = "sb-adr";
const string Encoder::sb_val_sym    = "sb-val";
const string Encoder::sb_full_sym   = "sb-full";

const string Encoder::heap_sym      = "heap";
const string Encoder::exit_code_sym = "exit-code";

const string Encoder::thread_sym    = "thread";
const string Encoder::flush_sym     = "flush";
const string Encoder::stmt_sym      = "stmt";
const string Encoder::exec_sym      = "exec";
const string Encoder::cas_sym       = "cas";
const string Encoder::block_sym     = "block";
const string Encoder::check_sym     = "check";
const string Encoder::exit_sym      = "exit";

Encoder::Encoder (const Program_list_ptr p, bound_t b) :
  programs(p),
  num_threads(p->size()),
  bound(b),
  use_sinz_constraint(num_threads > 4)
{
  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        const Instruction_ptr & op = program[pc];

        /* collect statements requiring an empty store buffer */
        if (op->requires_flush())
          flush_pcs[thread].insert(pc);

        /* collect CHECK statemets */
        if (Check_ptr s = dynamic_pointer_cast<Check>(op))
          check_pcs[s->arg][thread].insert(pc);

        /* collect exit calls */
        if (Exit_ptr e = dynamic_pointer_cast<Exit>(op))
          exit_pcs[thread].push_back(pc);

        /* collect CAS statemets */
        if (Cas_ptr c = dynamic_pointer_cast<Cas>(op))
          cas_threads.insert(thread);
      }
  });
}

string Encoder::str () { return formula.str(); }

/* DEBUG **********************************************************************/
string Encoder::predecessors_to_string ()
{
  ostringstream ss;

  for (word_t tid = 0; tid < programs->size(); tid++)
    for (const auto & [_pc, _predecessors] : programs->at(tid)->predecessors)
      {
        ss << "thread " << tid << " @ " << _pc << " :";
        for (const auto & prev : _predecessors)
          ss << " " << prev;
        ss << eol;
      }

  return ss.str();
}

string Encoder::check_pcs_to_string ()
{
  ostringstream ss;

  for (const auto & [id, threads] : check_pcs)
    {
      ss << "check " << id << ": " << eol;
      for (const auto & [_thread, pcs] : threads)
        {
          ss << "  " << _thread << ":";
          for (const auto & _pc : pcs)
            ss << " " << _pc;
          ss << eol;
        }
    }

  return ss.str();
}

string Encoder::exit_pcs_to_string ()
{
  ostringstream ss;

  for (const auto & [_thread, pcs] : exit_pcs)
    {
      ss << "thread " << _thread << ":";
      for (const auto & _pc : pcs)
        ss << ' ' << _pc;
      ss << eol;
    }

  return ss.str();
}
