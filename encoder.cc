#include "encoder.hh"

//==============================================================================
// using declarations
//==============================================================================

using std::string;
using std::ostringstream;

//==============================================================================
// Encoder
//==============================================================================

//------------------------------------------------------------------------------
// static members
//------------------------------------------------------------------------------

const string Encoder::accu_sym          = "accu";
const string Encoder::mem_sym           = "mem";
const string Encoder::sb_adr_sym        = "sb-adr";
const string Encoder::sb_val_sym        = "sb-val";
const string Encoder::sb_full_sym       = "sb-full";
const string Encoder::stmt_sym          = "stmt";
const string Encoder::block_sym         = "block";

const string Encoder::heap_sym          = "heap";
const string Encoder::exit_flag_sym     = "exit";
const string Encoder::exit_code_sym     = "exit-code";

const string Encoder::thread_sym        = "thread";
const string Encoder::exec_sym          = "exec";
const string Encoder::flush_sym         = "flush";
const string Encoder::check_sym         = "check";

const string Encoder::accu_comment      = "accu variables";
const string Encoder::mem_comment       = "mem variables";
const string Encoder::sb_adr_comment    = "store buffer address variables";
const string Encoder::sb_val_comment    = "store buffer value variables";
const string Encoder::sb_full_comment   = "store buffer full variables";
const string Encoder::stmt_comment      = "statement activation variables";
const string Encoder::block_comment     = "blocking variables";

const string Encoder::heap_comment      = "heap variable";
const string Encoder::exit_flag_comment = "exit flag variable";
const string Encoder::exit_code_comment = "exit code variable";

const string Encoder::thread_comment    = "thread activation variables";
const string Encoder::exec_comment      = "statement execution variables";
const string Encoder::flush_comment     = "store buffer flush variables";
const string Encoder::check_comment     = "checkpoint variables";

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

Encoder::Encoder (const Program::List::ptr & p, bound_t b) :
  programs(p),
  num_threads(p->size()),
  bound(b),
  use_sinz_constraint(num_threads > 4)
{
  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        const Instruction & op = program[pc];

        // collect statements requiring an empty store buffer
        if (op.requires_flush())
          flush_pcs[thread].push_back(pc);

        // collect exit calls
        if (&op.symbol() == &Instruction::Exit::symbol)
          exit_pcs[thread].push_back(pc);
      }

    // collect checkpoints
    for (const auto & [c, pcs] : program.checkpoints)
      {
        auto & lst = check_pcs[c][thread];

        lst.reserve(lst.size() + pcs.size());
        lst.insert(lst.end(), pcs.begin(), pcs.end());
      }
  });
}

//------------------------------------------------------------------------------
// public member functions
//------------------------------------------------------------------------------

// Encode::str -----------------------------------------------------------------

string Encoder::str () { return formula.str(); }

//------------------------------------------------------------------------------
// DEBUG
//------------------------------------------------------------------------------

string Encoder::predecessors_to_string ()
{
  ostringstream ss;

  for (word_t tid = 0; tid < programs->size(); tid++)
    for (const auto & [_pc, _predecessors] : (*programs)[tid].predecessors)
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
