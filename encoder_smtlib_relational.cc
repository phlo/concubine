#include "encoder_smtlib_relational.hh"

#include <cassert>

#include "smtlib.hh"

namespace ConcuBinE::smtlib {

//==============================================================================
// smtlib::Relational
//==============================================================================

//------------------------------------------------------------------------------
// private member functions
//------------------------------------------------------------------------------

// smtlib::Relational::imply ---------------------------------------------------

std::string Relational::imply (const std::string & ante,
                               const std::string & cons) const
{
  return assertion(implication(ante, cons)) + eol;
}

// smtlib::Relational::set_accu ------------------------------------------------

template <class T>
std::shared_ptr<std::string> Relational::set_accu (const T & op)
{
  update = Update::accu;

  return
    std::make_shared<std::string>(
      equality(accu_var(), Encoder::encode(op)));
}

// smtlib::Relational::restore_accu --------------------------------------------

std::shared_ptr<std::string> Relational::restore_accu () const
{
  return
    std::make_shared<std::string>(
      equality(accu_var(), accu_var(prev, thread)));
}

// smtlib::Relational::set_mem -------------------------------------------------

template <class T>
std::shared_ptr<std::string> Relational::set_mem (const T & op)
{
  update = Update::mem;

  return
    std::make_shared<std::string>(
      equality(mem_var(), Encoder::encode(op)));
}

// smtlib::Relational::restore_mem ---------------------------------------------

std::shared_ptr<std::string> Relational::restore_mem () const
{
  return
    std::make_shared<std::string>(
      equality(mem_var(), mem_var(prev, thread)));
}

// smtlib::Relational::set_sb_adr ----------------------------------------------

template <class T>
std::shared_ptr<std::string> Relational::set_sb_adr (const T & op)
{
  update = Update::sb_adr;

  return
    std::make_shared<std::string>(
      equality(sb_adr_var(), Encoder::encode(op)));
}

// smtlib::Relational::restore_sb_adr ------------------------------------------

std::shared_ptr<std::string> Relational::restore_sb_adr () const
{
  return
    std::make_shared<std::string>(
      equality(sb_adr_var(), sb_adr_var(prev, thread)));
}

// smtlib::Relational::set_sb_val ----------------------------------------------

template <class T>
std::shared_ptr<std::string> Relational::set_sb_val (const T & op)
{
  update = Update::sb_val;

  return
    std::make_shared<std::string>(
      equality(sb_val_var(), Encoder::encode(op)));
}

// smtlib::Relational::restore_sb_val ------------------------------------------

std::shared_ptr<std::string> Relational::restore_sb_val () const
{
  return
    std::make_shared<std::string>(
      equality(sb_val_var(), sb_val_var(prev, thread)));
}

// smtlib::Relational::set_sb_full ---------------------------------------------

std::shared_ptr<std::string> Relational::set_sb_full () const
{
  return std::make_shared<std::string>(sb_full_var());
}

// smtlib::Relational::reset_sb_full -------------------------------------------

std::shared_ptr<std::string> Relational::reset_sb_full () const
{
  return
    std::make_shared<std::string>(
      equality(
        sb_full_var(),
        ite(
          flush_var(prev, thread),
          FALSE,
          sb_full_var(prev, thread))));
}

// smtlib::Relational::restor_sb_full ------------------------------------------

std::shared_ptr<std::string> Relational::restore_sb_full () const
{
  return
    std::make_shared<std::string>(
      equality(sb_full_var(), sb_full_var(prev, thread)));
}

// smtlib::Relational::set_stmt ------------------------------------------------

std::shared_ptr<std::string> Relational::set_stmt (const word_t target)
{
  const word_t cur = pc;
  const Program & program = (*programs)[thread];
  std::vector<std::string> stmts;

  stmts.reserve(program.size());

  for (pc = 0; pc < program.size(); pc++)
    stmts.push_back(pc == target ? stmt_var() : lnot(stmt_var()));

  pc = cur;

  return std::make_shared<std::string>(land(stmts));
}

// smtlib::Relational::set_stmt_jmp --------------------------------------------

template <>
std::shared_ptr<std::string>
Relational::set_stmt_jmp (const Instruction::Jmp & j)
{
  return set_stmt(j.arg);
}

template <class T>
std::shared_ptr<std::string> Relational::set_stmt_jmp (const T & op)
{
  const word_t cur = pc;
  const word_t next = pc + 1;
  const Program & program = (*programs)[thread];
  const std::string condition = Encoder::encode(op);
  std::vector<std::string> stmts;

  stmts.reserve(program.size());

  for (pc = 0; pc < program.size(); pc++)
    {
      const std::string stmt = stmt_var();

      if (pc == op.arg)
        stmts.push_back(ite(condition, stmt, lnot(stmt)));
      else if (pc == next)
        stmts.push_back(ite(condition, lnot(stmt), stmt));
      else
        stmts.push_back(lnot(stmt));
    }

  pc = cur;

  return std::make_shared<std::string>(land(stmts));
}

// smtlib::Relational::set_stmt_next -------------------------------------------

std::shared_ptr<std::string> Relational::set_stmt_next ()
{
  return set_stmt(pc + 1);
}

// smtlib::Relational::restore_stmt --------------------------------------------

std::shared_ptr<std::string> Relational::restore_stmt ()
{
  const word_t cur = pc;
  const Program & program = (*programs)[thread];
  std::vector<std::string> stmts;

  stmts.reserve(program.size());

  for (pc = 0; pc < program.size(); pc++)
    stmts.push_back(
      equality(
        stmt_var(step, thread, pc),
        stmt_var(prev, thread, pc)));

  pc = cur;

  return std::make_shared<std::string>(land(stmts));
}

// smtlib::Relational::set_block -----------------------------------------------

template <class T>
std::shared_ptr<std::string> Relational::set_block (const T & op) const
{
  if (checkpoints.empty())
    return {};

  std::vector<std::string> block_vars;

  for (const auto & [c, threads] : checkpoints)
    if (threads.find(thread) != threads.end())
      block_vars.push_back(
        c == op.arg
          ? block_var(step, c, thread)
          : reset_block(c));

  return std::make_shared<std::string>(land(block_vars));
}

// smtlib::Relational::reset_block ---------------------------------------------

std::string Relational::reset_block (const word_t id) const
{
  return
    equality(
      block_var(step, id, thread),
      ite(
        check_var(prev, id),
        FALSE,
        block_var(prev, id, thread)));
}

// smtlib::Relational::restore_block -------------------------------------------

std::shared_ptr<std::string> Relational::restore_block () const
{
  if (checkpoints.empty())
    return {};

  std::vector<std::string> block_vars;

  for (const auto & [c, threads] : checkpoints)
    if (threads.find(thread) != threads.end())
      block_vars.push_back(reset_block(c));

  return std::make_shared<std::string>(land(block_vars));
}

// smtlib::Relational::set_halt ------------------------------------------------

std::shared_ptr<std::string> Relational::set_halt () const
{
  if (halts.empty())
    return {};

  if (num_threads > 1)
    {
      std::vector<std::string> args;

      args.reserve(halts.size());

      for (const auto & it : halts)
        if (thread != it.first)
          args.push_back(halt_var(step, it.first));

      return
        std::make_shared<std::string>(
          land(
            halt_var(),
            ite(
              land(args),
              land(
                exit_flag_var(),
                equality(exit_code_var, word2hex(0))),
              lnot(exit_flag_var()))));
    }
  else
    {
      return
        std::make_shared<std::string>(
          land(
            halt_var(),
            exit_flag_var(),
            equality(exit_code_var, word2hex(0))));
    }
}

// smtlib::Relational::restore_halt --------------------------------------------

std::shared_ptr<std::string> Relational::restore_halt () const
{
  if (halts.empty())
    return {};

  return
    std::make_shared<std::string>(
      equality(halt_var(), halt_var(prev, thread)));
}

// smtlib::Relational::set_heap ------------------------------------------------

template <class T>
std::shared_ptr<std::string> Relational::set_heap (const T & op)
{
  update = Update::heap;

  return
    std::make_shared<std::string>(
      equality(heap_var(), Encoder::encode(op)));
}

// smtlib::Relational::restore_heap --------------------------------------------

std::shared_ptr<std::string> Relational::restore_heap () const
{
  return std::make_shared<std::string>(equality(heap_var(), heap_var(prev)));
}

// smtlib::Relational::set_exit_flag -------------------------------------------

std::shared_ptr<std::string> Relational::set_exit_flag () const
{
  if (halts.empty() && exits.empty())
    return {};

  return std::make_shared<std::string>(exit_flag_var());
}

// smtlib::Relational::unset_exit_flag -----------------------------------------

std::shared_ptr<std::string> Relational::unset_exit_flag () const
{
  if (halts.empty() && exits.empty())
    return {};

  return std::make_shared<std::string>(lnot(exit_flag_var()));
}

// smtlib::Relational::set_exit_code -------------------------------------------

std::shared_ptr<std::string> Relational::set_exit_code (const word_t e) const
{
  return std::make_shared<std::string>(equality(exit_code_var, word2hex(e)));
}

// smtlib::Relational::imply_thread_executed -----------------------------------
//
// thread t executed an instruction (exec_k_t_pc):
// * update thread state accordingly
// * restore heap (or update iff the instruction was a successful CAS)
// * unset exit flag iff the instruction was neither an EXIT, nor a HALT
// * set exit code iff the instruction was an EXIT

void Relational::imply_thread_executed ()
{
  const Program & program = (*programs)[thread];
  const State tmp = state = *this;

  for (pc = 0; pc < program.size(); pc++, state = tmp)
    formula <<
      imply(exec_var(prev, thread, pc), program[pc].encode(*this)) <<
      eol;
}

// smtlib::Relational::imply_thread_not_executed -------------------------------
//
// thread t didn't execute an instruction (not thread_k_t):
// * preserve thread state
// * reset sb-full iff the thread's store buffer has been flushed

void Relational::imply_thread_not_executed ()
{
  state.sb_full = reset_sb_full();
  state.stmt = restore_stmt();
  state.heap = {};
  state.exit_flag = {};

  formula << imply(lnot(thread_var(prev, thread)), state) << eol;
}

// smtlib::Relational::imply_thread_flushed ------------------------------------
//
// thread t flushed its store buffer (flush_k_t):
// * update heap
// * unset exit flag

void Relational::imply_thread_flushed ()
{
  std::vector<std::string> args({
    lnot(sb_full_var()),
    equality(
      heap_var(),
      store(
        heap_var(prev),
        sb_adr_var(prev, thread),
        sb_val_var(prev, thread)))});

  if (!halts.empty() || !exits.empty())
    args.push_back(lnot(exit_flag_var()));

  formula << imply(flush_var(prev, thread), land(args)) << eol;
}

// smtlib::Relational::imply_machine_exited ------------------------------------
//
// machine exited (exit_k):
// * preserve exit flag
// * preserve heap
// * set exit code to zero iff machine never exited (step == bound)

void Relational::imply_machine_exited ()
{
  if (halts.empty() && exits.empty())
    {
      // set exit code for programs running in an infinite loop
      if (step == bound)
        {
          if (verbose)
            formula << comment("exit code") << eol;

          formula << assign(exit_code_var, word2hex(0)) << eol << eol;
        }

      return;
    }

  if (verbose)
    formula << comment("exited") << eol;

  formula <<
    imply(
      exit_flag_var(prev),
      land(
        equality(
          heap_var(),
          heap_var(prev)),
        exit_flag_var())) <<
    eol;

  // set exit if machine didn't exit within bound
  if (step == bound)
    formula <<
      imply(
        lnot(exit_flag_var()),
        equality(
          exit_code_var,
          word2hex(0))) <<
      eol;
}

//------------------------------------------------------------------------------
// private member functions inherited from ConcuBinE::smtlib::Encoder
//------------------------------------------------------------------------------

// smtlib::Relational::define_states -------------------------------------------

void Relational::define_states ()
{
  if (verbose)
    formula << comment_subsection("state variable definitions");

  iterate_threads([this]
    {
      if (verbose)
        formula << comment("thread " + std::to_string(thread)) << eol;

      imply_thread_executed();
      imply_thread_not_executed();
      imply_thread_flushed();
    });

  imply_machine_exited();
}

// smtlib::Relational::encode --------------------------------------------------

std::string Relational::encode (const Instruction::Load & l)
{
  state.accu = set_accu(l);
  state.stmt = set_stmt_next();

  return state;
}

std::string Relational::encode (const Instruction::Store & s)
{
  state.sb_adr = set_sb_adr(s);
  state.sb_val = set_sb_val(s);
  state.sb_full = set_sb_full();
  state.stmt = set_stmt_next();

  return state;
}

std::string Relational::encode (const Instruction::Fence & f [[maybe_unused]])
{
  state.stmt = set_stmt_next();

  return state;
}

std::string Relational::encode (const Instruction::Add & a)
{
  state.accu = set_accu(a);
  state.stmt = set_stmt_next();

  return state;
}

std::string Relational::encode (const Instruction::Addi & a)
{
  state.accu = set_accu(a);
  state.stmt = set_stmt_next();

  return state;
}

std::string Relational::encode (const Instruction::Sub & s)
{
  state.accu = set_accu(s);
  state.stmt = set_stmt_next();

  return state;
}

std::string Relational::encode (const Instruction::Subi & s)
{
  state.accu = set_accu(s);
  state.stmt = set_stmt_next();

  return state;
}

std::string Relational::encode (const Instruction::Mul & m)
{
  state.accu = set_accu(m);
  state.stmt = set_stmt_next();

  return state;
}

std::string Relational::encode (const Instruction::Muli & m)
{
  state.accu = set_accu(m);
  state.stmt = set_stmt_next();

  return state;
}

std::string Relational::encode (const Instruction::Cmp & c)
{
  state.accu = set_accu(c);
  state.stmt = set_stmt_next();

  return state;
}

std::string Relational::encode (const Instruction::Jmp & j)
{
  state.stmt = set_stmt_jmp(j);

  return state;
}

std::string Relational::encode (const Instruction::Jz & j)
{
  state.stmt = set_stmt_jmp(j);

  return state;
}

std::string Relational::encode (const Instruction::Jnz & j)
{
  state.stmt = set_stmt_jmp(j);

  return state;
}

std::string Relational::encode (const Instruction::Js & j)
{
  state.stmt = set_stmt_jmp(j);

  return state;
}

std::string Relational::encode (const Instruction::Jns & j)
{
  state.stmt = set_stmt_jmp(j);

  return state;
}

std::string Relational::encode (const Instruction::Jnzns & j)
{
  state.stmt = set_stmt_jmp(j);

  return state;
}

std::string Relational::encode (const Instruction::Mem & m)
{
  state.accu = set_accu(m);
  state.mem = set_mem(m);
  state.stmt = set_stmt_next();

  return state;
}

std::string Relational::encode (const Instruction::Cas & c)
{
  state.accu = set_accu(c);
  state.stmt = set_stmt_next();
  state.heap = set_heap(c);

  return state;
}

std::string Relational::encode (const Instruction::Check & c)
{
  state.stmt = set_stmt_next();
  state.block = set_block(c);

  return state;
}

std::string Relational::encode (const Instruction::Halt & h [[maybe_unused]])
{
  state.stmt = set_stmt(word_max); // hack: disable all stmt variables
  state.halt = set_halt();
  state.exit_flag = {};

  return state;
}

std::string Relational::encode (const Instruction::Exit & e)
{
  state.stmt = set_stmt(pc);
  state.exit_flag = set_exit_flag();
  state.exit_code = set_exit_code(e.arg);

  return state;
}

//==============================================================================
// smtlib::Relational::State
//==============================================================================

//------------------------------------------------------------------------------
// public constructors
//------------------------------------------------------------------------------

Relational::State::State (Relational & e) :
  accu(e.restore_accu()),
  mem(e.restore_mem()),
  sb_adr(e.restore_sb_adr()),
  sb_val(e.restore_sb_val()),
  sb_full(e.restore_sb_full()),
  block(e.restore_block()),
  halt(e.restore_halt()),
  heap(e.restore_heap()),
  exit_flag(e.unset_exit_flag())
{
  assert(!stmt);
  assert(!exit_code);
}

//------------------------------------------------------------------------------
// public member operators
//------------------------------------------------------------------------------

// conversion ------------------------------------------------------------------

Relational::State::operator std::string () const
{
  std::vector<std::string> args;

  args.reserve(10);

  args.push_back(*accu);
  args.push_back(*mem);
  args.push_back(*sb_adr);
  args.push_back(*sb_val);
  args.push_back(*sb_full);

  if (stmt)
    args.push_back(*stmt);

  if (block)
    args.push_back(*block);

  if (halt)
    args.push_back(*halt);

  if (heap)
    args.push_back(*heap);

  if (exit_flag)
    args.push_back(*exit_flag);

  if (exit_code)
    args.push_back(*exit_code);

  return land(args);
}

} // namespace ConcuBinE::smtlib
