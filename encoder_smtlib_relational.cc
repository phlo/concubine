#include "encoder.hh"

#include <cassert>

#include "smtlib.hh"

using namespace std;

SMTLib_Encoder_Relational::State::State (SMTLib_Encoder_Relational & e) :
  accu(e.restore_accu()),
  mem(e.restore_mem()),
  sb_adr(e.restore_sb_adr()),
  sb_val(e.restore_sb_val()),
  sb_full(e.restore_sb_full()),
  block(e.restore_block()),
  heap(e.restore_heap()),
  exit_flag(e.unset_exit_flag())
{
  assert(!stmt);
  assert(!exit_code);
}

SMTLib_Encoder_Relational::State::operator string () const
{
  vector<string> args;

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

  if (heap)
    args.push_back(*heap);

  if (exit_flag)
    args.push_back(*exit_flag);

  if (exit_code)
    args.push_back(*exit_code);

  return smtlib::land(args);
}

SMTLib_Encoder_Relational::SMTLib_Encoder_Relational (
                                                  const Program_list_ptr p,
                                                  bound_t b,
                                                  bool e
                                                 ) : SMTLib_Encoder(p, b)
{
  if (e) SMTLib_Encoder::encode();
}

string SMTLib_Encoder_Relational::imply (const string a, const string c) const
{
  return smtlib::assertion(smtlib::implication(a, c)) + eol;
}

template <class T>
shared_ptr<string> SMTLib_Encoder_Relational::set_accu (T & op)
{
  update = Update::accu;

  return
    make_shared<string>(
      smtlib::equality({accu_var(), SMTLib_Encoder::encode(op)}));
}

shared_ptr<string> SMTLib_Encoder_Relational::restore_accu () const
{
  return
    make_shared<string>(
      smtlib::equality({accu_var(), accu_var(prev, thread)}));
}

template <class T>
shared_ptr<string> SMTLib_Encoder_Relational::set_mem (T & op)
{
  update = Update::mem;

  return
    make_shared<string>(
      smtlib::equality({mem_var(), SMTLib_Encoder::encode(op)}));
}

shared_ptr<string> SMTLib_Encoder_Relational::restore_mem () const
{
  return
    make_shared<string>(
      smtlib::equality({mem_var(), mem_var(prev, thread)}));
}

template <class T>
shared_ptr<string> SMTLib_Encoder_Relational::set_sb_adr (T & op)
{
  update = Update::sb_adr;

  return
    make_shared<string>(
      smtlib::equality({sb_adr_var(), SMTLib_Encoder::encode(op)}));
}

shared_ptr<string> SMTLib_Encoder_Relational::restore_sb_adr () const
{
  return
    make_shared<string>(
      smtlib::equality({sb_adr_var(), sb_adr_var(prev, thread)}));
}

template <class T>
shared_ptr<string> SMTLib_Encoder_Relational::set_sb_val (T & op)
{
  update = Update::sb_val;

  return
    make_shared<string>(
      smtlib::equality({sb_val_var(), SMTLib_Encoder::encode(op)}));
}

shared_ptr<string> SMTLib_Encoder_Relational::restore_sb_val () const
{
  return
    make_shared<string>(
      smtlib::equality({sb_val_var(), sb_val_var(prev, thread)}));
}

shared_ptr<string> SMTLib_Encoder_Relational::set_sb_full () const
{
  return make_shared<string>(sb_full_var());
}

shared_ptr<string> SMTLib_Encoder_Relational::reset_sb_full () const
{
  return
    make_shared<string>(
      smtlib::equality({
        sb_full_var(),
        smtlib::ite(
          flush_var(prev, thread),
          smtlib::FALSE,
          sb_full_var(prev, thread))}));
}

shared_ptr<string> SMTLib_Encoder_Relational::restore_sb_full () const
{
  return
    make_shared<string>(
      smtlib::equality({sb_full_var(), sb_full_var(prev, thread)}));
}

shared_ptr<string> SMTLib_Encoder_Relational::set_stmt (const word_t target)
{
  const word_t cur = pc;
  const Program & program = *(*programs)[thread];
  vector<string> stmts;

  stmts.reserve(program.size());

  for (pc = 0; pc < program.size(); pc++)
    stmts.push_back(pc == target ? stmt_var() : smtlib::lnot(stmt_var()));

  pc = cur;

  return make_shared<string>(smtlib::land(stmts));
}

shared_ptr<string> SMTLib_Encoder_Relational::set_stmt_next ()
{
  return set_stmt(pc + 1);
}

template <>
shared_ptr<string> SMTLib_Encoder_Relational::set_stmt (Jmp & j)
{
  return set_stmt(j.arg);
}

template <class T>
shared_ptr<string> SMTLib_Encoder_Relational::set_stmt (T & op)
{
  const word_t cur = pc;
  const word_t next = pc + 1;
  const Program & program = *(*programs)[thread];
  const string condition = SMTLib_Encoder::encode(op);
  vector<string> stmts;

  stmts.reserve(program.size());

  for (pc = 0; pc < program.size(); pc++)
    {
      const string stmt = stmt_var();

      if (pc == op.arg)
        stmts.push_back(smtlib::ite(condition, stmt, smtlib::lnot(stmt)));
      else if (pc == next)
        stmts.push_back(smtlib::ite(condition, smtlib::lnot(stmt), stmt));
      else
        stmts.push_back(smtlib::lnot(stmt));
    }

  pc = cur;

  return make_shared<string>(smtlib::land(stmts));
}

shared_ptr<string> SMTLib_Encoder_Relational::restore_stmt ()
{
  const word_t cur = pc;
  const Program & program = *(*programs)[thread];
  vector<string> stmts;

  stmts.reserve(program.size());

  for (pc = 0; pc < program.size(); pc++)
    stmts.push_back(
      smtlib::equality({
        stmt_var(step, thread, pc),
        stmt_var(prev, thread, pc)}));

  pc = cur;

  return make_shared<string>(smtlib::land(stmts));
}

string SMTLib_Encoder_Relational::reset_block (const word_t id) const
{
  return
    smtlib::equality({
      block_var(step, id, thread),
      smtlib::ite(
        check_var(prev, id),
        smtlib::FALSE,
        block_var(prev, id, thread))});
}

template <class T>
shared_ptr<string> SMTLib_Encoder_Relational::set_block (T & op) const
{
  if (check_pcs.empty())
    return {};

  vector<string> block_vars;

  for (const auto & [c, threads] : check_pcs)
    if (threads.find(thread) != threads.end())
      block_vars.push_back(
        c == op.arg
          ? block_var(step, c, thread)
          : reset_block(c));

  return make_shared<string>(smtlib::land(block_vars));
}

shared_ptr<string> SMTLib_Encoder_Relational::restore_block () const
{
  if (check_pcs.empty())
    return {};

  vector<string> block_vars;

  for (const auto & [c, threads] : check_pcs)
    if (threads.find(thread) != threads.end())
      block_vars.push_back(reset_block(c));

  return make_shared<string>(smtlib::land(block_vars));
}

template <class T>
shared_ptr<string> SMTLib_Encoder_Relational::set_heap (T & op)
{
  update = Update::heap;

  return
    make_shared<string>(
      smtlib::equality({heap_var(), SMTLib_Encoder::encode(op)}));
}

shared_ptr<string> SMTLib_Encoder_Relational::restore_heap () const
{
  return
    make_shared<string>(
      smtlib::equality({heap_var(), heap_var(prev)}));
}

shared_ptr<string> SMTLib_Encoder_Relational::set_exit_flag () const
{
  if (exit_pcs.empty())
    return {};

  return make_shared<string>(exit_flag_var());
}

shared_ptr<string> SMTLib_Encoder_Relational::unset_exit_flag () const
{
  if (exit_pcs.empty())
    return {};

  return make_shared<string>(smtlib::lnot(exit_flag_var()));
}

shared_ptr<string>
SMTLib_Encoder_Relational::set_exit_code (const word_t e) const
{
  return
    make_shared<string>(
      smtlib::equality({exit_code_sym, smtlib::word2hex(e)}));
}

// thread t executed an instruction (exec_k_t_pc):
// * update thread state accordingly
// * restore heap (or update iff the instruction was a successful CAS)
// * unset exit flag
// * set exit code iff the instruction was an EXIT
void SMTLib_Encoder_Relational::imply_thread_executed ()
{
  const Program & program = *(*programs)[thread];
  const State tmp = state = *this;

  for (pc = 0; pc < program.size(); pc++, state = tmp)
    formula
      << imply(exec_var(prev, thread, pc), program[pc]->encode(*this))
      << eol;
}

// thread t didn't execute an instruction (not thread_k_t):
// * preserve thread state
// * reset sb-full iff the thread's store buffer has been flushed
void SMTLib_Encoder_Relational::imply_thread_not_executed ()
{
  state.sb_full = reset_sb_full();
  state.stmt = restore_stmt();
  state.heap = {};
  state.exit_flag = {};

  formula << imply(smtlib::lnot(thread_var(prev, thread)), state) << eol;
}

// thread t flushed its store buffer (flush_k_t):
// * update heap
// * unset exit flag
void SMTLib_Encoder_Relational::imply_thread_flushed ()
{
  vector<string> args {
    smtlib::lnot(sb_full_var()),
    smtlib::equality({
      heap_var(),
      smtlib::store(
        heap_var(prev),
        sb_adr_var(prev, thread),
        sb_val_var(prev, thread))})};

  if (!exit_pcs.empty())
    args.push_back(smtlib::lnot(exit_flag_var()));

  formula << imply(flush_var(prev, thread), smtlib::land(args)) << eol;
}

// machine exited (exit_k):
// * preserve exit flag
// * preserve heap
// * set exit code to zero iff machine never exited (step == bound)
void SMTLib_Encoder_Relational::imply_machine_exited ()
{
  if (exit_pcs.empty())
    return;

  if (verbose)
    formula << smtlib::comment("exited") << eol;

  formula <<
    imply(
      exit_flag_var(prev),
      smtlib::land({
        smtlib::equality({
          heap_var(),
          heap_var(prev)}),
        exit_flag_var()})) <<
    eol;

  if (step == bound)
    formula <<
      imply(
        smtlib::lnot(exit_flag_var()),
        smtlib::equality({
          exit_code_sym,
          smtlib::word2hex(0)})) <<
      eol;
}

void SMTLib_Encoder_Relational::define_states ()
{
  if (verbose)
    formula << smtlib::comment_subsection("state variable definitions");

  iterate_threads([this]
    {
      if (verbose)
        formula << smtlib::comment("thread " + to_string(thread)) << eol;

      imply_thread_executed();
      imply_thread_not_executed();
      imply_thread_flushed();
    });

  imply_machine_exited();
}

string SMTLib_Encoder_Relational::encode (Load & l)
{
  state.accu = set_accu(l);
  state.stmt = set_stmt_next();

  return state;
}

string SMTLib_Encoder_Relational::encode (Store & s)
{
  state.sb_adr = set_sb_adr(s);
  state.sb_val = set_sb_val(s);
  state.sb_full = set_sb_full();
  state.stmt = set_stmt_next();

  return state;
}

// TODO
string SMTLib_Encoder_Relational::encode (Fence & f [[maybe_unused]])
{
  state.stmt = set_stmt_next();

  return state;
}

string SMTLib_Encoder_Relational::encode (Add & a)
{
  state.accu = set_accu(a);
  state.stmt = set_stmt_next();

  return state;
}

string SMTLib_Encoder_Relational::encode (Addi & a)
{
  state.accu = set_accu(a);
  state.stmt = set_stmt_next();

  return state;
}

string SMTLib_Encoder_Relational::encode (Sub & s)
{
  state.accu = set_accu(s);
  state.stmt = set_stmt_next();

  return state;
}

string SMTLib_Encoder_Relational::encode (Subi & s)
{
  state.accu = set_accu(s);
  state.stmt = set_stmt_next();

  return state;
}

string SMTLib_Encoder_Relational::encode (Mul & m)
{
  state.accu = set_accu(m);
  state.stmt = set_stmt_next();

  return state;
}

string SMTLib_Encoder_Relational::encode (Muli & m)
{
  state.accu = set_accu(m);
  state.stmt = set_stmt_next();

  return state;
}

string SMTLib_Encoder_Relational::encode (Cmp & c)
{
  state.accu = set_accu(c);
  state.stmt = set_stmt_next();

  return state;
}

string SMTLib_Encoder_Relational::encode (Jmp & j)
{
  state.stmt = set_stmt(j);

  return state;
}

string SMTLib_Encoder_Relational::encode (Jz & j)
{
  state.stmt = set_stmt(j);

  return state;
}

string SMTLib_Encoder_Relational::encode (Jnz & j)
{
  state.stmt = set_stmt(j);

  return state;
}

string SMTLib_Encoder_Relational::encode (Js & j)
{
  state.stmt = set_stmt(j);

  return state;
}

string SMTLib_Encoder_Relational::encode (Jns & j)
{
  state.stmt = set_stmt(j);

  return state;
}

string SMTLib_Encoder_Relational::encode (Jnzns & j)
{
  state.stmt = set_stmt(j);

  return state;
}

string SMTLib_Encoder_Relational::encode (Mem & m)
{
  state.accu = set_accu(m);
  state.mem = set_mem(m);
  state.stmt = set_stmt_next();

  return state;
}

string SMTLib_Encoder_Relational::encode (Cas & c)
{
  state.accu = set_accu(c);
  state.stmt = set_stmt_next();
  state.heap = set_heap(c);

  return state;
}

string SMTLib_Encoder_Relational::encode (Check & c)
{
  state.stmt = set_stmt_next();
  state.block = set_block(c);

  return state;
}

// TODO
string SMTLib_Encoder_Relational::encode (Halt & h [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string SMTLib_Encoder_Relational::encode (Exit & e)
{
  state.stmt = set_stmt(pc);
  state.exit_flag = set_exit_flag();
  state.exit_code = set_exit_code(e.arg);

  return state;
}
