#include "encoder.hh"

#include "smtlib.hh"

using namespace std;

SMTLibEncoderRelational::SMTLibEncoderRelational (
                                                  const Program_list_ptr p,
                                                  bound_t b,
                                                  bool e
                                                 ) : SMTLibEncoder(p, b)
{
  if (e) SMTLibEncoder::encode();
}

string SMTLibEncoderRelational::imply (const string ante, const string cons)
{
  return smtlib::assertion(smtlib::implication(ante, cons)) + eol;
}

string SMTLibEncoderRelational::assign_accu (string expr)
{
  return smtlib::equality({accu_var(), expr});
}

string SMTLibEncoderRelational::preserve_accu ()
{
  return assign_accu(accu_var(prev, thread));
}

string SMTLibEncoderRelational::assign_mem (const string expr)
{
  return smtlib::equality({mem_var(), expr});
}

string SMTLibEncoderRelational::preserve_mem ()
{
  return assign_mem(mem_var(prev, thread));
}

string SMTLibEncoderRelational::assign_sb_adr (const string expr)
{
  return smtlib::equality({sb_adr_var(), expr});
}

string SMTLibEncoderRelational::preserve_sb_adr ()
{
  return assign_sb_adr(sb_adr_var(prev, thread));
}

string SMTLibEncoderRelational::assign_sb_val (const string expr)
{
  return smtlib::equality({sb_val_var(), expr});
}

string SMTLibEncoderRelational::preserve_sb_val ()
{
  return assign_sb_val(sb_val_var(prev, thread));
}

string SMTLibEncoderRelational::assign_sb_full (const bool val)
{
  return val ? sb_full_var() : smtlib::lnot(sb_full_var());
}

string SMTLibEncoderRelational::preserve_sb_full ()
{
  return smtlib::equality({sb_full_var(), sb_full_var(prev, thread)});
}

string SMTLibEncoderRelational::assign_stmt (const word_t target, const optional<string> condition)
{
  vector<string> stmts;

  const word_t next = target + 1;

  const Program & program = *(*programs)[thread];

  for (pc = 0; pc < program.size(); pc++)
    {
      const string stmt = stmt_var();

      if (condition)
        {
          if (pc == target)
            stmts.push_back(smtlib::ite(*condition, stmt, smtlib::lnot(stmt)));
          else if (pc == next)
            stmts.push_back(smtlib::ite(*condition, smtlib::lnot(stmt), stmt));
          else
            stmts.push_back(smtlib::lnot(stmt));
        }
      else
        {
          if (pc == target)
            stmts.push_back(stmt);
          else
            stmts.push_back(smtlib::lnot(stmt));
        }

      stmts.push_back(
        pc == target
          ? condition
            ? smtlib::ite(*condition, stmt_var(), smtlib::lnot(stmt_var()))
            : stmt_var()
          : smtlib::lnot(stmt_var()));
    }

  return smtlib::land(stmts);
}

string SMTLibEncoderRelational::preserve_stmt ()
{
  const Program & program = *(*programs)[thread];

  vector<string> stmts;
  stmts.reserve(program.size());

  for (pc = 0; pc < program.size(); pc++)
    stmts.push_back(
      smtlib::equality({
        stmt_var(step, thread, pc),
        stmt_var(prev, thread, pc)}));

  return smtlib::land(stmts);
}

string SMTLibEncoderRelational::assign_block (const word_t id)
{
  vector<string> block_vars;

  for (const auto & [c, threads] : check_pcs)
    if (threads.find(thread) != threads.end())
      block_vars.push_back(
        c == id
          ? block_var(step, id, thread)
          : smtlib::equality({
              block_var(step, id, thread),
              block_var(prev, id, thread)}));

  return smtlib::land(block_vars);
}

string SMTLibEncoderRelational::preserve_block ()
{
  ostringstream expr;

  vector<string> block_vars;

  for (const auto & [c, threads] : check_pcs)
    if (threads.find(thread) != threads.end())
      block_vars.push_back(
        smtlib::equality({
          block_var(step, c, thread),
          block_var(prev, c, thread)}));

  return smtlib::land(block_vars);

  /*
  for (const auto & [c, threads] : check_pcs)
    for (const auto & [t, pcs] : threads)
      if (step)
        {
          vector<string> block_args;

          block_args.reserve(pcs.size() + 1);

          for (const word_t p : pcs)
            block_args.push_back(exec_var(prev, t, p));

          block_args.push_back(block_var(prev, c, t));

          formula <<
            assign_var(
              block_var(step, c, t),
              smtlib::ite(
                check_var(prev, c),
                "false",
                smtlib::lor(block_args))) <<
            eol;
        }
      else
        {
          formula
            << smtlib::assertion(smtlib::lnot(block_var(step, c, t)))
            << eol;
        }

  formula << eol;
  */
}

string SMTLibEncoderRelational::assign_heap (const string expr)
{
  return smtlib::equality({heap_var(), expr});
}

string SMTLibEncoderRelational::preserve_heap ()
{
  return assign_heap(heap_var(prev));
}

/*
string SMTLibEncoderRelational::preserve_accu ()
{
  return assign(accu_var(), accu_var(prev, thread));
}

string SMTLibEncoderRelational::preserve_mem ()
{
  return assign(mem_var(), mem_var(prev, thread));
}

string SMTLibEncoderRelational::preserve_sb_adr ()
{
  return assign(sb_adr_var(), sb_adr_var(prev, thread));
}

string SMTLibEncoderRelational::preserve_sb_val ()
{
  return assign(sb_val_var(), sb_val_var(prev, thread));
}

string SMTLibEncoderRelational::preserve_sb_full ()
{
  return assign(sb_full_var(), sb_full_var(prev, thread));
}

string SMTLibEncoderRelational::preserve_block ()
{
  ostringstream expr;

  return assign(sb_full_var(), sb_full_var(prev, thread));

  for (const auto & [c, threads] : check_pcs)
    for (const auto & [t, pcs] : threads)
      if (step)
        {
          vector<string> block_args;

          block_args.reserve(pcs.size() + 1);

          for (const word_t p : pcs)
            block_args.push_back(exec_var(prev, t, p));

          block_args.push_back(block_var(prev, c, t));

          expr <<
            assign(
              block_var(step, c, t),
              smtlib::ite(
                check_var(prev, c),
                "false",
                smtlib::lor(block_args))) <<
            eol;
        }
      else
        {
          formula
            << smtlib::assertion(smtlib::lnot(block_var(step, c, t)))
            << eol;
        }

  formula << eol;

  return expr.str();
}

string SMTLibEncoderRelational::stmt_activation (word_t target)
{
  vector<string> args;

  for (word_t cur = 0; cur < programs->at(thread)->size(); cur++)
    args.push_back(
      cur == target
        ? stmt_var(step + 1, thread, target)
        : smtlib::lnot(stmt_var(step + 1, thread, cur)));

  return smtlib::land(args);
}

string SMTLibEncoderRelational::activate_pc (word_t target)
{
  return step < bound ? imply(exec_var(), stmt_activation(target)) : "";
}

string SMTLibEncoderRelational::activate_next ()
{
  return step < bound ? activate_pc(pc + 1) : "";
}

string SMTLibEncoderRelational::activate_jmp (string condition, word_t target)
{
  return step < bound
    ? imply(
        exec_var(),
        smtlib::ite(
          condition,
          stmt_activation(target),
          stmt_activation(pc + 1)))
    : "";
}

string SMTLibEncoderRelational::preserve_heap ()
{
  return
    imply(
      exec_var(),
      smtlib::equality({heap_var(), heap_var(step - 1)}));
}
*/

string SMTLibEncoderRelational::imply_state (
                                             string antecedent,
                                             string accu,
                                             string mem,
                                             string sb_adr,
                                             string sb_val,
                                             string sb_full,
                                             string stmt,
                                             string block,
                                             string heap,
                                             string exit,
                                             string exit_code
                                            )
{
  return
    imply(
      antecedent,
      smtlib::land({
        accu,
        mem,
        sb_adr,
        sb_val,
        sb_full,
        stmt,
        block,
        heap,
        exit,
        exit_code
      }));
}

void SMTLibEncoderRelational::define_states ()
{
  if (verbose)
    formula << smtlib::comment_subsection("state updates");

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula
        << (verbose
          ? "; thread " +
            to_string(thread) +
            "@" +
            to_string(pc) +
            ": " +
            program.print(false, pc) +
            eol
          : "")
        << program[pc]->encode(*this)
        << eol;
  });
}

/*
void SMTLibEncoderRelational::add_exit_code ()
{
  if (verbose)
    formula << smtlib::comment_section("exit code");

  formula <<
    (exit_pcs.empty()
      ? assign_var(exit_code_sym, smtlib::word2hex(0)) + eol
      : imply(
          smtlib::lnot(exit_var()),
          smtlib::equality({exit_code_sym, smtlib::word2hex(0)})));
}

void SMTLibEncoderRelational::add_statement_declaration ()
{
  if (step >= bound)
    return;

  if (verbose)
    formula
      << smtlib::comment_subsection("statement activation forward declaration");

  step++;

  declare_stmt_vars();

  if (step == 1)
    add_initial_statement_activation();

  step--;
}

void SMTLibEncoderRelational::add_state_updates ()
{
  if (verbose)
    formula << smtlib::comment_subsection("state updates");

  declare_accu_vars();
  declare_mem_vars();
  declare_heap_var();

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula
        << (verbose
          ? "; thread " +
            to_string(thread) +
            "@" +
            to_string(pc) +
            ": " +
            program.print(false, pc) +
            eol
          : "")
        << program[pc]->encode(*this)
        << eol;
  });
}

void SMTLibEncoderRelational::add_state_preservation ()
{
  if (verbose)
    formula << smtlib::comment_subsection("state preservation");

  iterate_programs([this] (const Program & program) {

    // define waiting variable
    string preserve = "preserve_" + to_string(step) + "_" + to_string(thread);

    // waiting condition - thread not scheduled
    formula
      << smtlib::declare_bool_var(preserve) << eol
      << assign_var(preserve, smtlib::lnot(thread_var())) << eol
      << eol;

    // preserver accu
    formula <<
      imply(
        preserve,
        smtlib::equality({accu_var(), accu_var(step - 1, thread)}));

    // preserve CAS memory register
    formula <<
      imply(
        preserve,
        smtlib::equality({mem_var(), mem_var(step - 1, thread)}));

    // preserver statement activation
    if (step < bound)
      {
        formula << eol;

        for (pc = 0; pc < program.size(); pc++)
          formula <<
            imply(
              preserve,
              smtlib::equality({stmt_var(step + 1, thread, pc), stmt_var()}));
      }

    formula << eol;
  });
}

void SMTLibEncoderRelational::encode ()
{
  // set logic and add common variable declarations
  SMTLibEncoder::encode();

  // declare exit code variable
  if (verbose)
    formula << "; exit code" << eol;

  declare_exit_code();

  // declare 1st step's statement activation variables
  add_statement_declaration();

  for (step = 1; step <= bound; step++)
    {
      if (verbose)
        formula << smtlib::comment_section("step " + to_string(step));

      // exit flag
      add_exit_flag();

      // thread scheduling
      add_thread_scheduling();

      // checkpoint constraints
      add_checkpoint_constraints();

      // statement execution
      add_statement_execution();

      // add forward declaration of statement activation variables
      add_statement_declaration();

      // encode instructions
      add_state_updates();

      // preserve thread's state if it wasn't executed
      add_state_preservation();
    }

  step--;

  // ensure exit code assignment
  add_exit_code();
}
*/

string SMTLibEncoderRelational::encode (Load & l)
{
  return
    imply_state(
      exec_var(),
      assign_accu(SMTLibEncoder::encode(l)),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      assign_stmt(pc + 1),
      preserve_block(),
      preserve_heap(),
      preserve_exit(),
      preserve_exit_code());
}

string SMTLibEncoderRelational::encode (Store & s)
{
  /*
  string addr(
    s.indirect
      ? smtlib::select(heap_var(step - 1), smtlib::word2hex(s.arg))
      : smtlib::word2hex(s.arg));

  return
    preserve_accu() +
    preserve_mem() +
    assign_heap(
      smtlib::store(
        heap_var(step - 1),
        addr,
        accu_var(step - 1, thread))) +
    activate_next();
  */

  string adr = smtlib::word2hex(s.arg);

  if (s.indirect)
    adr = smtlib::select(heap_var(prev), adr);

  return
    imply_state(
      exec_var(),
      preserve_accu(),
      preserve_mem(),
      assign_sb_adr((update = Update::sb_adr, SMTLibEncoder::encode(s))),
      assign_sb_val((update = Update::sb_val, SMTLibEncoder::encode(s))),
      assign_sb_full(true),
      assign_stmt(pc + 1),
      preserve_block(),
      preserve_heap(),
      preserve_exit(),
      preserve_exit_code());
}

// TODO
string SMTLibEncoderRelational::encode (Fence & f [[maybe_unused]])
{
  return
    imply_state(
      exec_var(),
      preserve_accu(),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      assign_stmt(pc + 1),
      preserve_block(),
      preserve_heap(),
      preserve_exit(),
      preserve_exit_code());
}

string SMTLibEncoderRelational::encode (Add & a)
{
  return
    imply_state(
      exec_var(),
      assign_accu(
        smtlib::bvadd({
          accu_var(prev, thread), load(a.arg, a.indirect)})),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      assign_stmt(pc + 1),
      preserve_block(),
      preserve_heap(),
      preserve_exit(),
      preserve_exit_code());
}

string SMTLibEncoderRelational::encode (Addi & a)
{
  return
    imply_state(
      exec_var(),
      assign_accu(
        smtlib::bvadd({accu_var(prev, thread), smtlib::word2hex(a.arg)})),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      assign_stmt(pc + 1),
      preserve_block(),
      preserve_heap(),
      preserve_exit(),
      preserve_exit_code());
}

string SMTLibEncoderRelational::encode (Sub & s)
{
  return
    assign_accu(
      smtlib::bvsub({accu_var(step - 1, thread), load(s.arg, s.indirect)})) +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Subi & s)
{
  return
    assign_accu(
      smtlib::bvsub({accu_var(step - 1, thread), smtlib::word2hex(s.arg)})) +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Cmp & c)
{
  return
    assign_accu(
      smtlib::bvsub({accu_var(step - 1, thread), load(c.arg, c.indirect)})) +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Jmp & j)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_pc(j.arg);
}

string SMTLibEncoderRelational::encode (Jz & j)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_jmp(
      smtlib::equality({accu_var(), smtlib::word2hex(0)}),
      j.arg);
}

string SMTLibEncoderRelational::encode (Jnz & j)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_jmp(
      smtlib::lnot(smtlib::equality({accu_var(), smtlib::word2hex(0)})),
      j.arg);
}

string SMTLibEncoderRelational::encode (Js & j)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_jmp(
      smtlib::equality({
        "#b1",
        smtlib::extract(
          to_string(word_size - 1),
          to_string(word_size - 1),
          accu_var())}),
      j.arg);
}

string SMTLibEncoderRelational::encode (Jns & j)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_jmp(
      smtlib::equality({
        "#b0",
        smtlib::extract(
          to_string(word_size - 1),
          to_string(word_size - 1),
          accu_var())}),
      j.arg);
}

string SMTLibEncoderRelational::encode (Jnzns & j)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_jmp(
      smtlib::land({
        smtlib::lnot(smtlib::equality({accu_var(), smtlib::word2hex(0)})),
        smtlib::equality({
          "#b0",
          smtlib::extract(
            to_string(word_size - 1),
            to_string(word_size - 1),
            accu_var())})}),
      j.arg);
}

string SMTLibEncoderRelational::encode (Mem & m)
{
  return
    assign_accu(load(m.arg, m.indirect)) +
    assign_mem(accu_var()) +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Cas & c)
{
  string heap = heap_var(step - 1);

  string addr = c.indirect
    ? smtlib::select(heap_var(step - 1), smtlib::word2hex(c.arg))
    : smtlib::word2hex(c.arg);

  string condition =
    smtlib::equality({
      mem_var(step - 1, thread),
      smtlib::select(heap, addr)});

  return
    assign_accu(
      smtlib::ite(
        condition,
        smtlib::word2hex(1),
        smtlib::word2hex(0))) +
    preserve_mem() +
    assign_heap(
      smtlib::ite(
        condition,
        smtlib::store(
          heap,
          addr,
          accu_var(step - 1, thread)),
        heap)) +
    activate_next();
}

string SMTLibEncoderRelational::encode (Check & s [[maybe_unused]])
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

// TODO
string SMTLibEncoderRelational::encode (Halt & h [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string SMTLibEncoderRelational::encode (Exit & e)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    imply(
      exec_var(),
      smtlib::equality({exit_code_sym, smtlib::word2hex(e.arg)}));
}
