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

template <class T>
string SMTLibEncoderRelational::update_accu (T & op)
{
  update = Update::accu;
  return update_accu(SMTLibEncoder::encode(op));
}

string SMTLibEncoderRelational::update_accu (string expr)
{
  return smtlib::equality({accu_var(), expr});
}

string SMTLibEncoderRelational::preserve_accu ()
{
  return update_accu(accu_var(prev, thread));
}

template <class T>
string SMTLibEncoderRelational::update_mem (T & op)
{
  update = Update::mem;
  return update_mem(SMTLibEncoder::encode(op));
}

string SMTLibEncoderRelational::update_mem (const string expr)
{
  return smtlib::equality({mem_var(), expr});
}

string SMTLibEncoderRelational::preserve_mem ()
{
  return update_mem(mem_var(prev, thread));
}

template <class T>
string SMTLibEncoderRelational::update_sb_adr (T & op)
{
  update = Update::sb_adr;
  return update_sb_adr(SMTLibEncoder::encode(op));
}

string SMTLibEncoderRelational::update_sb_adr (const string expr)
{
  return smtlib::equality({sb_adr_var(), expr});
}

string SMTLibEncoderRelational::preserve_sb_adr ()
{
  return update_sb_adr(sb_adr_var(prev, thread));
}

template <class T>
string SMTLibEncoderRelational::update_sb_val (T & op)
{
  update = Update::sb_val;
  return update_sb_val(SMTLibEncoder::encode(op));
}

string SMTLibEncoderRelational::update_sb_val (const string expr)
{
  return smtlib::equality({sb_val_var(), expr});
}

string SMTLibEncoderRelational::preserve_sb_val ()
{
  return update_sb_val(sb_val_var(prev, thread));
}

string SMTLibEncoderRelational::update_sb_full (const bool val)
{
  return val ? sb_full_var() : smtlib::lnot(sb_full_var());
}

string SMTLibEncoderRelational::preserve_sb_full ()
{
  return
    smtlib::equality({
      sb_full_var(),
      smtlib::ite(
        flush_var(prev, thread),
        smtlib::FALSE,
        sb_full_var(prev, thread))});
}

string SMTLibEncoderRelational::update_stmt ()
{
  const word_t cur = pc;
  const word_t next = pc + 1;
  const Program & program = *(*programs)[thread];
  vector<string> stmts;
  stmts.reserve(program.size());

  for (pc = 0; pc < program.size(); pc++)
    stmts.push_back(pc == next ? stmt_var() : smtlib::lnot(stmt_var()));

  pc = cur; // reset state

  return smtlib::land(stmts);
}

template<>
string SMTLibEncoderRelational::update_stmt (Jmp & j)
{
  const word_t cur = pc;
  const Program & program = *(*programs)[thread];
  vector<string> stmts;
  stmts.reserve(program.size());

  for (pc = 0; pc < program.size(); pc++)
    stmts.push_back(pc == j.arg ? stmt_var() : smtlib::lnot(stmt_var()));

  pc = cur; // reset state

  return smtlib::land(stmts);
}

template <class T>
string SMTLibEncoderRelational::update_stmt (T & op)
{
  const word_t cur = pc;
  const word_t next = pc + 1;
  const Program & program = *(*programs)[thread];
  const string condition = SMTLibEncoder::encode(op);
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

  pc = cur; // reset state

  return smtlib::land(stmts);
}

/*
string SMTLibEncoderRelational::update_stmt (
                                             const word_t target,
                                             const string condition
                                            )
{
  const Program & program = *(*programs)[thread];
  const word_t next = target + 1;
  vector<string> stmts;
  stmts.reserve(program.size());

  for (pc = 0; pc < program.size(); pc++)
    {
      const string stmt = stmt_var();

      if (pc == target)
        stmts.push_back(smtlib::ite(condition, stmt, smtlib::lnot(stmt)));
      else if (pc == next)
        stmts.push_back(smtlib::ite(condition, smtlib::lnot(stmt), stmt));
      else
        stmts.push_back(smtlib::lnot(stmt));
    }

  return smtlib::land(stmts);
}
*/

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

string SMTLibEncoderRelational::update_block (const word_t id)
{
  if (check_pcs.empty())
    return {};

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
  if (check_pcs.empty())
    return {};

  vector<string> block_vars;

  for (const auto & [c, threads] : check_pcs)
    if (threads.find(thread) != threads.end())
      block_vars.push_back(
        smtlib::equality({
          block_var(step, c, thread),
          smtlib::ite(
            check_var(prev, c),
            smtlib::FALSE,
            block_var(prev, c, thread))}));

  return smtlib::land(block_vars);
}

template <class T>
string SMTLibEncoderRelational::update_heap (T & op)
{
  update = Update::heap;
  return update_heap(SMTLibEncoder::encode(op));
}

string SMTLibEncoderRelational::update_heap (const string expr)
{
  return smtlib::equality({heap_var(), expr});
}

string SMTLibEncoderRelational::preserve_heap ()
{
  return update_heap(heap_var(prev));
}

string SMTLibEncoderRelational::set_exit ()
{
  if (exit_pcs.empty())
    return {};

  return exit_var();
}

string SMTLibEncoderRelational::unset_exit ()
{
  if (exit_pcs.empty())
    return {};

  return smtlib::lnot(exit_var());
}

string SMTLibEncoderRelational::set_exit_code (Exit & e)
{
  return smtlib::equality({exit_code_sym, SMTLibEncoder::encode(e)});
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

string SMTLibEncoderRelational::assign_state (initializer_list<string> && args)
{
  return imply(exec_var(prev, thread, pc), smtlib::land(args));
}

string SMTLibEncoderRelational::preserve_state ()
{
  return
    imply(
      smtlib::lnot(thread_var(prev, thread)),
      smtlib::land({
        preserve_accu(),
        preserve_mem(),
        preserve_sb_adr(),
        preserve_sb_val(),
        preserve_sb_full(),
        preserve_stmt(),
        preserve_block()
      }));
}

void SMTLibEncoderRelational::define_states ()
{
  if (verbose)
    formula << smtlib::comment_subsection("state updates");

  iterate_programs([this] (const Program & program) {

    // executed -> update state
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

    // not executed -> preserve state
    formula << preserve_state() << eol;

    // store buffer flush
    formula <<
      imply(
        flush_var(prev, thread),
        smtlib::land({
          smtlib::equality({
            heap_var(),
            smtlib::store(
              heap_var(prev),
              sb_adr_var(prev, thread),
              sb_val_var(prev, thread))
          }),
          smtlib::lnot(exit_var())})) <<
      eol;
  });

  if (exit_pcs.empty())
    return;

  // exited
  formula << imply(exit_var(prev), exit_var()) << eol;

  // exit code
  if (step == bound && !exit_pcs.empty())
    formula <<
      imply(
        smtlib::lnot(exit_var()),
        smtlib::equality({
          exit_code_sym,
          smtlib::word2hex(0)})) <<
      eol;
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
    assign_state({
      update_accu(l),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Store & s)
{
  return
    assign_state({
      preserve_accu(),
      preserve_mem(),
      update_sb_adr(s),
      update_sb_val(s),
      update_sb_full(true),
      update_stmt(),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

// TODO
string SMTLibEncoderRelational::encode (Fence & f [[maybe_unused]])
{
  return
    assign_state({
      preserve_accu(),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Add & a)
{
  return
    assign_state({
      update_accu(a),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Addi & a)
{
  return
    assign_state({
      update_accu(a),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Sub & s)
{
  return
    assign_state({
      update_accu(s),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Subi & s)
{
  return
    assign_state({
      update_accu(s),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Cmp & c)
{
  return
    assign_state({
      update_accu(c),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Jmp & j)
{
  return
    assign_state({
      preserve_accu(),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(j),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Jz & j)
{
  return
    assign_state({
      preserve_accu(),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(j),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Jnz & j)
{
  return
    assign_state({
      preserve_accu(),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(j),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Js & j)
{
  return
    assign_state({
      preserve_accu(),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(j),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Jns & j)
{
  return
    assign_state({
      preserve_accu(),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(j),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Jnzns & j)
{
  return
    assign_state({
      preserve_accu(),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(j),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Mem & m)
{
  return
    assign_state({
      update_accu(m),
      update_mem(m),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Cas & c)
{
  return
    assign_state({
      update_accu(c),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(),
      preserve_block(),
      update_heap(c),
      unset_exit()
    });
}

string SMTLibEncoderRelational::encode (Check & s [[maybe_unused]])
{
  return
    assign_state({
      preserve_accu(),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(),
      preserve_block(),
      preserve_heap(),
      unset_exit()
    });
}

// TODO
string SMTLibEncoderRelational::encode (Halt & h [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string SMTLibEncoderRelational::encode (Exit & e)
{
  return
    assign_state({
      preserve_accu(),
      preserve_mem(),
      preserve_sb_adr(),
      preserve_sb_val(),
      preserve_sb_full(),
      update_stmt(),
      preserve_block(),
      preserve_heap(),
      set_exit(),
      set_exit_code(e)
    });
}
