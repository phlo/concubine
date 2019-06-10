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

string SMTLibEncoderRelational::imply (string antecedent, string consequent)
{
  return smtlib::assertion(smtlib::implication(antecedent, consequent)) + eol;
}

string SMTLibEncoderRelational::assign_heap (string exp)
{
  return imply(exec_var(), smtlib::equality({heap_var(), exp}));
}

string SMTLibEncoderRelational::assign_accu (string val)
{
  return imply(exec_var(), smtlib::equality({accu_var(), val}));
}

string SMTLibEncoderRelational::assign_mem (string val)
{
  return imply(exec_var(), smtlib::equality({mem_var(), val}));
}

string SMTLibEncoderRelational::preserve_heap ()
{
  return
    imply(
      exec_var(),
      smtlib::equality({heap_var(), heap_var(step - 1)}));
}

string SMTLibEncoderRelational::preserve_accu ()
{
  return
    imply(
      exec_var(),
      smtlib::equality({accu_var(), accu_var(step - 1, thread)}));
}

string SMTLibEncoderRelational::preserve_mem ()
{
  return
    imply(
      exec_var(),
      smtlib::equality({mem_var(), mem_var(step - 1, thread)}));
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
    assign_accu(load(l.arg, l.indirect)) +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Store & s)
{
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
}

// TODO
string SMTLibEncoderRelational::encode (Fence & f [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string SMTLibEncoderRelational::encode (Add & a)
{
  return
    assign_accu(
      smtlib::bvadd({accu_var(step - 1, thread), load(a.arg, a.indirect)})) +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Addi & a)
{
  return
    assign_accu(
      smtlib::bvadd({accu_var(step - 1, thread), smtlib::word2hex(a.arg)})) +
    preserve_mem() +
    preserve_heap() +
    activate_next();
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
