#include "encoder.hh"

#include "smtlib.hh"

using namespace std;

SMTLibEncoderFunctional::SMTLibEncoderFunctional (
                                                  const Program_list_ptr p,
                                                  bound_t b,
                                                  bool e
                                                 ) : SMTLibEncoder(p, b)
{
  /* initialize state update maps */
  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        const Instruction::Type type = program[pc]->type();

        if (type & Instruction::Types::accu)
          alters_accu[thread].push_back(pc);

        if (type & Instruction::Types::mem)
          alters_mem[thread].push_back(pc);

        if (type & Instruction::Types::write)
          alters_heap[thread].push_back(pc);
      }
  });

  if (e) encode();
}

void SMTLibEncoderFunctional::add_statement_activation ()
{
  if (verbose)
    formula << smtlib::comment_subsection("statement activation");

  declare_stmt_vars();

  if (step == 1)
    add_initial_statement_activation();
  else
    iterate_programs([this] (const Program & program) {
      for (pc = 0; pc < program.size(); pc++)
        {
          /* statement reactivation */
          string expr =
            smtlib::land({
              stmt_var(step - 1, thread, pc),
              smtlib::lnot(exec_var(step - 1, thread, pc))});

          for (word_t prev : program.predecessors.at(pc))
            {
              /* predecessor's execution variable */
              string val = exec_var(step - 1, thread, prev);

              /* build conjunction of execution variable and jump condition */
              if (Jmp_ptr j = dynamic_pointer_cast<Jmp>(program[prev]))
                {
                  string cond = j->encode(*this);

                  /* JMP has no condition and returns an empty string */
                  val = cond.empty()
                    ? val
                    : smtlib::land({
                        val,
                        /* only activate successor if jump condition failed */
                        prev == pc - 1 && j->arg != pc
                          ? smtlib::lnot(cond)
                          : cond
                      });
                }

              /* add predecessor to the activation */
              expr = smtlib::ite(stmt_var(step - 1, thread, prev), val, expr);
            }

          formula << assign_var(stmt_var(), expr) << eol;
        }

      formula << eol;
    });
}

void SMTLibEncoderFunctional::add_state_update ()
{
  if (verbose)
    formula << smtlib::comment_subsection("state update");

  /* accumulator */
  declare_accu_vars();

  update_accu = true;

  iterate_programs([this] (const Program & program) {
    vector<word_t> & pcs = alters_accu[thread];
    string expr = accu_var(step - 1, thread);

    // for (const word_t & _pc : alters_accu[thread])
    for (auto rit = pcs.rbegin(); rit != pcs.rend(); ++rit)
      expr =
        smtlib::ite(
          exec_var(step, thread, *rit),
          program[*rit]->encode(*this),
          expr);

    formula << assign_var(accu_var(), expr) << eol;
  });

  formula << eol;

  update_accu = false;

  /* CAS memory register */
  declare_mem_vars();

  iterate_programs([this] (const Program & program) {
    vector<word_t> & pcs = alters_mem[thread];
    string expr = mem_var(step - 1, thread);

    // for (const word_t & _pc : alters_mem[thread])
    for (auto rit = pcs.rbegin(); rit != pcs.rend(); ++rit)
      expr =
        smtlib::ite(
          exec_var(step, thread, *rit),
          program[*rit]->encode(*this),
          expr);

    formula << assign_var(mem_var(), expr) << eol;
  });

  formula << eol;

  /* heap */
  declare_heap_var();

  string expr = heap_var(step - 1);

  iterate_programs_reverse([this, &expr] (const Program & program) {
    vector<word_t> & pcs = alters_heap[thread];

    // for (const word_t & _pc : alters_heap[thread])
    for (auto rit = pcs.rbegin(); rit != pcs.rend(); ++rit)
      expr =
        smtlib::ite(
          exec_var(step, thread, *rit),
          program[*rit]->encode(*this),
          expr);
  });

  formula << assign_var(heap_var(), expr) << eol;

  formula << eol;
}

void SMTLibEncoderFunctional::add_exit_code ()
{
  if (verbose)
    formula << smtlib::comment_section("exit code");

  declare_exit_code();

  string ite = smtlib::word2hex(0);

  for (bound_t k = step; k > 0; k--)
    iterate_programs_reverse([this, &ite, k] (const Program & program) {
      for (const word_t & exit_pc : exit_pcs[thread])
        ite =
          smtlib::ite(
            exec_var(k, thread, exit_pc),
            program[exit_pc]->encode(*this),
            ite);
    });

  formula << assign_var(exit_code_sym, ite) << eol;
}

void SMTLibEncoderFunctional::encode ()
{
  /* set logic and add common variable declarations */
  SMTLibEncoder::encode();

  for (step = 1; step <= bound; step++)
    {
      if (verbose)
        formula << smtlib::comment_section("step " + to_string(step));

      /* exit flag */
      add_exit_flag();

      /* statement activation */
      add_statement_activation();

      /* thread scheduling */
      add_thread_scheduling();

      /* checkpoint constraints */
      add_checkpoint_constraints();

      /* statement execution */
      add_statement_execution();

      /* state update */
      add_state_update();
    }

  step--;

  /* assign exit code */
  add_exit_code();
}

string SMTLibEncoderFunctional::encode (Load & l)
{
  return load(l);
}

string SMTLibEncoderFunctional::encode (Store & s)
{
  string heap = heap_var(step - 1);

  return
    smtlib::store(
      heap,
      s.indirect
        ? smtlib::select(heap, smtlib::word2hex(s.arg))
        : smtlib::word2hex(s.arg),
      accu_var(step - 1, thread));
}

// TODO
string SMTLibEncoderFunctional::encode (Fence & f [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string SMTLibEncoderFunctional::encode (Add & a)
{
  return smtlib::bvadd({accu_var(step - 1, thread), load(a)});
}

string SMTLibEncoderFunctional::encode (Addi & a)
{
  return smtlib::bvadd({accu_var(step - 1, thread), smtlib::word2hex(a.arg)});
}

string SMTLibEncoderFunctional::encode (Sub & s)
{
  return smtlib::bvsub({accu_var(step - 1, thread), load(s)});
}

string SMTLibEncoderFunctional::encode (Subi & s)
{
  return smtlib::bvsub({accu_var(step - 1, thread), smtlib::word2hex(s.arg)});
}

string SMTLibEncoderFunctional::encode (Cmp & c)
{
  return smtlib::bvsub({accu_var(step - 1, thread), load(c)});
}

string SMTLibEncoderFunctional::encode (Jmp & j [[maybe_unused]])
{
  return "";
}

string SMTLibEncoderFunctional::encode (Jz & j [[maybe_unused]])
{
  return smtlib::equality({accu_var(step - 1, thread), smtlib::word2hex(0)});
}

string SMTLibEncoderFunctional::encode (Jnz & j [[maybe_unused]])
{
  return
    smtlib::lnot(
      smtlib::equality({
        accu_var(step - 1, thread),
        smtlib::word2hex(0)}));
}

string SMTLibEncoderFunctional::encode (Js & j [[maybe_unused]])
{
  return
      smtlib::equality({
        "#b1",
        smtlib::extract(
          to_string(word_size - 1),
          to_string(word_size - 1),
          accu_var(step - 1, thread))});
}

string SMTLibEncoderFunctional::encode (Jns & j [[maybe_unused]])
{
  return
      smtlib::equality({
        "#b0",
        smtlib::extract(
          to_string(word_size - 1),
          to_string(word_size - 1),
          accu_var(step - 1, thread))});
}

string SMTLibEncoderFunctional::encode (Jnzns & j [[maybe_unused]])
{
  return
    smtlib::land({
      smtlib::lnot(
        smtlib::equality({
          accu_var(step - 1, thread),
          smtlib::word2hex(0)})),
      smtlib::equality({
        "#b0",
        smtlib::extract(
          to_string(word_size - 1),
          to_string(word_size - 1),
          accu_var(step - 1, thread))})});
}

string SMTLibEncoderFunctional::encode (Mem & m)
{
  return load(m);
}

string SMTLibEncoderFunctional::encode (Cas & c)
{
  string heap = heap_var(step - 1);

  string addr = c.indirect
    ? smtlib::select(heap_var(step - 1), smtlib::word2hex(c.arg))
    : smtlib::word2hex(c.arg);

  string condition =
    smtlib::equality({
      mem_var(step - 1, thread),
      smtlib::select(heap, addr)});

  return update_accu
    ? smtlib::ite(
        condition,
        smtlib::word2hex(1),
        smtlib::word2hex(0))
    : smtlib::ite(
        condition,
        smtlib::store(
          heap,
          addr,
          accu_var(step - 1, thread)),
        heap);
}

string SMTLibEncoderFunctional::encode (Check & s [[maybe_unused]])
{
  return "";
}

// TODO
string SMTLibEncoderFunctional::encode (Halt & h [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string SMTLibEncoderFunctional::encode (Exit & e)
{
  return smtlib::word2hex(e.arg);
}
