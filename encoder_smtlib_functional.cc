#include "encoder.hh"

#include <cassert>

#include "smtlib.hh"

using namespace std;

SMTLibEncoderFunctional::SMTLibEncoderFunctional (
                                                  const Program_list_ptr p,
                                                  bound_t b,
                                                  bool e
                                                 ) : SMTLibEncoder(p, b)
{
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
              stmt_var(prev, thread, pc),
              smtlib::lnot(exec_var(prev, thread, pc))});

          const auto & predecessors = program.predecessors.at(pc);

          for (auto p = predecessors.rbegin(); p != predecessors.rend(); ++p)
            {
              /* predecessor's execution variable */
              string val = exec_var(prev, thread, *p);

              /* build conjunction of execution variable and jump condition */
              if (Jmp_ptr j = dynamic_pointer_cast<Jmp>(program[*p]))
                {
                  string cond = j->encode(*this);

                  /* JMP has no condition and returns an empty string */
                  val = cond.empty()
                    ? val
                    : smtlib::land({
                        val,
                        /* only activate successor if jump condition failed */
                        *p == pc - 1 && j->arg != pc
                          ? smtlib::lnot(cond)
                          : cond
                      });
                }

              /* add predecessor to the activation */
              expr = smtlib::ite(stmt_var(prev, thread, *p), val, expr);
            }

          formula << assign_var(stmt_var(), expr) << eol;
        }

      formula << eol;
    });
}

#include <iostream>
#include <bitset>
void SMTLibEncoderFunctional::add_state_update (const Update u)
{
  Type type;
  string (*var) (word_t, word_t);

  switch (update = u)
    {
    case Update::accu:
      type = Types::accu;
      var = accu_var;
      break;
    case Update::mem:
      type = Types::mem;
      var = mem_var;
      break;
    case Update::sb_adr:
      type = Types::write;
      var = sb_adr_var;
      break;
    case Update::sb_val:
      type = Types::write;
      var = sb_val_var;
      break;
    default:
      throw runtime_error("illegal state update");
    }

  iterate_programs([this, type, var] (const Program & program) {
    string expr = var(prev, thread);
    pc = program.size() - 1;

    for (auto rit = program.rbegin(); rit != program.rend(); ++rit, pc--)
      {
        const Instruction_ptr & op = *rit;

        if (op->type() & type)
          cout
            << "  " << op->symbol()
            << "\t" << bitset<8>(op->type())
            << "\t" << bitset<8>(type)
            << "\t" << bitset<8>(op->type() & type) << eol;

        if (op->type() & type)
          expr =
            smtlib::ite(
              exec_var(step, thread, pc),
              op->encode(*this),
              expr);
      }

    formula << assign_var(var(step, thread), expr) << eol;
  });

  formula << eol;
}

void SMTLibEncoderFunctional::add_accu_update ()
{
  declare_accu_vars();
  cout << accu_sym << eol;
  add_state_update(Update::accu);
}

void SMTLibEncoderFunctional::add_mem_update ()
{
  declare_mem_vars();
  cout << mem_sym << eol;
  add_state_update(Update::mem);
}

void SMTLibEncoderFunctional::add_sb_adr_update ()
{
  declare_sb_adr_vars();
  cout << sb_adr_sym << eol;
  add_state_update(Update::sb_adr);
}

void SMTLibEncoderFunctional::add_sb_val_update ()
{
  declare_sb_val_vars();
  cout << sb_val_sym << eol;
  add_state_update(Update::sb_val);
}

void SMTLibEncoderFunctional::add_sb_full_update ()
{
  declare_sb_full_vars();
  cout << sb_full_sym << eol;

  iterate_programs([this] (const Program & program) {
    vector<string> args {sb_full_var(prev, thread)};
    pc = program.size() - 1;
    for (auto rit = program.rbegin(); rit != program.rend(); ++rit, pc--)
      {
        const Instruction_ptr & op = *rit;

        if (op->type() & Types::write)
          args.push_back(exec_var(step, thread, pc));
      }

    formula <<
      assign_var(
        sb_full_var(),
        step > 1
          ? smtlib::ite(
              flush_var(),
              "false",
              smtlib::lor(args))
          : smtlib::lor(args)) << eol;
  });
  formula << eol;
}

void SMTLibEncoderFunctional::add_heap_update ()
{
  declare_heap_var();
  cout << heap_sym << eol;

  const string heap_prev = heap_var(prev);
  string expr = heap_prev;

  iterate_programs_reverse([this, &heap_prev, &expr] (const Program & program) {
    pc = program.size() - 1;

    for (auto rit = program.rbegin(); rit != program.rend(); ++rit, pc--)
      {
        const Instruction_ptr & op = *rit;

        if (op->type() & Types::atomic)
          cout
            << "  " << op->symbol()
            << "\t" << bitset<8>(op->type())
            << "\t" << bitset<8>(Types::atomic)
            << "\t" << bitset<8>(op->type() & Types::atomic) << eol;

        if (op->type() & Types::atomic)
          expr =
            smtlib::ite(
              exec_var(step, thread, pc),
              op->encode(*this),
              expr);
      }

    if (step > 1)
      expr =
        smtlib::ite(
          flush_var(),
          smtlib::store(
            heap_prev,
            sb_adr_var(prev, thread),
            sb_val_var(prev, thread)),
          expr);
  });

  formula << assign_var(heap_var(), expr) << eol;

  formula << eol;
}

void SMTLibEncoderFunctional::add_state_updates ()
{
  if (verbose)
    formula << smtlib::comment_subsection("state updates");

  add_accu_update();
  add_mem_update();
  add_sb_adr_update();
  add_sb_val_update();
  add_sb_full_update();
  add_heap_update();
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

  for (step = 1, prev = 0; step <= bound; step++, prev++)
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
      add_state_updates();
    }

  step--;

  /* assign exit code */
  add_exit_code();
}

string SMTLibEncoderFunctional::encode (Load & l)
{
  return load(l.arg, l.indirect);
}

string SMTLibEncoderFunctional::encode (Store & s)
{
  switch (update)
    {
    case Update::sb_adr:
      return s.indirect ? load(s.arg) : smtlib::word2hex(s.arg);

    case Update::sb_val:
      return accu_var(prev, thread);

    default:
      throw runtime_error("illegal state update");
    }
}

// TODO
string SMTLibEncoderFunctional::encode (Fence & f [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string SMTLibEncoderFunctional::encode (Add & a)
{
  return smtlib::bvadd({accu_var(prev, thread), load(a.arg, a.indirect)});
}

string SMTLibEncoderFunctional::encode (Addi & a)
{
  return smtlib::bvadd({accu_var(prev, thread), smtlib::word2hex(a.arg)});
}

string SMTLibEncoderFunctional::encode (Sub & s)
{
  return smtlib::bvsub({accu_var(prev, thread), load(s.arg, s.indirect)});
}

string SMTLibEncoderFunctional::encode (Subi & s)
{
  return smtlib::bvsub({accu_var(prev, thread), smtlib::word2hex(s.arg)});
}

string SMTLibEncoderFunctional::encode (Cmp & c)
{
  return smtlib::bvsub({accu_var(prev, thread), load(c.arg, c.indirect)});
}

string SMTLibEncoderFunctional::encode (Jmp & j [[maybe_unused]])
{
  return "";
}

string SMTLibEncoderFunctional::encode (Jz & j [[maybe_unused]])
{
  return smtlib::equality({accu_var(prev, thread), smtlib::word2hex(0)});
}

string SMTLibEncoderFunctional::encode (Jnz & j [[maybe_unused]])
{
  return
    smtlib::lnot(
      smtlib::equality({
        accu_var(prev, thread),
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
          accu_var(prev, thread))});
}

string SMTLibEncoderFunctional::encode (Jns & j [[maybe_unused]])
{
  return
      smtlib::equality({
        "#b0",
        smtlib::extract(
          to_string(word_size - 1),
          to_string(word_size - 1),
          accu_var(prev, thread))});
}

string SMTLibEncoderFunctional::encode (Jnzns & j [[maybe_unused]])
{
  return
    smtlib::land({
      smtlib::lnot(
        smtlib::equality({
          accu_var(prev, thread),
          smtlib::word2hex(0)})),
      smtlib::equality({
        "#b0",
        smtlib::extract(
          to_string(word_size - 1),
          to_string(word_size - 1),
          accu_var(prev, thread))})});
}

string SMTLibEncoderFunctional::encode (Mem & m)
{
  return load(m.arg, m.indirect);
}

string SMTLibEncoderFunctional::encode (Cas & c)
{
  string heap = heap_var(prev);

  string addr = c.indirect
    ? smtlib::select(heap, smtlib::word2hex(c.arg))
    : smtlib::word2hex(c.arg);

  string condition =
    smtlib::equality({
      mem_var(prev, thread),
      smtlib::select(heap, addr)});

  return update == Update::accu
    ? smtlib::ite(
        condition,
        smtlib::word2hex(1),
        smtlib::word2hex(0))
    : smtlib::ite(
        condition,
        smtlib::store(
          heap,
          addr,
          accu_var(prev, thread)),
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
