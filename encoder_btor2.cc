#include "encoder.hh"

#include <functional>

#include "btor2.hh"

using namespace std;

/* map lookup helper, performing an arbitrary action for missing values */
template <class K, class V, class F>
V & lookup (Encoder::Map<K, V> & m, K k, F fun)
{
  /* avoid extra lookups https://stackoverflow.com/a/101980 */
  auto it = m.find(k);

  return it != m.end()
    ? it->second
    : m.insert(it, {k, fun()})->second;
}

string Btor2_Encoder::msb = to_string(word_size - 1);

Btor2_Encoder::Btor2_Encoder (const Program_list_ptr p, bound_t b, bool e) :
  Encoder(p, b), node(1)
{
  /* collect constants */
  nids_const[0] = "";
  nids_const[bound] = "";

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        const Instruction_ptr & op = program[pc];

        /* collect constants */
        if (Unary_ptr i = dynamic_pointer_cast<Unary>(op))
          nids_const[i->arg] = "";

        /* initialize state update maps */
        const Instruction::Type type = op->type();

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

string Btor2_Encoder::nid ()
{
  return to_string(node++);
}

string Btor2_Encoder::nid (int offset)
{
  return to_string(static_cast<int>(node) + offset);
}

string Btor2_Encoder::debug_symbol (word_t p)
{
  Unary & op = *dynamic_pointer_cast<Unary>(programs->at(thread)->at(p));

  return
    to_string(thread) +
    ":" +
    to_string(p) +
    ":" +
    op.symbol() +
    ":" +
    to_string(op.arg);
}

string Btor2_Encoder::accu_var (const word_t t)
{
  return accu_sym + '_' + to_string(t);
}

string Btor2_Encoder::accu_var () const
{
  return accu_var(thread);
}

string Btor2_Encoder::mem_var (const word_t t)
{
  return mem_sym + '_' + to_string(t);
}

string Btor2_Encoder::mem_var () const
{
  return mem_var(thread);
}

string Btor2_Encoder::stmt_var (const word_t t, const word_t pc)
{
  return stmt_sym + '_' + to_string(t) + '_' + to_string(pc);
}

string Btor2_Encoder::stmt_var () const
{
  return stmt_var(thread, pc);
}

string Btor2_Encoder::thread_var (const word_t t)
{
  return thread_sym + '_' + to_string(t);
}

string Btor2_Encoder::thread_var () const
{
  return thread_var(thread);
}

string Btor2_Encoder::exec_var (const word_t t, const word_t pc)
{
  return exec_sym + '_' + to_string(t) + '_' + to_string(pc);
}

string Btor2_Encoder::exec_var () const
{
  return exec_var(thread, pc);
}

string Btor2_Encoder::cas_var (const word_t t)
{
  return cas_sym + '_' + to_string(t);
}

string Btor2_Encoder::cas_var () const
{
  return cas_var(thread);
}

string Btor2_Encoder::block_var (const word_t t, const word_t id)
{
  return block_sym + '_' + to_string(t) + '_' + to_string(id);
}

string Btor2_Encoder::check_var (const word_t id)
{
  return check_sym + '_' + to_string(id);
}

void Btor2_Encoder::declare_heap ()
{
  if (verbose)
    formula << btor2::comment(heap_sym) << eol;

  formula << btor2::state(nid_heap = nid(), sid_heap, heap_sym) << eol;
}

void Btor2_Encoder::declare_accu ()
{
  if (verbose)
    formula
      << btor2::comment("accumulator registers - " + accu_sym + "_<thread>")
      << eol;

  iterate_threads([this] {
    formula << btor2::state(nids_accu[thread] = nid(), sid_bv, accu_var());
  });

  formula << eol;
}

void Btor2_Encoder::declare_mem ()
{
  if (verbose)
    formula
      << btor2::comment("CAS memory registers - " + mem_sym + "_<thread>")
      << eol;

  iterate_threads([this] {
    formula << btor2::state(nids_mem[thread] = nid(), sid_bv, mem_var());
  });

  formula << eol;
}

void Btor2_Encoder::declare_stmt ()
{
  if (verbose)
    formula <<
      btor2::comment(
        "statement activation flags - " + stmt_sym + "_<thread>_<pc>") <<
      eol;

  iterate_programs([this] (const Program & program) {
    nids_stmt[thread].reserve(program.size());

    for (pc = 0; pc < program.size(); pc++)
      formula <<
        btor2::state(
          nids_stmt[thread].emplace_back(nid()),
          sid_bool,
          stmt_var());

    formula << eol;
  });
}

void Btor2_Encoder::declare_block ()
{
  if (verbose)
    formula <<
      btor2::comment(
        "thread blocking flags - " + block_sym + "_<id>_<thread>") <<
      eol;

  for (const auto & [s, threads] : check_pcs)
    {
      // TODO: ignore single-threaded checkpoints -> see gitlab issue #65
      if (threads.size() > 1)
        {
          auto & nids = nids_block.insert(nids_block.end(), {s, {}})->second;

          for (const auto & t : threads)
            formula <<
              btor2::state(
                nids.emplace_hint(nids.end(), t.first, nid())->second,
                sid_bool,
                block_var(s, t.first));

          formula << eol;
        }
    }
}

void Btor2_Encoder::declare_exit_flag ()
{
  if (verbose)
    formula << btor2::comment(exit_flag_sym + " flag") << eol;

  formula <<
    btor2::state(nid_exit_flag = nid(), sid_bool, exit_flag_sym) <<
    eol;
}

void Btor2_Encoder::declare_exit_code ()
{
  formula << btor2::state(nid_exit_code = nid(), sid_bv, exit_code_sym);
}

void Btor2_Encoder::define_state (
                                 string nid_state,
                                 string sid,
                                 string nid_init,
                                 string sym,
                                 Map<word_t, vector<word_t>> & alters_state,
                                 const bool global
                                )
{
  string nid_next = nid_state;

  /* initialize thread for global state updates */
  if (global)
    thread = 0;

  if (verbose && !global)
    formula << btor2::comment(sym) << eol;

  if (!nid_init.empty())
    formula << btor2::init(nid(), sid, nid_state, nid_init);

  Map<word_t, vector<word_t>>::iterator thread_it;
  do
    if ((thread_it = alters_state.find(thread)) != alters_state.end())
      {
        /* minimize lookups */
        vector<word_t> & pcs = thread_it->second;
        vector<string> & exec = nids_exec[thread];

        vector<word_t>::iterator pc_it = pcs.begin();
        for (pc = *pc_it; pc_it != pcs.end(); ++pc_it, pc = *pc_it)
          {
            Unary & op =
              *dynamic_pointer_cast<Unary>(programs->at(thread)->at(pc));

            formula <<
              btor2::ite(
                nid_next = nid(),
                sid,
                exec[pc],
                op.encode(*this),
                nid_next,
                verbose ? debug_symbol(pc) : "");
          }
      }
  while (global && thread++ < num_threads);

  formula << btor2::next(nid(), sid, nid_state, nid_next, sym) << eol;
}

void Btor2_Encoder::define_accu ()
{
  if (verbose)
    formula << btor2::comment_subsection("accumulator definitions");

  update_accu = true;

  iterate_threads([this] {
    define_state(
      nids_accu[thread],
      sid_bv,
      nids_const[0],
      accu_var(),
      alters_accu);
  });

  update_accu = false;
}

void Btor2_Encoder::define_mem ()
{
  if (verbose)
    formula
      << btor2::comment_subsection("CAS memory register definitions");

  iterate_threads([this] {
    define_state(
      nids_mem[thread],
      sid_bv,
      nids_const[0],
      mem_var(),
      alters_mem);
  });
}

void Btor2_Encoder::define_heap ()
{
  define_state(nid_heap, sid_heap, "", heap_sym, alters_heap, true);
}

void Btor2_Encoder::define_stmt ()
{
  iterate_programs([this] (const Program & program) {

    /* map storing nids of jump conditions */
    Map<Jmp_ptr, string> nid_jmp;

    /* reduce lookups */
    const vector<string> & nids_stmt_thread = nids_stmt[thread];
    const vector<string> & nids_exec_thread = nids_exec[thread];

    for (pc = 0; pc < program.size(); pc++)
      {
        if (verbose)
          formula << btor2::comment(stmt_var()) << eol;

        string nid_next = nid();
        string nid_exec = nids_exec_thread[pc];
        string nid_stmt = nids_stmt_thread[pc];

        /* initialization */
        formula <<
          btor2::init(
            nid_next,
            sid_bool,
            nid_stmt,
            pc ? nid_false : nid_true);

        /* add statement reactivation */
        formula <<
          btor2::land(
            nid_next = nid(),
            sid_bool,
            nid_stmt,
            btor2::lnot(nid_exec));

        /* add activation by predecessor's execution */
        for (word_t prev : program.predecessors.at(pc))
          {
            nid_exec = nids_exec_thread[prev];

            /* predecessor is a jump */
            if (Jmp_ptr j = dynamic_pointer_cast<Jmp>(program[prev]))
              {
                string nid_cond = lookup(nid_jmp, j, [&] () {
                  return j->encode(*this);
                });

                /* nothing to do here for unconditional jumps (JMP) */
                if (!nid_cond.empty())
                  {
                    /* add negated condition if preceding jump failed */
                    if (prev == pc - 1 && j->arg != pc)
                      nid_cond = btor2::lnot(nid_cond);

                    /* add conjunction of execution variable & jump condition */
                    formula <<
                      btor2::land(
                        nid_exec = nid(),
                        sid_bool,
                        nid_exec,
                        nid_cond);
                  }
              }

            /* add predecessors activation */
            formula <<
              btor2::ite(
                nid_next = nid(),
                sid_bool,
                nids_stmt_thread[prev],
                nid_exec,
                nid_next,
                verbose ? debug_symbol(prev) : "");
          }

        formula <<
          btor2::next(
            nid(),
            sid_bool,
            nid_stmt,
            nid_next,
            verbose ? debug_symbol(pc) : "") <<
          eol;
      }
  });
}

void Btor2_Encoder::define_block ()
{
  if (verbose)
    formula << btor2::comment("thread blocking flag definitions") << eol;

  auto nids_check_it = nids_check.begin();
  auto nids_block_it = nids_block.begin();

  for (const auto & [s, threads] : check_pcs)
    {
      // TODO: ignore single-threaded checkpoints -> see gitlab issue #65
      if (threads.size() > 1)
        {
          string & nid_check = nids_check_it++->second;

          auto nid_block_it = nids_block_it++->second.begin();

          for (const auto & [t, pcs] : threads)
            {
              string prev;

              string & nid_block = nid_block_it++->second;

              vector<string> args;
              args.reserve(pcs.size() + 1);
              for (const auto & p : pcs)
                args.push_back(nids_exec[t][p]);
              args.push_back(nid_block);

              formula <<
                btor2::init(nid(), sid_bool, nid_block, nid_false) <<
                btor2::lor(node, sid_bool, args) <<
                btor2::ite(
                  prev = nid(),
                  sid_bool,
                  nid_check,
                  nid_false,
                  nid(-1)) <<
                btor2::next(
                  nid(),
                  sid_bool,
                  nid_block,
                  prev,
                  block_var(s, t)) <<
                eol;
            }
        }
    }
}

void Btor2_Encoder::define_check ()
{
  if (verbose)
    formula <<
      btor2::comment("checkpoint flags - " + check_sym + "_<id>") << eol;

  for (const auto & [s, blocks] : nids_block)
    {
      // TODO: ignore single-threaded checkpoints -> see gitlab issue #65
      if (blocks.size() > 1)
        {
          vector<string> args;

          for (const auto & [t, nid_block] : blocks)
            args.push_back(nid_block);

          formula << btor2::land(node, sid_bool, args, check_var(s));

          nids_check.emplace_hint(nids_check.end(), s, nid(-1));
        }
      else
        {
          nids_check.emplace_hint(nids_check.end(), s, blocks.begin()->second);
        }
    }

  formula << eol;
}

void Btor2_Encoder::define_exit_flag ()
{
  if (verbose)
    formula << btor2::comment("exit flag") << eol;

  formula << btor2::init(nid(), sid_bool, nid_exit_flag, nid_false);

  vector<string> args({nid_exit_flag});

  for (const auto & [t, pcs] : exit_pcs)
    for (const auto & p : pcs)
      args.push_back(nids_exec[t][p]);

  string nid_cond = nid_exit_flag;

  if (args.size() > 1)
    {
      formula << btor2::lor(node, sid_bool, args);
      nid_cond = to_string(node - 1);
    }

  formula
    << btor2::next(nid(), sid_bool, nid_exit_flag, nid_cond, exit_flag_sym)
    << eol;
}

void Btor2_Encoder::define_exit_code ()
{
  if (verbose)
    formula << btor2::comment("exit code") << eol;

  declare_exit_code();

  define_state(
    nid_exit_code,
    sid_bv,
    nids_const[0],
    exit_code_sym,
    exit_pcs,
    true);
}

void Btor2_Encoder::add_sorts ()
{
  if (verbose)
    formula << btor2::comment_section("sorts");

  formula <<
    btor2::declare_sort(sid_bool = nid(), "1") <<
    btor2::declare_sort(sid_bv = nid(), to_string(word_size)) <<
    btor2::declare_array(sid_heap = nid(), "2", "2") <<
    eol;
}

void Btor2_Encoder::add_constants ()
{
  if (verbose)
    formula << btor2::comment_section("constants");

  /* declare boolean constants */
  formula <<
    btor2::constd(nid_false = nid(), sid_bool, "0") <<
    btor2::constd(nid_true = nid(), sid_bool, "1") <<
    eol;

  /* declare bitvector constants */
  for (const auto & c : nids_const)
    formula <<
      btor2::constd(
        nids_const[c.first] = nid(),
        sid_bv,
        to_string(c.first));

  formula << eol;
}

void Btor2_Encoder::add_machine_state_declarations ()
{
  if (verbose)
    formula << btor2::comment_section("machine state declarations");

  declare_heap();
  declare_accu();
  declare_mem();
  declare_stmt();
  declare_exit_flag();
}

void Btor2_Encoder::add_thread_scheduling ()
{
  if (verbose)
    formula << btor2::comment_section("thread scheduling");

  /* declare thread inputs */
  iterate_threads([&] () {
    formula <<
      btor2::input(
        nids_thread[thread] = nid(),
        sid_bool,
        thread_var());
  });

  formula << eol;

  /* cardinality constraint */
  if (verbose)
    formula << btor2::comment("cardinality constraint") << eol;

  vector<string> variables;

  for (const auto & t : nids_thread)
    variables.push_back(t.second);

  variables.push_back(nid_exit_flag);

  formula <<
    (use_sinz_constraint
      ? btor2::card_constraint_sinz(node, sid_bool, variables)
      : btor2::card_constraint_naive(node, sid_bool, variables)) <<
    eol;
}

void Btor2_Encoder::add_statement_execution ()
{
  if (verbose)
    formula <<
      btor2::comment_section(
        "statement execution - " + exec_sym + "_<thread>_<pc>");

  iterate_programs([this] (const Program & program) {

    auto program_size = program.size();

    nids_exec[thread].reserve(program_size);

    for (pc = 0; pc < program_size; pc++)
      formula <<
        btor2::land(
          nids_exec[thread].emplace_back(nid()),
          sid_bool,
          nids_stmt[thread][pc],
          nids_thread[thread],
          exec_var());

    formula << eol;
  });
}

void Btor2_Encoder::add_statement_activation ()
{
  if (verbose)
    formula <<
      btor2::comment_section("statement activation state definitions");

  define_stmt();
}

void Btor2_Encoder::add_register_definitions ()
{
  if (verbose)
    formula << btor2::comment_section("register state definitions");

  define_accu();
  define_mem();
}

void Btor2_Encoder::add_heap_definition ()
{
  if (verbose)
    formula << btor2::comment_section("heap state definition");

  define_heap();
}

void Btor2_Encoder::add_exit_definitions ()
{
  if (verbose)
    formula << btor2::comment_section("exit state definitions");

  define_exit_flag();
  define_exit_code();
}

void Btor2_Encoder::add_checkpoint_constraints ()
{
  /* skip if there is no call to CHECK */
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << btor2::comment_section("checkpoint constraints");

  declare_block();
  define_check();
  define_block();

  if (verbose)
    formula << btor2::comment("prevent scheduling of blocked threads") << eol;

  for (const auto & [s, threads] : nids_block)
    {
      // TODO: ignore single-threaded checkpoints -> see gitlab issue #65
      if (threads.size() > 1)
        {
          string not_check = btor2::lnot(nids_check[s]);

          for (const auto & [t, nid_block] : threads)
            {
              string prev;

              formula <<
                btor2::land(
                  prev = nid(),
                  sid_bool,
                  nid_block,
                  not_check) <<
                btor2::implies(
                  prev = nid(),
                  sid_bool,
                  prev,
                  btor2::lnot(nids_thread[t])) <<
                btor2::constraint(
                  nid(),
                  prev,
                  block_var(s, t)) <<
                eol;
            }
        }
    }
}

void Btor2_Encoder::add_bound ()
{
  if (verbose)
    formula << btor2::comment_section("bound");

  /* step counter */
  if (verbose)
    formula << btor2::comment("step counter") << eol;

  string nid_prev;
  string nid_ctr = nid();

  formula <<
    btor2::state(nid_ctr, sid_bv, "k") <<
    btor2::init(nid(), sid_bv, nid_ctr, nids_const[0]) <<
    btor2::add(nid_prev = nid(), sid_bv, nids_const[1], nid_ctr) <<
    btor2::next(nid(), sid_bv, nid_ctr, nid_prev) <<
    eol;

  /* bound */
  if (verbose)
    formula << btor2::comment("bound (" + to_string(bound) + ")") << eol;

  formula <<
    btor2::eq(nid_prev = nid(), sid_bool, nids_const[bound], nid_ctr) <<
    btor2::bad(nid(), nid_prev);
}

string Btor2_Encoder::add_load (string * nid_idx)
{
  formula << btor2::read(*nid_idx = nid(), sid_bv, nid_heap, *nid_idx);

  return *nid_idx;
}

string Btor2_Encoder::load (Load & l)
{
  string nid_load = nids_const[l.arg];

  auto add_load = bind(&Btor2_Encoder::add_load, this, &nid_load);

  nid_load = lookup(nids_load, l.arg, add_load);

  return l.indirect
    ? lookup(nids_load_indirect, l.arg, add_load)
    : nid_load;
}

/* requires thread to be set */
string Btor2_Encoder::store (Store & s)
{
  string nid_store = nids_const[s.arg];

  if (s.indirect)
    nid_store =
      lookup(
        nids_load,
        s.arg,
        bind(&Btor2_Encoder::add_load, this, &nid_store));

  Map<word_t, string> & nids_thread_store =
    lookup(
      s.indirect
        ? nids_store_indirect
        : nids_store,
      thread,
      [] () { return Map<word_t, string>(); });

  return
    lookup(
      nids_thread_store,
      s.arg,
      [&] () {
        formula <<
          btor2::write(
            nid_store = nid(),
            sid_heap,
            nid_heap,
            nid_store,
            nids_accu[thread]);

        return nid_store;
      });
}

void Btor2_Encoder::encode ()
{
  add_sorts();
  add_constants();
  add_machine_state_declarations();
  add_thread_scheduling();
  add_statement_execution();
  add_statement_activation();
  add_register_definitions();
  add_heap_definition();
  add_exit_definitions();
  add_checkpoint_constraints();
  add_bound();
}

string Btor2_Encoder::encode (Load & l)
{
  return load(l);
}

string Btor2_Encoder::encode (Store & s)
{
  return store(s);
}

// TODO
string Btor2_Encoder::encode (Fence & f [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string Btor2_Encoder::encode (Add & a)
{
  string nid_add = load(a);

  formula << btor2::add(nid_add = nid(), sid_bv, nids_accu[thread], nid_add);

  return nid_add;
}

string Btor2_Encoder::encode (Addi & a)
{
  string nid_addi = nids_const[a.arg];

  formula << btor2::add(nid_addi = nid(), sid_bv, nids_accu[thread], nid_addi);

  return nid_addi;
}

string Btor2_Encoder::encode (Sub & s)
{
  string nid_sub = load(s);

  formula << btor2::sub(nid_sub = nid(), sid_bv, nids_accu[thread], nid_sub);

  return nid_sub;
}

string Btor2_Encoder::encode (Subi & s)
{
  string nid_subi = nids_const[s.arg];

  formula << btor2::sub(nid_subi = nid(), sid_bv, nids_accu[thread], nid_subi);

  return nid_subi;
}

string Btor2_Encoder::encode (Cmp & c)
{
  string nid_sub = load(c);

  formula << btor2::sub(nid_sub = nid(), sid_bv, nids_accu[thread], nid_sub);

  return nid_sub;
}

string Btor2_Encoder::encode (Jmp & j [[maybe_unused]])
{
  return "";
}

string Btor2_Encoder::encode (Jz & j [[maybe_unused]])
{
  string ret = nid();

  formula << btor2::eq(ret, sid_bool, nids_accu[thread], nids_const[0]);

  return ret;
}

string Btor2_Encoder::encode (Jnz & j [[maybe_unused]])
{
  string ret = nid();

  formula << btor2::ne(ret, sid_bool, nids_accu[thread], nids_const[0]);

  return ret;
}

string Btor2_Encoder::encode (Js & j [[maybe_unused]])
{
  string ret = nid();

  formula << btor2::slice(ret, sid_bool, nids_accu[thread], msb, msb);

  return ret;
}

string Btor2_Encoder::encode (Jns & j [[maybe_unused]])
{
  string ret = nid();

  formula <<
    btor2::slice(ret, sid_bool, nids_accu[thread], msb, msb) <<
    btor2::lnot(ret = nid(), sid_bool, ret);

  return ret;
}

string Btor2_Encoder::encode (Jnzns & j [[maybe_unused]])
{
  string nid_nz = nid();

  formula <<
    btor2::ne(nid_nz = nid(), sid_bool, nids_accu[thread], nids_const[0]);

  string nid_nzns = nid();

  formula <<
    btor2::slice(nid_nzns, sid_bool, nids_accu[thread], msb, msb) <<
    btor2::lnot(nid_nzns = nid(), sid_bool, nid_nzns);

  formula <<
    btor2::land(nid_nzns = nid(), sid_bool, nid_nz, nid_nzns);

  return nid_nzns;
}

string Btor2_Encoder::encode (Mem & m)
{
  return load(m);
}

string Btor2_Encoder::encode (Cas & c)
{
  Load l(c.arg, c.indirect);

  string nid_cas = load(l);

  formula << btor2::eq(nid_cas = nid(), sid_bool, nids_mem[thread], nid_cas);

  if (update_accu)
    {
      formula <<
        btor2::ite(
          nid_cas = nid(),
          sid_bv,
          nid_cas,
          nids_const[1],
          nids_const[0]);
    }
  else
    {
      string nid_store = store(c);

      formula <<
        btor2::ite(nid_cas = nid(), sid_heap, nid_cas, nid_store, nid_heap);
    }

  return nid_cas;
}

string Btor2_Encoder::encode (Check & s [[maybe_unused]])
{
  return "";
}

// TODO
string Btor2_Encoder::encode (Halt & h [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string Btor2_Encoder::encode (Exit & e [[maybe_unused]])
{
  return nids_const[e.arg];
}
