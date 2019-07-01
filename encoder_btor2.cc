#include "encoder.hh"

#include <algorithm>

#include "btor2.hh"

//==============================================================================
// using declarations
//==============================================================================

using std::string;
using std::to_string;

using std::map;
using std::unordered_map;
using std::vector;

using std::runtime_error;

//==============================================================================
// helpers
//==============================================================================

// map lookup helpers, performing an arbitrary action for missing values -------

template <typename K, typename V, typename F>
V & lookup (map<K, V> & m, K k, F fun)
{
  // avoid extra lookups https://stackoverflow.com/a/101980
  auto lb = m.lower_bound(k);

  return
    lb != m.end() && !(m.key_comp()(k, lb->first))
      ? lb->second
      : m.insert(lb, {k, fun()})->second;
}

template <class K, class V, class F>
V & lookup (unordered_map<K, V> & m, K k, F fun)
{
  auto it = m.find(k);

  return
    it != m.end()
      ? it->second
      : m.insert(it, {k, fun()})->second;
}

//==============================================================================
// Btor2_Encoder
//==============================================================================

//------------------------------------------------------------------------------
// static members
//------------------------------------------------------------------------------

// exit code variable ----------------------------------------------------------

const string & Btor2_Encoder::exit_code_var = exit_code_sym;

// variable comments -----------------------------------------------------------

const string Btor2_Encoder::accu_comment =
  btor2::comment(
    Encoder::accu_comment + " - " + accu_sym + "_<thread>" + eol);

const string Btor2_Encoder::mem_comment =
  btor2::comment(
    Encoder::mem_comment + " - " + mem_sym + "_<thread>" + eol);

const string Btor2_Encoder::sb_adr_comment =
  btor2::comment(
    Encoder::sb_adr_comment + " - " + sb_adr_sym + "_<thread>" + eol);

const string Btor2_Encoder::sb_val_comment =
  btor2::comment(
    Encoder::sb_val_comment + " - " + sb_val_sym + "_<thread>" + eol);

const string Btor2_Encoder::sb_full_comment =
  btor2::comment(
    Encoder::sb_full_comment + " - " + sb_full_sym + "_<thread>" + eol);

const string Btor2_Encoder::stmt_comment =
  btor2::comment(
    Encoder::stmt_comment + " - " + stmt_sym + "_<thread>_<pc>" + eol);

const string Btor2_Encoder::block_comment =
  btor2::comment(
    Encoder::block_comment + " - " + block_sym + "_<id>_<thread>" + eol);

const string Btor2_Encoder::heap_comment =
  btor2::comment(Encoder::heap_comment + eol);

const string Btor2_Encoder::exit_flag_comment =
  btor2::comment(Encoder::exit_flag_comment + eol);

const string Btor2_Encoder::exit_code_comment =
  btor2::comment(Encoder::exit_code_comment + eol);

const string Btor2_Encoder::thread_comment =
  btor2::comment(
    Encoder::thread_comment + " - " + thread_sym + "_<thread>" + eol);

const string Btor2_Encoder::exec_comment =
  btor2::comment(
    Encoder::exec_comment + " - " + exec_sym + "_<thread>_<pc>" + eol);

const string Btor2_Encoder::flush_comment =
  btor2::comment(
    Encoder::flush_comment + " - " + flush_sym + "_<thread>" + eol);

const string Btor2_Encoder::check_comment =
  btor2::comment(
    Encoder::check_comment + " - " + check_sym + "_<id>" + eol);

// most significant bit's bitvector constant -----------------------------------

const string Btor2_Encoder::msb = to_string(word_size - 1);

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

Btor2_Encoder::Btor2_Encoder (const Program::List::ptr & p,
                              const bound_t b,
                              const bool e) :
  Encoder(p, b),
  node(1)
{
  // collect constants
  nids_const[0] = "";
  nids_const[bound] = "";

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      if (program[pc].is_unary())
        nids_const[program[pc].arg()];
  });

  if (e) encode();
}

//------------------------------------------------------------------------------
// private member functions
//------------------------------------------------------------------------------

// Btor2_Encoder::accu_var -----------------------------------------------------

string Btor2_Encoder::accu_var (const word_t t)
{
  return accu_sym + '_' + to_string(t);
}

string Btor2_Encoder::accu_var () const
{
  return accu_var(thread);
}

// Btor2_Encoder::mem_var ------------------------------------------------------

string Btor2_Encoder::mem_var (const word_t t)
{
  return mem_sym + '_' + to_string(t);
}

string Btor2_Encoder::mem_var () const
{
  return mem_var(thread);
}

// Btor2_Encoder::sb_adr_var ---------------------------------------------------

string Btor2_Encoder::sb_adr_var (const word_t t)
{
  return sb_adr_sym + '_' + to_string(t);
}

string Btor2_Encoder::sb_adr_var () const
{
  return sb_adr_var(thread);
}

// Btor2_Encoder::sb_val_var ---------------------------------------------------

string Btor2_Encoder::sb_val_var (const word_t t)
{
  return sb_val_sym + '_' + to_string(t);
}

string Btor2_Encoder::sb_val_var () const
{
  return sb_val_var(thread);
}

// Btor2_Encoder::sb_full_var --------------------------------------------------

string Btor2_Encoder::sb_full_var (const word_t t)
{
  return sb_full_sym + '_' + to_string(t);
}

string Btor2_Encoder::sb_full_var () const
{
  return sb_full_var(thread);
}

// Btor2_Encoder::stmt_var -----------------------------------------------------

string Btor2_Encoder::stmt_var (const word_t t, const word_t pc)
{
  return stmt_sym + '_' + to_string(t) + '_' + to_string(pc);
}

string Btor2_Encoder::stmt_var () const
{
  return stmt_var(thread, pc);
}

// Btor2_Encoder::block_var ----------------------------------------------------

string Btor2_Encoder::block_var (const word_t t, const word_t id)
{
  return block_sym + '_' + to_string(t) + '_' + to_string(id);
}

// Btor2_Encoder::thread_var ---------------------------------------------------

string Btor2_Encoder::thread_var (const word_t t)
{
  return thread_sym + '_' + to_string(t);
}

string Btor2_Encoder::thread_var () const
{
  return thread_var(thread);
}

// Btor2_Encoder::exec_var -----------------------------------------------------

string Btor2_Encoder::exec_var (const word_t t, const word_t pc)
{
  return exec_sym + '_' + to_string(t) + '_' + to_string(pc);
}

string Btor2_Encoder::exec_var () const
{
  return exec_var(thread, pc);
}

// Btor2_Encoder::flush_var ----------------------------------------------------

string Btor2_Encoder::flush_var (const word_t t)
{
  return flush_sym + '_' + to_string(t);
}

string Btor2_Encoder::flush_var () const
{
  return flush_var(thread);
}

// Btor2_Encoder::check_var ----------------------------------------------------

string Btor2_Encoder::check_var (const word_t id)
{
  return check_sym + '_' + to_string(id);
}

// Btor2_Encoder::nid ----------------------------------------------------------

string Btor2_Encoder::nid ()
{
  return to_string(node++);
}

string Btor2_Encoder::nid (int offset)
{
  return to_string(static_cast<int>(node) + offset);
}

// Btor2_Encoder::debug_symbol -------------------------------------------------

string Btor2_Encoder::debug_symbol (const word_t t, const word_t p)
{
  const Instruction & op = (*programs)[t][p];

  string sym =
    to_string(t) +
    ":" +
    to_string(p) +
    ":" +
    op.symbol();

  if (op.is_unary())
    sym += ":" + to_string(op.arg());

  return sym;
}

// Btor2_Encoder::load ---------------------------------------------------------

string Btor2_Encoder::load (const word_t address, const bool indirect)
{
  //////////////////////////////////////////////////////////////////////////////
  //
  // * store buffer is full
  //   * store buffer contains address
  //     * store buffer value equals address
  //       * return store buffer value
  //     * store buffer value does not equal address
  //       * store buffer address equals heap[store buffer value]
  //         * return return store buffer value
  //       * store buffer address does not equal heap[store buffer value]
  //         * return heap[heap[store buffer value]]
  //   * store buffer does not contain address
  //     * store buffer address equals heap[address]
  //       * return return store buffer value
  //     * store buffer address does not equal heap[address]
  //       * return heap[heap[address]]
  // * store buffer is empty
  //   * return heap[heap[address]]
  //
  // direct ////////////////////////////////////////////////////////////////////
  //
  // sb-adr == address
  //   ? sb-val
  //   : heap[address]
  //
  // indirect //////////////////////////////////////////////////////////////////
  //
  // sb-full
  // ? sb-adr == address
  //   ? sb-val == address
  //     ? sb-val (e.g. LOAD 0 | sb = {0, 0})
  //     : sb-adr == heap[sb-val]
  //       ? sb-val (e.b. LOAD 0 | sb = {0, 1}, heap = {{1, 0}})
  //       : heap[heap[sb-val]] (e.g. LOAD 0 | sb = {0, 1}, heap = {{1, 1}})
  //   : sb-adr == heap[address]
  //     ? sb-val (e.g. LOAD 0 | sb = {1, 0}, heap = {{0, 1}})
  //     : heap[heap[address]] (e.g. LOAD 0 | sb = {1, x}, heap = {{0, 0}}
  // : heap[heap[address]] (e.g. LOAD 0 | sb = {}, heap = {{0, 0}}
  //
  //////////////////////////////////////////////////////////////////////////////

  const string & nid_adr = nids_const[address];
  const string & nid_sb_adr = nids_sb_adr[thread];
  const string & nid_sb_val = nids_sb_val[thread];
  const string & nid_sb_full = nids_sb_full[thread];

  // heap[address]
  string nid_read_adr =
    lookup(
      nids_read,
      address,
      [this, &nid_adr] {
        string nid_read = nid();

        formula <<
          btor2::read(
            nid_read,
            sid_bv,
            nid_heap,
            nid_adr);

        return nid_read;
      });

  // sb-adr == address
  string nid_eq_sb_adr_adr =
    lookup(
      nids_eq_sb_adr_adr[thread],
      address,
      [this, &nid_adr, &nid_sb_adr] {
        string nid_eq = nid();

        formula <<
          btor2::eq(
            nid_eq,
            sid_bool,
            nid_sb_adr,
            nid_adr);

        return nid_eq;
      });

  if (indirect)
    return
      lookup(
        nids_load_indirect[thread],
        address,
        [&] {
          // heap[heap[address]]
          string nid_read_indirect =
            lookup(
              nids_read_indirect,
              address,
              [this, &nid_read_adr] {
                string nid_read = nid();

                formula <<
                  btor2::read(
                    nid_read,
                    sid_bv,
                    nid_heap,
                    nid_read_adr);

                return nid_read;
              });

          // sb-adr == heap[address]
          string nid_eq_sb_adr_read_adr = nid();

          formula <<
            btor2::eq(
              nid_eq_sb_adr_read_adr,
              sid_bool,
              nid_sb_adr,
              nid_read_adr);

          // sb-adr == heap[address]
          // ? sb-val_t
          // : heap[heap[address]]
          string nid_ite_eq_sb_adr_read_adr = nid();

          formula <<
            btor2::ite(
              nid_ite_eq_sb_adr_read_adr,
              sid_bv,
              nid_eq_sb_adr_read_adr,
              nid_sb_val,
              nid_read_indirect);

          // sb-adr == heap[sb-val]
          // ? sb-val (e.b. LOAD 0 | sb = {0, 1}, heap = {{1, 0}})
          // : heap[heap[sb-val]] (e.g. LOAD 0 | sb = {0, 1}, heap = {{1, 1}})
          string nid_ite_eq_sb_adr_read_sb_val =
            lookup(
              nids_ite_eq_sb_adr_read_sb_val,
              thread,
              [this, &nid_sb_adr, &nid_sb_val] {
                // heap[sb-val]]
                string nid_read_sb_val = nid();

                formula <<
                  btor2::read(
                    nid_read_sb_val,
                    sid_bv,
                    nid_heap,
                    nid_sb_val);

                // heap[heap[sb-val]]
                string nid_read_sb_val_indirect = nid();

                formula <<
                  btor2::read(
                    nid_read_sb_val_indirect,
                    sid_bv,
                    nid_heap,
                    nid_read_sb_val);

                // sb-adr == heap[sb-val]
                string nid_eq_sb_adr_read_sb_val = nid();

                formula <<
                  btor2::eq(
                    nid_eq_sb_adr_read_sb_val,
                    sid_bool,
                    nid_sb_adr,
                    nid_read_sb_val);

                // sb-adr == heap[sb-val]
                // ? sb-val
                // : heap[heap[sb-val]]
                string nid_ite = nid();

                formula <<
                  btor2::ite(
                    nid_ite,
                    sid_bv,
                    nid_eq_sb_adr_read_sb_val,
                    nid_sb_val,
                    nid_read_sb_val_indirect);

                return nid_ite;
              });

          // sb-val == address
          string nid_eq_sb_val_adr = nid();

          formula <<
            btor2::eq(
              nid_eq_sb_val_adr,
              sid_bool,
              nid_sb_val,
              nid_adr);

          // sb-val == address
          // ? sb-val
          // : sb-adr == heap[sb-val]
          //   ? sb-val
          //   : heap[heap[sb-val]]
          string nid_ite_eq_sb_val_adr = nid();

          formula <<
            btor2::ite(
              nid_ite_eq_sb_val_adr,
              sid_bv,
              nid_eq_sb_val_adr,
              nid_sb_val,
              nid_ite_eq_sb_adr_read_sb_val);

          // sb-adr == address
          // ? sb-val == address
          //   ? sb-val (e.g. LOAD 0 | sb = {0, 0})
          //   : sb-adr == heap[sb-val]
          //     ? sb-val (e.b. LOAD 0 | sb = {0, 1}, heap = {{1, 0}})
          //     : heap[heap[sb-val]] (e.g. LOAD 0 | sb = {0, 1}, heap = {{1, 1}})
          // : sb-adr == heap[address]
          //   ? sb-val (e.g. LOAD 0 | sb = {1, 0}, heap = {{0, 1}})
          //   : heap[heap[address]] (e.g. LOAD 0 | sb = {1, x}, heap = {{0, 0}}
          string nid_ite_eq_sb_adr_adr = nid();

          formula <<
            btor2::ite(
              nid_ite_eq_sb_adr_adr,
              sid_bv,
              nid_eq_sb_adr_adr,
              nid_ite_eq_sb_val_adr,
              nid_ite_eq_sb_adr_read_adr);

          // sb-full
          // ? sb-adr == address
          //   ? sb-val == address
          //     ? sb-val
          //     : sb-adr == heap[sb-val]
          //       ? sb-val
          //       : heap[heap[sb-val]]
          //   : sb-adr == heap[address]
          //     ? sb-val
          //     : heap[heap[address]]
          // : heap[heap[address]]
          string nid_load_indirect = nid();

          formula <<
            btor2::ite(
              nid_load_indirect,
              sid_bv,
              nid_sb_full,
              nid_ite_eq_sb_adr_adr,
              nid_read_indirect);

          return nid_load_indirect;
        });
  else
    return
      lookup(
        nids_load[thread],
        address,
        [&] {
          string nid_load = nid();

          // sb-full && (sb-adr == address)
          formula <<
            btor2::land(
              nid_load,
              sid_bool,
              nid_sb_full,
              nid_eq_sb_adr_adr);

          // sb-full && (sb-adr == address)
          // ? sb-val
          // : heap[address]
          formula <<
            btor2::ite(
              nid_load = nid(),
              sid_bv,
              nid_load,
              nid_sb_val,
              nid_read_adr);

          return nid_load;
        });
}

// Btor2_Encoder::declare_sorts ------------------------------------------------

void Btor2_Encoder::declare_sorts ()
{
  if (verbose)
    formula << btor2::comment_section("sorts");

  formula <<
    btor2::declare_sort(sid_bool = nid(), "1") <<
    btor2::declare_sort(sid_bv = nid(), to_string(word_size)) <<
    btor2::declare_array(sid_heap = nid(), "2", "2") <<
    eol;
}

// Btor2_Encoder::declare_constants --------------------------------------------

void Btor2_Encoder::declare_constants ()
{
  if (verbose)
    formula << btor2::comment_section("constants");

  // boolean constants
  formula <<
    btor2::constd(nid_false = nid(), sid_bool, "0") <<
    btor2::constd(nid_true = nid(), sid_bool, "1") <<
    eol;

  // bitvector constants
  for (const auto & c : nids_const)
    formula <<
      btor2::constd(
        nids_const[c.first] = nid(),
        sid_bv,
        to_string(c.first));

  formula << eol;
}

// Btor2_Encoder::declare_accu -------------------------------------------------

void Btor2_Encoder::declare_accu ()
{
  if (verbose)
    formula << accu_comment;

  nids_accu.reserve(num_threads);

  iterate_threads([this] {
    formula <<
      btor2::state(nids_accu.emplace_back(nid()), sid_bv, accu_var());
  });

  formula << eol;
}

// Btor2_Encoder::declare_mem --------------------------------------------------

void Btor2_Encoder::declare_mem ()
{
  if (verbose)
    formula << mem_comment;

  nids_mem.reserve(num_threads);

  iterate_threads([this] {
    formula <<
      btor2::state(nids_mem.emplace_back(nid()), sid_bv, mem_var());
  });

  formula << eol;
}

// Btor2_Encoder::declare_sb_adr -----------------------------------------------

void Btor2_Encoder::declare_sb_adr ()
{
  if (verbose)
    formula << sb_adr_comment;

  nids_sb_adr.reserve(num_threads);

  iterate_threads([this] {
    formula <<
      btor2::state(nids_sb_adr.emplace_back(nid()), sid_bv, sb_adr_var());
  });

  formula << eol;
}

// Btor2_Encoder::declare_sb_val -----------------------------------------------

void Btor2_Encoder::declare_sb_val ()
{
  if (verbose)
    formula << sb_val_comment;

  nids_sb_val.reserve(num_threads);

  iterate_threads([this] {
    formula <<
      btor2::state(nids_sb_val.emplace_back(nid()), sid_bv, sb_val_var());
  });

  formula << eol;
}

// Btor2_Encoder::declare_sb_full ----------------------------------------------

void Btor2_Encoder::declare_sb_full ()
{
  if (verbose)
    formula << sb_full_comment;

  nids_sb_full.reserve(num_threads);

  iterate_threads([this] {
    formula <<
      btor2::state(nids_sb_full.emplace_back(nid()), sid_bool, sb_full_var());
  });

  formula << eol;
}

// Btor2_Encoder::declare_stmt -------------------------------------------------

void Btor2_Encoder::declare_stmt ()
{
  if (verbose)
    formula << stmt_comment;

  nids_stmt.resize(num_threads);

  iterate_programs([this] (const Program & program) {
    auto & nids = nids_stmt[thread];
    nids.reserve(program.size());

    for (pc = 0; pc < program.size(); pc++)
      formula <<
        btor2::state(
          nids.emplace_back(nid()),
          sid_bool,
          stmt_var());

    formula << eol;
  });
}

// Btor2_Encoder::declare_block ------------------------------------------------

void Btor2_Encoder::declare_block ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << block_comment;

  for (const auto & [c, threads] : check_pcs)
    {
      // TODO: ignore single-threaded checkpoints -> see gitlab issue #65
      if (threads.size() > 1)
        {
          auto & nids = nids_block.insert(nids_block.end(), {c, {}})->second;

          for (const auto & t : threads)
            formula <<
              btor2::state(
                nids.emplace_hint(nids.end(), t.first, nid())->second,
                sid_bool,
                block_var(c, t.first));

          formula << eol;
        }
    }
}

// Btor2_Encoder::declare_heap -------------------------------------------------

void Btor2_Encoder::declare_heap ()
{
  if (verbose)
    formula << heap_comment;

  formula << btor2::state(nid_heap = nid(), sid_heap, heap_sym) << eol;
}

// Btor2_Encoder::declare_exit_flag --------------------------------------------

void Btor2_Encoder::declare_exit_flag ()
{
  if (exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_flag_comment;

  formula
    << btor2::state(nid_exit_flag = nid(), sid_bool, exit_flag_sym)
    << eol;
}

// Btor2_Encoder::declare_exit_code --------------------------------------------

void Btor2_Encoder::declare_exit_code ()
{
  if (exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_code_comment;

  formula << btor2::state(nid_exit_code = nid(), sid_bv, exit_code_var) << eol;
}

// Btor2_Encoder::declare_states -----------------------------------------------

void Btor2_Encoder::declare_states ()
{
  if (verbose)
    formula << btor2::comment_section("state variable declarations");

  declare_accu();
  declare_mem();
  declare_sb_adr();
  declare_sb_val();
  declare_sb_full();
  declare_stmt();
  declare_block();

  declare_heap();
  declare_exit_flag();
  declare_exit_code();
}

// Btor2_Encoder::declare_thread -----------------------------------------------

void Btor2_Encoder::declare_thread ()
{
  if (verbose)
    formula << thread_comment;

  nids_thread.reserve(num_threads);

  iterate_threads([&] () {
    formula <<
      btor2::input(
        nids_thread.emplace_back(nid()),
        sid_bool,
        thread_var());
  });

  formula << eol;
}

// Btor2_Encoder::declare_flush ------------------------------------------------

void Btor2_Encoder::declare_flush ()
{
  if (verbose)
    formula << flush_comment;

  nids_flush.reserve(num_threads);

  iterate_threads([&] () {
    formula <<
      btor2::input(
        nids_flush.emplace_back(nid()),
        sid_bool,
        flush_var());
  });

  formula << eol;
}

// Btor2_Encoder::declare_inputs -----------------------------------------------

void Btor2_Encoder::declare_inputs ()
{
  if (verbose)
    formula << btor2::comment_section("input variable declarations");

  declare_thread();
  declare_flush();
}

// Btor2_Encoder::define_exec --------------------------------------------------

void Btor2_Encoder::define_exec ()
{
  if (verbose)
    formula << exec_comment;

  nids_exec.resize(num_threads);

  iterate_programs([this] (const Program & program) {
    auto & nids = nids_exec[thread];
    nids.reserve(program.size());

    for (pc = 0; pc < program.size(); pc++)
      formula <<
        btor2::land(
          nids.emplace_back(nid()),
          sid_bool,
          nids_stmt[thread][pc],
          nids_thread[thread],
          exec_var());

    formula << eol;
  });
}

// Btor2_Encoder::define_check -------------------------------------------------

void Btor2_Encoder::define_check ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << check_comment;

  for (const auto & [c, blocks] : nids_block)
    {
      // TODO: ignore single-threaded checkpoints -> see gitlab issue #65
      if (blocks.size() > 1)
        {
          vector<string> args;
          args.reserve(blocks.size());

          for (const auto & [t, nid_block] : blocks)
            args.push_back(nid_block);

          formula << btor2::land(node, sid_bool, args, check_var(c));

          nids_check.emplace_hint(nids_check.end(), c, nid(-1));
        }
      else
        {
          nids_check.emplace_hint(nids_check.end(), c, blocks.begin()->second);
        }
    }

  formula << eol;
}

// Btor2_Encoder::define_transitions -------------------------------------------

void Btor2_Encoder::define_transitions ()
{
  if (verbose)
    formula << btor2::comment_section("transition variable definitions");

  define_exec();
  define_check();
}

// Btor2_Encoder::define_state_bv ----------------------------------------------

void Btor2_Encoder::define_state_bv (Instruction::Type type,
                                     const string & nid_state,
                                     const string sym)
{
  const Program & program = (*programs)[thread];
  const vector<string> & exec = nids_exec[thread];

  formula << btor2::init(nid(), sid_bv, nid_state, nids_const[0]);

  string nid_next = nid_state;
  for (pc = 0; pc < program.size(); pc++)
    {
      const Instruction & op = program[pc];

      if (op.type() & type)
        formula <<
          btor2::ite(
            nid_next = nid(),
            sid_bv,
            exec[pc],
            op.encode(*this),
            nid_next,
            verbose ? debug_symbol(thread, pc) : "");
    }

  formula << btor2::next(nid(), sid_bv, nid_state, nid_next, sym) << eol;
}

// Btor2_Encoder::define_accu --------------------------------------------------

void Btor2_Encoder::define_accu ()
{
  if (verbose)
    formula << accu_comment;

  update = State::accu;

  iterate_threads([this] {
    define_state_bv(
      Instruction::Type::accu,
      nids_accu[thread],
      accu_var());
  });
}

// Btor2_Encoder::define_mem ---------------------------------------------------

void Btor2_Encoder::define_mem ()
{
  if (verbose)
    formula << mem_comment;

  update = State::mem;

  iterate_threads([this] {
    define_state_bv(
      Instruction::Type::mem,
      nids_mem[thread],
      mem_var());
  });
}

// Btor2_Encoder::define_sb_adr ------------------------------------------------

void Btor2_Encoder::define_sb_adr ()
{
  if (verbose)
    formula << sb_adr_comment;

  update = State::sb_adr;

  iterate_threads([this] {
    define_state_bv(
      Instruction::Type::write,
      nids_sb_adr[thread],
      sb_adr_var());
  });
}

// Btor2_Encoder::define_sb_val ------------------------------------------------

void Btor2_Encoder::define_sb_val ()
{
  if (verbose)
    formula << sb_val_comment;

  update = State::sb_val;

  iterate_threads([this] {
    define_state_bv(
      Instruction::Type::write,
      nids_sb_val[thread],
      sb_val_var());
  });
}

// Btor2_Encoder::define_sb_full -----------------------------------------------

void Btor2_Encoder::define_sb_full ()
{
  if (verbose)
    formula << sb_full_comment;

  iterate_programs([this] (const Program & program) {
    vector<string> lor;

    for (pc = 0; pc < program.size(); pc++)
      if (program[pc].type() & Instruction::Type::write)
        lor.push_back(nids_exec[thread][pc]);

    lor.push_back(nids_sb_full[thread]);

    string prev;

    formula <<
      btor2::init(nid(), sid_bool, nids_sb_full[thread], nid_false) <<
      btor2::lor(node, sid_bool, lor) <<
      btor2::ite(
        prev = nid(),
        sid_bool,
        nids_flush[thread],
        nid_false,
        nid(-1)) <<
      btor2::next(
        nid(),
        sid_bool,
        nids_sb_full[thread],
        prev,
        sb_full_var()) <<
      eol;
  });
}

// Btor2_Encoder::define_stmt --------------------------------------------------

void Btor2_Encoder::define_stmt ()
{
  if (verbose)
    formula << stmt_comment;

  iterate_programs([this] (const Program & program) {
    // map storing nids of jump conditions
    unordered_map<word_t, string> nid_jmp;

    // reduce lookups
    const vector<string> & nids_stmt_thread = nids_stmt[thread];
    const vector<string> & nids_exec_thread = nids_exec[thread];

    for (pc = 0; pc < program.size(); pc++)
      {
        string nid_next = nid();
        string nid_exec = nids_exec_thread[pc];
        string nid_stmt = nids_stmt_thread[pc];

        // init
        formula <<
          btor2::init(
            nid_next,
            sid_bool,
            nid_stmt,
            pc ? nid_false : nid_true);

        // add statement reactivation
        formula <<
          btor2::land(
            nid_next = nid(),
            sid_bool,
            nid_stmt,
            btor2::lnot(nid_exec),
            verbose ? debug_symbol(thread, pc) : "");

        // add activation by predecessor's execution
        for (word_t prev : program.predecessors.at(pc))
          {
            nid_exec = nids_exec_thread[prev];

            const Instruction & pred = program[prev];

            // predecessor is a jump
            if (pred.is_jump())
              {
                string nid_cond =
                  lookup(
                    nid_jmp,
                    prev,
                    [this, &pred] { return pred.encode(*this); });

                // nothing to do here for unconditional jumps (JMP)
                if (!nid_cond.empty())
                  {
                    // add negated condition if preceding jump failed
                    if (prev == pc - 1 && pred.arg() != pc)
                      nid_cond = btor2::lnot(nid_cond);

                    // add conjunction of execution variable & jump condition
                    formula <<
                      btor2::land(
                        nid_exec = nid(),
                        sid_bool,
                        nid_exec,
                        nid_cond);
                  }
              }

            // add predecessors activation
            formula <<
              btor2::ite(
                nid_next = nid(),
                sid_bool,
                nids_stmt_thread[prev],
                nid_exec,
                nid_next,
                verbose ? debug_symbol(thread, prev) : "");
          }

        formula <<
          btor2::next(
            nid(),
            sid_bool,
            nid_stmt,
            nid_next,
            stmt_var()) <<
          eol;
      }
  });
}

// Btor2_Encoder::define_block -------------------------------------------------

void Btor2_Encoder::define_block ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << block_comment;

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
              string & nid_block = nid_block_it++->second;

              vector<string> args;
              args.reserve(pcs.size() + 1);

              for (const auto & p : pcs)
                args.push_back(nids_exec[t][p]);

              args.push_back(nid_block);

              string prev;

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

// Btor2_Encoder::define_heap --------------------------------------------------

void Btor2_Encoder::define_heap ()
{
  if (verbose)
    formula << heap_comment;

  update = State::heap;

  string nid_next = nid_heap;

  iterate_programs([this, &nid_next] (const Program & program) {
    // store buffer flush
    string nid_flush = nid();

    formula <<
      btor2::write(
        nid_flush,
        sid_heap,
        nid_heap,
        nids_sb_adr[thread],
        nids_sb_val[thread]) <<
      btor2::ite(
        nid_next = nid(),
        sid_heap,
        nids_flush[thread],
        nid_flush,
        nid_next,
        verbose ? flush_var() : "");

    // atomic instructions
    for (pc = 0; pc < program.size(); pc++)
      {
        const Instruction & op = program[pc];

        if (op.type() & Instruction::Type::atomic)
          formula <<
            btor2::ite(
              nid_next = nid(),
              sid_heap,
              nids_exec[thread][pc],
              op.encode(*this),
              nid_next,
              verbose ? debug_symbol(thread, pc) : "");
      }
  });

  formula << btor2::next(nid(), sid_heap, nid_heap, nid_next, heap_sym) << eol;
}

// Btor2_Encoder::define_exit_flag ---------------------------------------------

void Btor2_Encoder::define_exit_flag ()
{
  if (exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_flag_comment;

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

// Btor2_Encoder::define_exit_code ---------------------------------------------

void Btor2_Encoder::define_exit_code ()
{
  if (exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_code_comment;

  formula << btor2::init(nid(), sid_bv, nid_exit_code, nids_const[0]);

  string nid_next = nid_exit_code;

  for (const auto & [t, pcs] : exit_pcs)
    for (const auto & p : pcs)
      formula <<
        btor2::ite(
          nid_next = nid(),
          sid_bv,
          nids_exec[t][p],
          (*programs)[t][p].encode(*this),
          nid_next,
          verbose ? debug_symbol(t, p) : "");

  formula
    << btor2::next(nid(), sid_bv, nid_exit_code, nid_next, exit_code_var)
    << eol;
}

// Btor2_Encoder::define_states ------------------------------------------------

void Btor2_Encoder::define_states ()
{
  if (verbose)
    formula << btor2::comment_section("state variable definitions");

  define_accu();
  define_mem();
  define_sb_adr();
  define_sb_val();
  define_sb_full();
  define_stmt();
  define_block();

  define_heap();
  define_exit_flag();
  define_exit_code();
}

// Btor2_Encoder::define_scheduling_constraints --------------------------------

void Btor2_Encoder::define_scheduling_constraints ()
{
  if (verbose)
    formula << btor2::comment_section("scheduling constraints");

  vector<string> variables;
  variables.reserve(num_threads * 2 + 1);

  variables.insert(variables.end(), nids_thread.begin(), nids_thread.end());
  variables.insert(variables.end(), nids_flush.begin(), nids_flush.end());

  if (!exit_pcs.empty())
    variables.push_back(nid_exit_flag);

  formula <<
    (use_sinz_constraint
      ? btor2::card_constraint_sinz(node, sid_bool, variables)
      : btor2::card_constraint_naive(node, sid_bool, variables)) <<
    eol;
}

// Btor2_Encoder::define_store_buffer_constraints ------------------------------

void Btor2_Encoder::define_store_buffer_constraints ()
{
  if (flush_pcs.empty())
    return;

  if (verbose)
    formula << btor2::comment_section("store buffer constraints");

  iterate_threads([this] {
    if (flush_pcs.find(thread) != flush_pcs.end())
      {
        string nid_or;

        if (flush_pcs[thread].size() > 1)
          {
            vector<string> stmts;

            stmts.reserve(flush_pcs[thread].size());

            std::transform(
              flush_pcs[thread].begin(),
              flush_pcs[thread].end(),
              back_inserter(stmts),
              [this] (const word_t p) { return nids_stmt[thread][p]; });

            formula << btor2::lor(node, sid_bool, stmts);

            nid_or = nid(-1);
          }
        else
          {
            nid_or = nids_stmt[thread][flush_pcs[thread][0]];
          }

        formula <<
          btor2::implies(
            nid(),
            sid_bool,
            nid_or,
            btor2::lnot(nids_thread[thread])) <<
          btor2::ite(
            nid(),
            sid_bool,
            nids_sb_full[thread],
            nid(-1),
            btor2::lnot(nids_flush[thread])) <<
          btor2::constraint(node) <<
          eol;
      }
  });
}

// Btor2_Encoder::define_checkpoint_constraints --------------------------------

void Btor2_Encoder::define_checkpoint_constraints ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << btor2::comment_section("checkpoint constraints");

  for (const auto & [c, threads] : nids_block)
    {
      // TODO: ignore single-threaded checkpoints -> see gitlab issue #65
      if (threads.size() > 1)
        {
          string not_check = btor2::lnot(nids_check[c]);

          for (const auto & [t, nid_block] : threads)
            {
              string prev = nid();

              formula <<
                btor2::land(
                  prev,
                  sid_bool,
                  nid_block,
                  not_check) <<
                btor2::implies(
                  prev = nid(),
                  sid_bool,
                  prev,
                  btor2::lnot(nids_thread[t])) <<
                btor2::constraint(node, block_var(c, t)) <<
                eol;
            }
        }
    }
}

// Btor2_Encoder::define_constraints -------------------------------------------

void Btor2_Encoder::define_constraints ()
{
  define_scheduling_constraints();
  define_store_buffer_constraints();
  define_checkpoint_constraints();
}

void Btor2_Encoder::define_bound ()
{
  if (verbose)
    formula << btor2::comment_section("bound");

  // step counter
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

  // bound
  if (verbose)
    formula << btor2::comment("bound (" + to_string(bound) + ")") << eol;

  formula <<
    btor2::eq(nid_prev = nid(), sid_bool, nids_const[bound], nid_ctr) <<
    btor2::bad(nid(), nid_prev);
}

// Btor2_Encoder::encode -------------------------------------------------------

void Btor2_Encoder::encode ()
{
  declare_sorts();
  declare_constants();
  declare_states();
  declare_inputs();
  define_transitions();
  define_states();
  define_constraints();
  define_bound();
}

string Btor2_Encoder::encode (const Instruction::Load & l)
{
  return load(l.arg, l.indirect);
}

string Btor2_Encoder::encode (const Instruction::Store & s)
{
  switch (update)
    {
    case State::sb_adr:
      return s.indirect ? load(s.arg) : nids_const[s.arg];

    case State::sb_val:
      return nids_accu[thread];

    default: throw runtime_error("illegal state update");
    }
}

// TODO
string Btor2_Encoder::encode (const Instruction::Fence & f [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string Btor2_Encoder::encode (const Instruction::Add & a)
{
  string nid_add = load(a.arg, a.indirect);

  formula << btor2::add(nid_add = nid(), sid_bv, nids_accu[thread], nid_add);

  return nid_add;
}

string Btor2_Encoder::encode (const Instruction::Addi & a)
{
  string nid_addi = nids_const[a.arg];

  formula << btor2::add(nid_addi = nid(), sid_bv, nids_accu[thread], nid_addi);

  return nid_addi;
}

string Btor2_Encoder::encode (const Instruction::Sub & s)
{
  string nid_sub = load(s.arg, s.indirect);

  formula << btor2::sub(nid_sub = nid(), sid_bv, nids_accu[thread], nid_sub);

  return nid_sub;
}

string Btor2_Encoder::encode (const Instruction::Subi & s)
{
  string nid_subi = nids_const[s.arg];

  formula << btor2::sub(nid_subi = nid(), sid_bv, nids_accu[thread], nid_subi);

  return nid_subi;
}

string Btor2_Encoder::encode (const Instruction::Mul & m)
{
  string nid_mul = load(m.arg, m.indirect);

  formula << btor2::mul(nid_mul = nid(), sid_bv, nids_accu[thread], nid_mul);

  return nid_mul;
}

string Btor2_Encoder::encode (const Instruction::Muli & m)
{
  string nid_muli = nids_const[m.arg];

  formula << btor2::mul(nid_muli = nid(), sid_bv, nids_accu[thread], nid_muli);

  return nid_muli;
}

string Btor2_Encoder::encode (const Instruction::Cmp & c)
{
  string nid_sub = load(c.arg, c.indirect);

  formula << btor2::sub(nid_sub = nid(), sid_bv, nids_accu[thread], nid_sub);

  return nid_sub;
}

string Btor2_Encoder::encode (const Instruction::Jmp & j [[maybe_unused]])
{
  return "";
}

string Btor2_Encoder::encode (const Instruction::Jz & j [[maybe_unused]])
{
  string nid_jz = nid();

  formula << btor2::eq(nid_jz, sid_bool, nids_accu[thread], nids_const[0]);

  return nid_jz;
}

string Btor2_Encoder::encode (const Instruction::Jnz & j [[maybe_unused]])
{
  string nid_jnz = nid();

  formula << btor2::ne(nid_jnz, sid_bool, nids_accu[thread], nids_const[0]);

  return nid_jnz;
}

string Btor2_Encoder::encode (const Instruction::Js & j [[maybe_unused]])
{
  string nid_js = nid();

  formula << btor2::slice(nid_js, sid_bool, nids_accu[thread], msb, msb);

  return nid_js;
}

string Btor2_Encoder::encode (const Instruction::Jns & j [[maybe_unused]])
{
  string nid_jns = nid();

  formula << btor2::slice(nid_jns, sid_bool, nids_accu[thread], msb, msb);

  return btor2::lnot(nid_jns);
}

string Btor2_Encoder::encode (const Instruction::Jnzns & j [[maybe_unused]])
{
  string nid_nz = nid();

  formula <<
    btor2::ne(nid_nz, sid_bool, nids_accu[thread], nids_const[0]);

  string nid_nzns = nid();

  formula
    << btor2::slice(nid_nzns, sid_bool, nids_accu[thread], msb, msb)
    << btor2::land(nid_nzns = nid(), sid_bool, nid_nz, btor2::lnot(nid_nzns));

  return nid_nzns;
}

string Btor2_Encoder::encode (const Instruction::Mem & m)
{
  return load(m.arg, m.indirect);
}

string Btor2_Encoder::encode (const Instruction::Cas & c)
{
  string nid_cas =
    lookup(
      c.indirect
        ? nids_cas_indirect[thread]
        : nids_cas[thread],
      c.arg,
      [this, &c] {
        string nid_cond = load(c.arg);

        formula
          << btor2::eq(nid_cond = nid(), sid_bool, nids_mem[thread], nid_cond);

        return nid_cond;
      });

  switch (update)
    {
    case State::accu:
        {
          formula <<
            btor2::ite(
              nid_cas = nid(),
              sid_bv,
              nid_cas,
              nids_const[1],
              nids_const[0]);
          break;
        }
    case State::heap:
        {
          string nid_write = nid();

          formula <<
            btor2::write(
              nid_write,
              sid_heap,
              nid_heap,
              c.indirect
                ? load(c.arg)
                : nids_const[c.arg],
              nids_accu[thread]);

          formula <<
            btor2::ite(nid_cas = nid(), sid_heap, nid_cas, nid_write, nid_heap);
          break;
        }

    default: throw runtime_error("illegal state update");
    }

  return nid_cas;
}

string Btor2_Encoder::encode (const Instruction::Check & s [[maybe_unused]])
{
  return "";
}

// TODO
string Btor2_Encoder::encode (const Instruction::Halt & h [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string Btor2_Encoder::encode (const Instruction::Exit & e [[maybe_unused]])
{
  return nids_const[e.arg];
}
