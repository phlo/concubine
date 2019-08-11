#include "encoder.hh"

#include <algorithm>
#include <cassert>

#include "btor2.hh"
#include "mmap.hh"

namespace ConcuBinE::btor2 {

//==============================================================================
// helpers
//==============================================================================

// map lookup helpers, performing an arbitrary action for missing values -------

template <typename K, typename V, typename F>
V & lookup (std::map<K, V> & m, K k, F fun)
{
  // avoid extra lookups https://stackoverflow.com/a/101980
  auto lb = m.lower_bound(k);

  return
    lb != m.end() && !(m.key_comp()(k, lb->first))
      ? lb->second
      : m.insert(lb, {k, fun()})->second;
}

template <class K, class V, class F>
V & lookup (std::unordered_map<K, V> & m, K k, F fun)
{
  auto it = m.find(k);

  return
    it != m.end()
      ? it->second
      : m.insert(it, {k, fun()})->second;
}

//==============================================================================
// btor2::Encoder
//==============================================================================

//------------------------------------------------------------------------------
// static members
//------------------------------------------------------------------------------

// exit code variable ----------------------------------------------------------

const std::string & Encoder::exit_code_var = exit_code_sym;

// variable comments -----------------------------------------------------------

const std::string Encoder::accu_comment =
  comment(
    ConcuBinE::Encoder::accu_comment
    + " - "
    + accu_sym
    + "_<thread>"
    + eol);

const std::string Encoder::mem_comment =
  comment(
    ConcuBinE::Encoder::mem_comment
    + " - "
    + mem_sym
    + "_<thread>"
    + eol);

const std::string Encoder::sb_adr_comment =
  comment(
    ConcuBinE::Encoder::sb_adr_comment
    + " - "
    + sb_adr_sym
    + "_<thread>"
    + eol);

const std::string Encoder::sb_val_comment =
  comment(
    ConcuBinE::Encoder::sb_val_comment
    + " - "
    + sb_val_sym
    + "_<thread>"
    + eol);

const std::string Encoder::sb_full_comment =
  comment(
    ConcuBinE::Encoder::sb_full_comment
    + " - "
    + sb_full_sym
    + "_<thread>"
    + eol);

const std::string Encoder::stmt_comment =
  comment(
    ConcuBinE::Encoder::stmt_comment
    + " - "
    + stmt_sym
    + "_<thread>_<pc>"
    + eol);

const std::string Encoder::block_comment =
  comment(
    ConcuBinE::Encoder::block_comment
    + " - "
    + block_sym
    + "_<id>_<thread>"
    + eol);

const std::string Encoder::halt_comment =
  comment(
    ConcuBinE::Encoder::halt_comment
    + " - "
    + halt_sym
    + "_<thread>"
    + eol);

const std::string Encoder::heap_comment =
  comment(ConcuBinE::Encoder::heap_comment + eol);

const std::string Encoder::exit_flag_comment =
  comment(ConcuBinE::Encoder::exit_flag_comment + eol);

const std::string Encoder::exit_code_comment =
  comment(ConcuBinE::Encoder::exit_code_comment + eol);

const std::string Encoder::thread_comment =
  comment(
    ConcuBinE::Encoder::thread_comment
    + " - "
    + thread_sym
    + "_<thread>"
    + eol);

const std::string Encoder::exec_comment =
  comment(
    ConcuBinE::Encoder::exec_comment
    + " - "
    + exec_sym
    + "_<thread>_<pc>"
    + eol);

const std::string Encoder::flush_comment =
  comment(
    ConcuBinE::Encoder::flush_comment
    + " - "
    + flush_sym
    + "_<thread>"
    + eol);

const std::string Encoder::check_comment =
  comment(
    ConcuBinE::Encoder::check_comment
    + " - "
    + check_sym
    + "_<id>"
    + eol);

// most significant bit's bitvector constant -----------------------------------

const std::string Encoder::msb = std::to_string(word_size - 1);

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

Encoder::Encoder (const Program::List::ptr & p,
                  const std::shared_ptr<MMap> & m,
                  const size_t b) :
  ConcuBinE::Encoder(p, m, b),
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

  if (mmap && !mmap->empty())
    for (const auto & [adr, val] : *mmap)
      nids_const[adr] = nids_const[val];
}

//------------------------------------------------------------------------------
// private member functions
//------------------------------------------------------------------------------

// btor2::Encoder::accu_var ----------------------------------------------------

std::string Encoder::accu_var (const word_t t)
{
  return accu_sym + '_' + std::to_string(t);
}

std::string Encoder::accu_var () const
{
  return accu_var(thread);
}

// btor2::Encoder::mem_var -----------------------------------------------------

std::string Encoder::mem_var (const word_t t)
{
  return mem_sym + '_' + std::to_string(t);
}

std::string Encoder::mem_var () const
{
  return mem_var(thread);
}

// btor2::Encoder::sb_adr_var --------------------------------------------------

std::string Encoder::sb_adr_var (const word_t t)
{
  return sb_adr_sym + '_' + std::to_string(t);
}

std::string Encoder::sb_adr_var () const
{
  return sb_adr_var(thread);
}

// btor2::Encoder::sb_val_var --------------------------------------------------

std::string Encoder::sb_val_var (const word_t t)
{
  return sb_val_sym + '_' + std::to_string(t);
}

std::string Encoder::sb_val_var () const
{
  return sb_val_var(thread);
}

// btor2::Encoder::sb_full_var -------------------------------------------------

std::string Encoder::sb_full_var (const word_t t)
{
  return sb_full_sym + '_' + std::to_string(t);
}

std::string Encoder::sb_full_var () const
{
  return sb_full_var(thread);
}

// btor2::Encoder::stmt_var ----------------------------------------------------

std::string Encoder::stmt_var (const word_t t, const word_t pc)
{
  return stmt_sym + '_' + std::to_string(t) + '_' + std::to_string(pc);
}

std::string Encoder::stmt_var () const
{
  return stmt_var(thread, pc);
}

// btor2::Encoder::block_var ---------------------------------------------------

std::string Encoder::block_var (const word_t t, const word_t id)
{
  return block_sym + '_' + std::to_string(t) + '_' + std::to_string(id);
}

// btor2::Encoder::halt_var ----------------------------------------------------

std::string Encoder::halt_var (const word_t t)
{
  return halt_sym + '_' + std::to_string(t);
}

std::string Encoder::halt_var () const
{
  return halt_var(thread);
}

// btor2::Encoder::thread_var --------------------------------------------------

std::string Encoder::thread_var (const word_t t)
{
  return thread_sym + '_' + std::to_string(t);
}

std::string Encoder::thread_var () const
{
  return thread_var(thread);
}

// btor2::Encoder::exec_var ----------------------------------------------------

std::string Encoder::exec_var (const word_t t, const word_t pc)
{
  return exec_sym + '_' + std::to_string(t) + '_' + std::to_string(pc);
}

std::string Encoder::exec_var () const
{
  return exec_var(thread, pc);
}

// btor2::Encoder::flush_var ---------------------------------------------------

std::string Encoder::flush_var (const word_t t)
{
  return flush_sym + '_' + std::to_string(t);
}

std::string Encoder::flush_var () const
{
  return flush_var(thread);
}

// btor2::Encoder::check_var ---------------------------------------------------

std::string Encoder::check_var (const word_t id)
{
  return check_sym + '_' + std::to_string(id);
}

// btor2::Encoder::nid ---------------------------------------------------------

std::string Encoder::nid ()
{
  return std::to_string(node++);
}

std::string Encoder::nid (const int offset)
{
  return std::to_string(static_cast<int>(node) + offset);
}

// btor2::Encoder::debug_symbol ------------------------------------------------

std::string Encoder::debug_symbol (const word_t t, const word_t p)
{
  const Instruction & op = (*programs)[t][p];

  std::string sym =
    std::to_string(t) +
    ":" +
    std::to_string(p) +
    ":" +
    op.symbol();

  if (op.is_unary())
    sym += ":" + std::to_string(op.arg());

  return sym;
}

// btor2::Encoder::load --------------------------------------------------------

std::string Encoder::load (const word_t address, const bool indirect)
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

  const std::string & nid_adr = nids_const[address];
  const std::string & nid_sb_adr = nids_sb_adr[thread];
  const std::string & nid_sb_val = nids_sb_val[thread];
  const std::string & nid_sb_full = nids_sb_full[thread];

  // heap[address]
  std::string nid_read_adr =
    lookup(
      nids_read,
      address,
      [this, &nid_adr] {
        std::string nid_read = nid();

        formula << read(nid_read, sid_bv, nid_heap, nid_adr);

        return nid_read;
      });

  // sb-adr == address
  std::string nid_eq_sb_adr_adr =
    lookup(
      nids_eq_sb_adr_adr[thread],
      address,
      [this, &nid_adr, &nid_sb_adr] {
        std::string nid_eq = nid();

        formula << eq(nid_eq, sid_bool, nid_sb_adr, nid_adr);

        return nid_eq;
      });

  if (indirect)
    return
      lookup(
        nids_load_indirect[thread],
        address,
        [&] {
          // heap[heap[address]]
          std::string nid_read_indirect =
            lookup(
              nids_read_indirect,
              address,
              [this, &nid_read_adr] {
                std::string nid_read = nid();

                formula << read(nid_read, sid_bv, nid_heap, nid_read_adr);

                return nid_read;
              });

          // sb-adr == heap[address]
          std::string nid_eq_sb_adr_read_adr = nid();

          formula <<
            eq(
              nid_eq_sb_adr_read_adr,
              sid_bool,
              nid_sb_adr,
              nid_read_adr);

          // sb-adr == heap[address]
          // ? sb-val_t
          // : heap[heap[address]]
          std::string nid_ite_eq_sb_adr_read_adr = nid();

          formula <<
            ite(
              nid_ite_eq_sb_adr_read_adr,
              sid_bv,
              nid_eq_sb_adr_read_adr,
              nid_sb_val,
              nid_read_indirect);

          // sb-adr == heap[sb-val]
          // ? sb-val (e.b. LOAD 0 | sb = {0, 1}, heap = {{1, 0}})
          // : heap[heap[sb-val]] (e.g. LOAD 0 | sb = {0, 1}, heap = {{1, 1}})
          std::string nid_ite_eq_sb_adr_read_sb_val =
            lookup(
              nids_ite_eq_sb_adr_read_sb_val,
              thread,
              [this, &nid_sb_adr, &nid_sb_val] {

                // heap[sb-val]]
                std::string nid_read_sb_val = nid();

                formula << read(nid_read_sb_val, sid_bv, nid_heap, nid_sb_val);

                // heap[heap[sb-val]]
                std::string nid_read_sb_val_indirect = nid();

                formula <<
                  read(
                    nid_read_sb_val_indirect,
                    sid_bv,
                    nid_heap,
                    nid_read_sb_val);

                // sb-adr == heap[sb-val]
                std::string nid_eq_sb_adr_read_sb_val = nid();

                formula <<
                  eq(
                    nid_eq_sb_adr_read_sb_val,
                    sid_bool,
                    nid_sb_adr,
                    nid_read_sb_val);

                // sb-adr == heap[sb-val]
                // ? sb-val
                // : heap[heap[sb-val]]
                std::string nid_ite = nid();

                formula <<
                  ite(
                    nid_ite,
                    sid_bv,
                    nid_eq_sb_adr_read_sb_val,
                    nid_sb_val,
                    nid_read_sb_val_indirect);

                return nid_ite;
              });

          // sb-val == address
          std::string nid_eq_sb_val_adr = nid();

          formula << eq(nid_eq_sb_val_adr, sid_bool, nid_sb_val, nid_adr);

          // sb-val == address
          // ? sb-val
          // : sb-adr == heap[sb-val]
          //   ? sb-val
          //   : heap[heap[sb-val]]
          std::string nid_ite_eq_sb_val_adr = nid();

          formula <<
            ite(
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
          std::string nid_ite_eq_sb_adr_adr = nid();

          formula <<
            ite(
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
          std::string nid_load_indirect = nid();

          formula <<
            ite(
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
          std::string nid_load = nid();

          // sb-full && (sb-adr == address)
          formula << land(nid_load, sid_bool, nid_sb_full, nid_eq_sb_adr_adr);

          // sb-full && (sb-adr == address)
          // ? sb-val
          // : heap[address]
          formula <<
            ite(
              nid_load = nid(),
              sid_bv,
              nid_load,
              nid_sb_val,
              nid_read_adr);

          return nid_load;
        });
}

// btor2::Encoder::declare_sorts -----------------------------------------------

void Encoder::declare_sorts ()
{
  if (verbose)
    formula << comment_section("sorts");

  formula <<
    declare_sort(sid_bool = nid(), "1") <<
    declare_sort(sid_bv = nid(), std::to_string(word_size)) <<
    declare_array(sid_heap = nid(), "2", "2") <<
    eol;
}

// btor2::Encoder::declare_constants -------------------------------------------

void Encoder::declare_constants ()
{
  if (verbose)
    formula << comment_section("constants");

  // boolean constants
  formula <<
    constd(nid_false = nid(), sid_bool, "0") <<
    constd(nid_true = nid(), sid_bool, "1") <<
    eol;

  // bitvector constants
  for (const auto & c : nids_const)
    formula <<
      constd(nids_const[c.first] = nid(), sid_bv, std::to_string(c.first));

  formula << eol;
}

// btor2::Encoder::declare_accu ------------------------------------------------

void Encoder::declare_accu ()
{
  if (verbose)
    formula << accu_comment;

  nids_accu.reserve(num_threads);

  iterate_threads([this] {
    formula << state(nids_accu.emplace_back(nid()), sid_bv, accu_var());
  });

  formula << eol;
}

// btor2::Encoder::declare_mem -------------------------------------------------

void Encoder::declare_mem ()
{
  if (verbose)
    formula << mem_comment;

  nids_mem.reserve(num_threads);

  iterate_threads([this] {
    formula << state(nids_mem.emplace_back(nid()), sid_bv, mem_var());
  });

  formula << eol;
}

// btor2::Encoder::declare_sb_adr ----------------------------------------------

void Encoder::declare_sb_adr ()
{
  if (verbose)
    formula << sb_adr_comment;

  nids_sb_adr.reserve(num_threads);

  iterate_threads([this] {
    formula << state(nids_sb_adr.emplace_back(nid()), sid_bv, sb_adr_var());
  });

  formula << eol;
}

// btor2::Encoder::declare_sb_val ----------------------------------------------

void Encoder::declare_sb_val ()
{
  if (verbose)
    formula << sb_val_comment;

  nids_sb_val.reserve(num_threads);

  iterate_threads([this] {
    formula << state(nids_sb_val.emplace_back(nid()), sid_bv, sb_val_var());
  });

  formula << eol;
}

// btor2::Encoder::declare_sb_full ---------------------------------------------

void Encoder::declare_sb_full ()
{
  if (verbose)
    formula << sb_full_comment;

  nids_sb_full.reserve(num_threads);

  iterate_threads([this] {
    formula << state(nids_sb_full.emplace_back(nid()), sid_bool, sb_full_var());
  });

  formula << eol;
}

// btor2::Encoder::declare_stmt ------------------------------------------------

void Encoder::declare_stmt ()
{
  if (verbose)
    formula << stmt_comment;

  nids_stmt.resize(num_threads);

  iterate_programs([this] (const Program & program) {
    auto & nids = nids_stmt[thread];
    nids.reserve(program.size());

    for (pc = 0; pc < program.size(); pc++)
      formula << state(nids.emplace_back(nid()), sid_bool, stmt_var());

    formula << eol;
  });
}

// btor2::Encoder::declare_block -----------------------------------------------

void Encoder::declare_block ()
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
              state(
                nids.emplace_hint(nids.end(), t.first, nid())->second,
                sid_bool,
                block_var(c, t.first));

          formula << eol;
        }
    }
}

// btor2::Encoder::declare_halt ------------------------------------------------

void Encoder::declare_halt ()
{
  if (halt_pcs.empty())
    return;

  if (verbose)
    formula << halt_comment;

  for (const auto & it : halt_pcs)
    formula <<
      state(
        nids_halt.emplace_hint(nids_halt.end(), it.first, nid())->second,
        sid_bool,
        halt_var(it.first));

  formula << eol;
}

// btor2::Encoder::declare_heap ------------------------------------------------

void Encoder::declare_heap ()
{
  if (verbose)
    formula << heap_comment;

  formula << state(nid_heap = nid(), sid_heap, heap_sym) << eol;
}

// btor2::Encoder::declare_exit_flag -------------------------------------------

void Encoder::declare_exit_flag ()
{
  if (halt_pcs.empty() && exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_flag_comment;

  formula << state(nid_exit_flag = nid(), sid_bool, exit_flag_sym) << eol;
}

// btor2::Encoder::declare_exit_code -------------------------------------------

void Encoder::declare_exit_code ()
{
  if (verbose)
    formula << exit_code_comment;

  formula << state(nid_exit_code = nid(), sid_bv, exit_code_var) << eol;
}

// btor2::Encoder::declare_states ----------------------------------------------

void Encoder::declare_states ()
{
  if (verbose)
    formula << comment_section("state variable declarations");

  declare_accu();
  declare_mem();
  declare_sb_adr();
  declare_sb_val();
  declare_sb_full();
  declare_stmt();
  declare_block();
  declare_halt();

  declare_heap();
  declare_exit_flag();
  declare_exit_code();
}

// btor2::Encoder::declare_thread ----------------------------------------------

void Encoder::declare_thread ()
{
  if (verbose)
    formula << thread_comment;

  nids_thread.reserve(num_threads);

  iterate_threads([&] () {
    formula << input(nids_thread.emplace_back(nid()), sid_bool, thread_var());
  });

  formula << eol;
}

// btor2::Encoder::declare_flush -----------------------------------------------

void Encoder::declare_flush ()
{
  if (verbose)
    formula << flush_comment;

  nids_flush.reserve(num_threads);

  iterate_threads([&] () {
    formula << input(nids_flush.emplace_back(nid()), sid_bool, flush_var());
  });

  formula << eol;
}

// btor2::Encoder::declare_inputs ----------------------------------------------

void Encoder::declare_inputs ()
{
  if (verbose)
    formula << comment_section("input variable declarations");

  declare_thread();
  declare_flush();
}

// btor2::Encoder::define_exec -------------------------------------------------

void Encoder::define_exec ()
{
  if (verbose)
    formula << exec_comment;

  nids_exec.resize(num_threads);

  iterate_programs([this] (const Program & program) {
    nids_exec[thread].reserve(program.size());

    for (pc = 0; pc < program.size(); pc++)
      formula <<
        land(
          nids_exec[thread].emplace_back(nid()),
          sid_bool,
          nids_stmt[thread][pc],
          nids_thread[thread],
          exec_var());

    formula << eol;
  });
}

// btor2::Encoder::define_check ------------------------------------------------

void Encoder::define_check ()
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
          std::vector<std::string> args;
          args.reserve(blocks.size());

          for (const auto & [t, nid_block] : blocks)
            args.push_back(nid_block);

          formula << land(node, sid_bool, args, check_var(c));

          nids_check.emplace_hint(nids_check.end(), c, nid(-1));
        }
      else
        {
          nids_check.emplace_hint(nids_check.end(), c, blocks.begin()->second);
        }
    }

  formula << eol;
}

// btor2::Encoder::define_transitions ------------------------------------------

void Encoder::define_transitions ()
{
  if (verbose)
    formula << comment_section("transition variable definitions");

  define_exec();
  define_check();
}

// btor2::Encoder::define_state_bv ---------------------------------------------

void Encoder::define_state_bv (Instruction::Type type,
                               const std::string & nid_state,
                               const std::string sym)
{
  const Program & program = (*programs)[thread];
  const std::vector<std::string> & exec = nids_exec[thread];

  formula << init(nid(), sid_bv, nid_state, nids_const[0]);

  std::string nid_next = nid_state;
  for (pc = 0; pc < program.size(); pc++)
    {
      const Instruction & op = program[pc];

      if (op.type() & type)
        formula <<
          ite(
            nid_next = nid(),
            sid_bv,
            exec[pc],
            op.encode(*this),
            nid_next,
            verbose ? debug_symbol(thread, pc) : "");
    }

  formula << next(nid(), sid_bv, nid_state, nid_next, sym) << eol;
}

// btor2::Encoder::define_accu -------------------------------------------------

void Encoder::define_accu ()
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

// btor2::Encoder::define_mem --------------------------------------------------

void Encoder::define_mem ()
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

// btor2::Encoder::define_sb_adr -----------------------------------------------

void Encoder::define_sb_adr ()
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

// btor2::Encoder::define_sb_val -----------------------------------------------

void Encoder::define_sb_val ()
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

// btor2::Encoder::define_sb_full ----------------------------------------------

void Encoder::define_sb_full ()
{
  if (verbose)
    formula << sb_full_comment;

  iterate_programs([this] (const Program & program) {
    formula << init(nid(), sid_bool, nids_sb_full[thread], nid_false);

    std::vector<std::string> args;

    std::string nid_next = nids_sb_full[thread];

    for (pc = 0; pc < program.size(); pc++)
      if (program[pc].type() & Instruction::Type::write)
        args.push_back(nids_exec[thread][pc]);

    if (!args.empty())
      {
        args.push_back(nids_sb_full[thread]);
        formula << lor(node, sid_bool, args);
        nid_next = nid(-1);
      }

    formula <<
      ite(nid_next = nid(), sid_bool, nids_flush[thread], nid_false, nid_next) <<
      next(nid(), sid_bool, nids_sb_full[thread], nid_next, sb_full_var()) <<
      eol;
  });
}

// btor2::Encoder::define_stmt -------------------------------------------------

void Encoder::define_stmt ()
{
  if (verbose)
    formula << stmt_comment;

  iterate_programs([this] (const Program & program) {
    std::unordered_map<word_t, std::string> nid_jmp; // nids of jump conditions

    for (pc = 0; pc < program.size(); pc++)
      {
        std::string nid_next = nid();
        std::string nid_exec = nids_exec[thread][pc];
        std::string nid_stmt = nids_stmt[thread][pc];

        // init
        formula <<
          init(nid_next, sid_bool, nid_stmt, pc ? nid_false : nid_true);

        // add statement reactivation
        formula <<
          land(
            nid_next = nid(),
            sid_bool,
            nid_stmt,
            lnot(nid_exec),
            verbose ? debug_symbol(thread, pc) : "");

        // add activation by predecessor's execution
        for (word_t prev : program.predecessors.at(pc))
          {
            nid_exec = nids_exec[thread][prev];

            const Instruction & pred = program[prev];

            // predecessor is a conditional jump
            if (pred.is_jump() && &pred.symbol() != &Instruction::Jmp::symbol)
              {
                std::string nid_cond =
                  lookup(
                    nid_jmp,
                    prev,
                    [this, &pred] { return pred.encode(*this); });

                // add negated condition if preceding jump failed
                if (prev == pc - 1 && pred.arg() != pc)
                  nid_cond = lnot(nid_cond);

                // add conjunction of execution variable & jump condition
                formula <<
                  land(nid_exec = nid(), sid_bool, nid_exec, nid_cond);
              }

            // add predecessors activation
            formula <<
              ite(
                nid_next = nid(),
                sid_bool,
                nids_stmt[thread][prev],
                nid_exec,
                nid_next,
                verbose ? debug_symbol(thread, prev) : "");
          }

        formula << next(nid(), sid_bool, nid_stmt, nid_next, stmt_var()) << eol;
      }
  });
}

// btor2::Encoder::define_block ------------------------------------------------

void Encoder::define_block ()
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
          std::string & nid_check = nids_check_it++->second;

          auto nid_block_it = nids_block_it++->second.begin();

          for (const auto & [t, pcs] : threads)
            {
              std::string & nid_block = nid_block_it++->second;

              std::vector<std::string> args;
              args.reserve(pcs.size() + 1);

              for (const auto & p : pcs)
                args.push_back(nids_exec[t][p]);

              args.push_back(nid_block);

              std::string prev;

              formula <<
                init(nid(), sid_bool, nid_block, nid_false) <<
                lor(node, sid_bool, args) <<
                ite(prev = nid(), sid_bool, nid_check, nid_false, nid(-1)) <<
                next(nid(), sid_bool, nid_block, prev, block_var(s, t)) <<
                eol;
            }
        }
    }
}

// btor2::Encoder::define_halt -------------------------------------------------

void Encoder::define_halt ()
{
  if (halt_pcs.empty())
    return;

  if (verbose)
    formula << halt_comment;

  for (const auto & [t, pcs] : halt_pcs)
    {
      std::vector<std::string> args;

      args.reserve(pcs.size() + 1);

      for (const word_t p : pcs)
        args.push_back(nids_exec[t][p]);

      args.push_back(nids_halt[t]);

      formula <<
        init(nid(), sid_bool, nids_halt[t], nid_false) <<
        lor(node, sid_bool, args) <<
        next(
          nid(),
          sid_bool,
          nids_halt[t],
          nids_halt_next.emplace_hint(nids_halt_next.end(), t, nid(-1))->second,
          halt_var(t)) <<
        eol;
    }
}

// btor2::Encoder::define_heap -------------------------------------------------

void Encoder::define_heap ()
{
  if (verbose)
    formula << heap_comment;

  // init
  if (mmap && !mmap->empty())
    {
      std::string nid_init = nid();

      formula << state(nid_init, sid_heap, "mmap");

      for (const auto & [adr, val] : *mmap)
        formula <<
          write(
            nid_init = nid(),
            sid_heap,
            nid_init,
            nids_const[adr],
            nids_const[val]);

      formula << init(nid(), sid_heap, nid_heap, nid_init);
    }

  // next
  update = State::heap;

  std::string nid_next = nid_heap;

  iterate_programs([this, &nid_next] (const Program & program) {
    // store buffer flush
    std::string nid_flush = nid();

    formula <<
      write(
        nid_flush,
        sid_heap,
        nid_heap,
        nids_sb_adr[thread],
        nids_sb_val[thread]) <<
      ite(
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
            ite(
              nid_next = nid(),
              sid_heap,
              nids_exec[thread][pc],
              op.encode(*this),
              nid_next,
              verbose ? debug_symbol(thread, pc) : "");
      }
  });

  formula << next(nid(), sid_heap, nid_heap, nid_next, heap_sym) << eol;
}

// btor2::Encoder::define_exit_flag --------------------------------------------

void Encoder::define_exit_flag ()
{
  if (halt_pcs.empty() && exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_flag_comment;

  formula << init(nid(), sid_bool, nid_exit_flag, nid_false);

  std::vector<std::string> args({nid_exit_flag});

  std::string nid_next = nid_exit_flag;

  if (!halt_pcs.empty())
    {
      if (nids_halt.size() > 1)
        {
          std::vector<std::string> halt;
          halt.reserve(nids_halt_next.size());

          for (const auto & it : nids_halt_next)
            halt.push_back(it.second);

          formula << land(node, sid_bool, halt);

          args.push_back(nid(-1));
        }
      else
        {
          args.push_back(nids_halt_next.begin()->second);
        }
    }

  if (!exit_pcs.empty())
    for (const auto & [t, pcs] : exit_pcs)
      for (const auto & p : pcs)
        args.push_back(nids_exec[t][p]);

  if (args.size() > 1)
    {
      formula << lor(node, sid_bool, args);
      nid_next = std::to_string(node - 1);
    }

  formula
    << next(nid(), sid_bool, nid_exit_flag, nid_next, exit_flag_sym)
    << eol;
}

// btor2::Encoder::define_exit_code --------------------------------------------

void Encoder::define_exit_code ()
{
  if (verbose)
    formula << exit_code_comment;

  formula << init(nid(), sid_bv, nid_exit_code, nids_const[0]);

  std::string nid_next = nid_exit_code;

  for (const auto & [t, pcs] : exit_pcs)
    for (const auto & p : pcs)
      formula <<
        ite(
          nid_next = nid(),
          sid_bv,
          nids_exec[t][p],
          (*programs)[t][p].encode(*this),
          nid_next,
          verbose ? debug_symbol(t, p) : "");

  formula
    << next(nid(), sid_bv, nid_exit_code, nid_next, exit_code_var)
    << eol;
}

// btor2::Encoder::define_states -----------------------------------------------

void Encoder::define_states ()
{
  if (verbose)
    formula << comment_section("state variable definitions");

  define_accu();
  define_mem();
  define_sb_adr();
  define_sb_val();
  define_sb_full();
  define_stmt();
  define_block();
  define_halt();

  define_heap();
  define_exit_flag();
  define_exit_code();
}

// btor2::Encoder::define_scheduling_constraints -------------------------------

void Encoder::define_scheduling_constraints ()
{
  if (verbose)
    formula << comment_section("scheduling constraints");

  std::vector<std::string> variables;
  variables.reserve(num_threads * 2 + 1);

  variables.insert(variables.end(), nids_thread.begin(), nids_thread.end());
  variables.insert(variables.end(), nids_flush.begin(), nids_flush.end());

  if (!nid_exit_flag.empty())
    variables.push_back(nid_exit_flag);

  formula <<
    (use_sinz_constraint
      ? card_constraint_sinz(node, sid_bool, variables)
      : card_constraint_naive(node, sid_bool, variables)) <<
    eol;
}

// btor2::Encoder::define_store_buffer_constraints -----------------------------

void Encoder::define_store_buffer_constraints ()
{
  if (verbose)
    formula << comment_section("store buffer constraints");

  iterate_threads([this] {
    if (flush_pcs.find(thread) != flush_pcs.end())
      {
        std::string nid_or;

        if (flush_pcs[thread].size() > 1)
          {
            std::vector<std::string> stmts;

            stmts.reserve(flush_pcs[thread].size());

            std::transform(
              flush_pcs[thread].begin(),
              flush_pcs[thread].end(),
              back_inserter(stmts),
              [this] (const word_t p) { return nids_stmt[thread][p]; });

            formula << lor(node, sid_bool, stmts);

            nid_or = nid(-1);
          }
        else
          {
            nid_or = nids_stmt[thread][flush_pcs[thread].front()];
          }

        formula <<
          implies(nid(), sid_bool, nid_or, lnot(nids_thread[thread])) <<
          ite(
            nid(),
            sid_bool,
            nids_sb_full[thread],
            nid(-1),
            lnot(nids_flush[thread]));
      }
    else
      formula <<
        implies(
          nid(),
          sid_bool,
          lnot(nids_sb_full[thread]),
          lnot(nids_flush[thread]));

    formula << constraint(node, flush_var()) << eol;
  });
}

// btor2::Encoder::define_checkpoint_constraints -------------------------------

void Encoder::define_checkpoint_constraints ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << comment_section("checkpoint constraints");

  for (const auto & [c, threads] : nids_block)
    {
      // TODO: ignore single-threaded checkpoints -> see gitlab issue #65
      if (threads.size() > 1)
        {
          std::string not_check = lnot(nids_check[c]);

          for (const auto & [t, nid_block] : threads)
            {
              std::string prev = nid();

              formula
                << land(prev, sid_bool, nid_block, not_check)
                << implies(prev = nid(), sid_bool, prev, lnot(nids_thread[t]))
                << constraint(node, block_var(c, t))
                << eol;
            }
        }
    }
}

// btor2::Encoder::define_halt_constraints -------------------------------------

void Encoder::define_halt_constraints ()
{
  if (halt_pcs.empty())
    return;

  if (verbose)
    formula << comment_section("halt constraints");

  for (const auto & [t, nid_halt] : nids_halt)
    formula
      << implies(nid(), sid_bool, nid_halt, lnot(nids_thread[t]))
      << constraint(node, halt_var(t))
      << eol;
}

// btor2::Encoder::define_constraints ------------------------------------------

void Encoder::define_constraints ()
{
  define_scheduling_constraints();
  define_store_buffer_constraints();
  define_checkpoint_constraints();
  define_halt_constraints();
}

// btor2::Encoder::define_bound ------------------------------------------------

void Encoder::define_bound ()
{
  if (verbose)
    formula << comment_section("bound");

  // step counter
  if (verbose)
    formula << comment("step counter") << eol;

  std::string nid_prev;
  std::string nid_ctr = nid();

  formula
    << state(nid_ctr, sid_bv, "k")
    << init(nid(), sid_bv, nid_ctr, nids_const[0])
    << add(nid_prev = nid(), sid_bv, nids_const[1], nid_ctr)
    << next(nid(), sid_bv, nid_ctr, nid_prev)
    << eol;

  // bound
  if (verbose)
    formula << comment("bound (" + std::to_string(bound) + ")") << eol;

  formula
    << eq(nid_prev = nid(), sid_bool, nids_const[bound], nid_ctr)
    << bad(nid(), nid_prev);
}

// btor2::Encoder::encode ------------------------------------------------------

void Encoder::encode ()
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

std::string Encoder::encode (const Instruction::Load & l)
{
  return load(l.arg, l.indirect);
}

std::string Encoder::encode (const Instruction::Store & s)
{
  switch (update)
    {
    case State::sb_adr:
      return s.indirect ? load(s.arg) : nids_const[s.arg];

    case State::sb_val:
      return nids_accu[thread];

    default: throw std::runtime_error("illegal state update");
    }
}

std::string Encoder::encode (const Instruction::Fence & f [[maybe_unused]])
{
  assert(false);
  return "";
}

std::string Encoder::encode (const Instruction::Add & a)
{
  std::string nid_add = load(a.arg, a.indirect);

  formula << add(nid_add = nid(), sid_bv, nids_accu[thread], nid_add);

  return nid_add;
}

std::string Encoder::encode (const Instruction::Addi & a)
{
  std::string nid_addi = nids_const[a.arg];

  formula << add(nid_addi = nid(), sid_bv, nids_accu[thread], nid_addi);

  return nid_addi;
}

std::string Encoder::encode (const Instruction::Sub & s)
{
  std::string nid_sub = load(s.arg, s.indirect);

  formula << sub(nid_sub = nid(), sid_bv, nids_accu[thread], nid_sub);

  return nid_sub;
}

std::string Encoder::encode (const Instruction::Subi & s)
{
  std::string nid_subi = nids_const[s.arg];

  formula << sub(nid_subi = nid(), sid_bv, nids_accu[thread], nid_subi);

  return nid_subi;
}

std::string Encoder::encode (const Instruction::Mul & m)
{
  std::string nid_mul = load(m.arg, m.indirect);

  formula << mul(nid_mul = nid(), sid_bv, nids_accu[thread], nid_mul);

  return nid_mul;
}

std::string Encoder::encode (const Instruction::Muli & m)
{
  std::string nid_muli = nids_const[m.arg];

  formula << mul(nid_muli = nid(), sid_bv, nids_accu[thread], nid_muli);

  return nid_muli;
}

std::string Encoder::encode (const Instruction::Cmp & c)
{
  std::string nid_sub = load(c.arg, c.indirect);

  formula << sub(nid_sub = nid(), sid_bv, nids_accu[thread], nid_sub);

  return nid_sub;
}

std::string Encoder::encode (const Instruction::Jmp & j [[maybe_unused]])
{
  return "";
}

std::string Encoder::encode (const Instruction::Jz & j [[maybe_unused]])
{
  std::string nid_jz = nid();

  formula << eq(nid_jz, sid_bool, nids_accu[thread], nids_const[0]);

  return nid_jz;
}

std::string Encoder::encode (const Instruction::Jnz & j [[maybe_unused]])
{
  std::string nid_jnz = nid();

  formula << ne(nid_jnz, sid_bool, nids_accu[thread], nids_const[0]);

  return nid_jnz;
}

std::string Encoder::encode (const Instruction::Js & j [[maybe_unused]])
{
  std::string nid_js = nid();

  formula << slice(nid_js, sid_bool, nids_accu[thread], msb, msb);

  return nid_js;
}

std::string Encoder::encode (const Instruction::Jns & j [[maybe_unused]])
{
  std::string nid_jns = nid();

  formula << slice(nid_jns, sid_bool, nids_accu[thread], msb, msb);

  return lnot(nid_jns);
}

std::string Encoder::encode (const Instruction::Jnzns & j [[maybe_unused]])
{
  std::string nid_nz = nid();

  formula << ne(nid_nz, sid_bool, nids_accu[thread], nids_const[0]);

  std::string nid_nzns = nid();

  formula
    << slice(nid_nzns, sid_bool, nids_accu[thread], msb, msb)
    << land(nid_nzns = nid(), sid_bool, nid_nz, lnot(nid_nzns));

  return nid_nzns;
}

std::string Encoder::encode (const Instruction::Mem & m)
{
  return load(m.arg, m.indirect);
}

std::string Encoder::encode (const Instruction::Cas & c)
{
  std::string nid_cas =
    lookup(
      c.indirect ? nids_cas_indirect[thread] : nids_cas[thread],
      c.arg,
      [this, &c] {
        std::string nid_cond = load(c.arg);

        formula << eq(nid_cond = nid(), sid_bool, nids_mem[thread], nid_cond);

        return nid_cond;
      });

  switch (update)
    {
    case State::accu:
        {
          formula <<
            ite(
              nid_cas = nid(),
              sid_bv,
              nid_cas,
              nids_const[1],
              nids_const[0]);

          break;
        }
    case State::heap:
        {
          std::string nid_write = nid();

          formula <<
            write(
              nid_write,
              sid_heap,
              nid_heap,
              c.indirect
                ? load(c.arg)
                : nids_const[c.arg],
              nids_accu[thread]) <<
            ite(
              nid_cas = nid(),
              sid_heap,
              nid_cas,
              nid_write,
              nid_heap);

          break;
        }

    default: throw std::runtime_error("illegal state update");
    }

  return nid_cas;
}

std::string Encoder::encode (const Instruction::Check & s [[maybe_unused]])
{
  assert(false);
  return "";
}

std::string Encoder::encode (const Instruction::Halt & h [[maybe_unused]])
{
  assert(false);
  return "";
}

std::string Encoder::encode (const Instruction::Exit & e [[maybe_unused]])
{
  return nids_const[e.arg];
}

} // namespace ConcuBinE::btor2
