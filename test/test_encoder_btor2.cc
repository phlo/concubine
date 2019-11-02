#include "test_encoder.hh"

#include <functional>

#include "btor2.hh"
#include "btormc.hh"

namespace ConcuBinE::test {

//==============================================================================
// helper
//==============================================================================

// TODO remove - debug only
void evaluate (const std::string & formula)
{
  BtorMC btormc;
  std::cout << "running btormc..." << eol;
  btormc.sat(formula);
}

//==============================================================================
// btor2::Encoder tests
//==============================================================================

using E = btor2::Encoder;

void init_declarations (E & encoder, const bool clear_formula = true)
{
  encoder.declare_sorts();
  encoder.declare_constants();

  encoder.thread = encoder.pc = 0;

  if (clear_formula)
    encoder.formula.str("");
}

void init_definitions (E & encoder, const bool clear_formula = true)
{
  init_declarations(encoder, clear_formula);

  encoder.declare_states();
  encoder.declare_inputs();

  encoder.thread = encoder.pc = 0;

  if (clear_formula)
    encoder.formula.str("");
}

void init_state_definitions (E & encoder, const bool clear_formula = true)
{
  init_definitions(encoder, clear_formula);

  encoder.define_transitions();

  encoder.thread = encoder.pc = 0;

  if (clear_formula)
    encoder.formula.str("");
}

std::string expected_load (E & encoder,
                           btor2::nid_t & nid,
                           const word_t address)
{
  std::ostringstream s;
  const word_t & thread = encoder.thread;

  if (!thread)
    {
      s <<
        btor2::read(
          encoder.nids_read[address],
          encoder.sid_bv,
          encoder.nid_heap,
          encoder.nids_const[address]);
      nid++;
    }

  s <<
    btor2::eq(
      encoder.nids_eq_sb_adr_adr[thread][address],
      encoder.sid_bool,
      encoder.nids_sb_adr[thread],
      encoder.nids_const[address]);
  nid++;
  s <<
    btor2::land(
      std::to_string(nid),
      encoder.sid_bool,
      encoder.nids_sb_full[thread],
      encoder.nids_eq_sb_adr_adr[thread][address]);
  nid++;
  s <<
    btor2::ite(
      encoder.nids_load[thread][address],
      encoder.sid_bv,
      std::to_string(nid - 1),
      encoder.nids_sb_val[thread],
      encoder.nids_read[address]);
  nid++;

  return s.str();
}

std::string expected_load_indirect (E & encoder,
                                    btor2::nid_t & nid,
                                    const word_t address)
{
  std::ostringstream s;
  const word_t & thread = encoder.thread;

  if (!thread)
    {
      s <<
        btor2::read(
          encoder.nids_read[address],
          encoder.sid_bv,
          encoder.nid_heap,
          encoder.nids_const[address]);
      nid++;
    }

  s <<
    btor2::eq(
      encoder.nids_eq_sb_adr_adr[thread][address],
      encoder.sid_bool,
      encoder.nids_sb_adr[thread],
      encoder.nids_const[address]);
  nid++;

  if (!thread)
    {
      s <<
        btor2::read(
          encoder.nids_read_indirect[address],
          encoder.sid_bv,
          encoder.nid_heap,
          encoder.nids_read[address]);
      nid++;
    }

  s <<
    btor2::eq(
      std::to_string(nid),
      encoder.sid_bool,
      encoder.nids_sb_adr[thread],
      encoder.nids_read[address]);
  nid++;

  std::string nid_ite_eq_sb_adr_read_adr = std::to_string(nid);

  s <<
    btor2::ite(
      nid_ite_eq_sb_adr_read_adr,
      encoder.sid_bv,
      std::to_string(nid - 1),
      encoder.nids_sb_val[thread],
      encoder.nids_read_indirect[address]);
  nid++;

  if (!address || thread)
    {
      s <<
        btor2::read(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nid_heap,
          encoder.nids_sb_val[thread]);
      nid++;
    }

  s <<
    btor2::eq(
      std::to_string(nid),
      encoder.sid_bool,
      encoder.nids_sb_val[thread],
      encoder.nids_const[address]);
  nid++;
  s <<
    btor2::ite(
      std::to_string(nid),
      encoder.sid_bv,
      std::to_string(nid - 1),
      encoder.nids_sb_val[thread],
      encoder.nids_read_sb_val[thread]);
  nid++;
  s <<
    btor2::ite(
      std::to_string(nid),
      encoder.sid_bv,
      encoder.nids_eq_sb_adr_adr[thread][address],
      std::to_string(nid - 1),
      nid_ite_eq_sb_adr_read_adr);
  nid++;
  s <<
    btor2::ite(
      encoder.nids_load_indirect[thread][address],
      encoder.sid_bv,
      encoder.nids_sb_full[thread],
      std::to_string(nid - 1),
      encoder.nids_read_indirect[address]);
  nid++;

  return s.str();
}

// btor2::Encoder::load ========================================================

TEST(btor2_Encoder, load)
{
  auto encoder = create<E>(dummy(2));

  init_definitions(encoder);

  btor2::nid_t nid = encoder.node;
  word_t & thread = encoder.thread;
  word_t address = 0;

  ASSERT_EQ(encoder.nids_load[thread][address], encoder.load(address));
  ASSERT_EQ(expected_load(encoder, nid, address), encoder.formula.str());
  encoder.formula.str("");

  // another load with the same address
  ASSERT_EQ(encoder.nids_load[thread][address], encoder.load(address));
  ASSERT_EQ("", encoder.formula.str());

  // another load with a different address
  address = 1;
  ASSERT_EQ(encoder.nids_load[thread][address], encoder.load(address));
  ASSERT_EQ(expected_load(encoder, nid, address), encoder.formula.str());
  encoder.formula.str("");

  // another load from a different thread
  thread = 1;
  ASSERT_EQ(encoder.nids_load[thread][address], encoder.load(address));
  ASSERT_EQ(expected_load(encoder, nid, address), encoder.formula.str());
}

TEST(btor2_Encoder, load_indirect)
{
  auto encoder = create<E>(dummy(2));

  init_definitions(encoder);

  btor2::nid_t nid = encoder.node;
  word_t & thread = encoder.thread;
  word_t address = 0;

  ASSERT_EQ(
    encoder.nids_load_indirect[thread][address],
    encoder.load(address, true));
  ASSERT_EQ(
    expected_load_indirect(encoder, nid, address),
    encoder.formula.str());
  encoder.formula.str("");

  // another load with the same address
  ASSERT_EQ(
    encoder.nids_load_indirect[thread][address],
    encoder.load(address, true));
  ASSERT_EQ("", encoder.formula.str());

  // another load with a different address
  address = 1;
  ASSERT_EQ(
    encoder.nids_load_indirect[thread][address],
    encoder.load(address, true));
  ASSERT_EQ(
    expected_load_indirect(encoder, nid, address),
    encoder.formula.str());
  encoder.formula.str("");

  // another load from a different thread
  thread = 1;
  ASSERT_EQ(
    encoder.nids_load_indirect[thread][address],
    encoder.load(address, true));
  ASSERT_EQ(
    expected_load_indirect(encoder, nid, address),
    encoder.formula.str());
}

// btor2::Encoder::declare_sorts ===============================================

TEST(btor2_Encoder, declare_sorts)
{
  auto encoder = create<E>();

  encoder.declare_sorts();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("sorts");

    s << encoder.sid_bool << " sort bitvec 1\n"
      << encoder.sid_bv << " sort bitvec 16\n"
      << encoder.sid_heap << " sort array 2 2\n"
      << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_sorts();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::declare_constants ===========================================

TEST(btor2_Encoder, declare_constants)
{
  auto encoder = create<E>(lst(prog("ADD 0"), prog("ADD 1"), prog("ADD 2")));

  encoder.declare_sorts();
  encoder.formula.str("");

  encoder.declare_constants();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("constants");

    s << encoder.nid_false << " zero 1\n"
      << encoder.nid_true << " one 1\n"
      << eol
      << encoder.nids_const[0] << " zero 2\n"
      << encoder.nids_const[1] << " one 2\n"
      << encoder.nids_const[2] << " constd 2 2\n"
      << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);

  encoder.declare_sorts();
  encoder.formula.str("");

  verbose = false;
  encoder.declare_constants();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::define_mmap =================================================

TEST(btor2_Encoder, define_mmap)
{
  auto encoder = create<E>(lst(), mmap({{0, 0}, {1, 0}}));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_mmap();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("memory map");

    s << btor2::state(std::to_string(nid++), encoder.sid_heap, "mmap");

    for (const auto & [adr, val] : *encoder.mmap)
      {
        s <<
          btor2::write(
            std::to_string(nid),
            encoder.sid_heap,
            std::to_string(nid - 1),
            encoder.nids_const[adr],
            encoder.nids_const[val]);
        nid++;
      }

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_mmap();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_mmap_empty)
{
  auto encoder = create<E>();

  encoder.define_mmap();

  ASSERT_EQ("", encoder.formula.str());
}

// btor2::Encoder::declare_accu ================================================

TEST(btor2_Encoder, declare_accu)
{
  auto encoder = create<E>(dummy(3));

  init_declarations(encoder);

  encoder.declare_accu();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.accu_comment;

    encoder.iterate_threads([&encoder, &s] {
      s <<
        btor2::state(
          encoder.nids_accu[encoder.thread],
          encoder.sid_bv,
          encoder.accu_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_declarations(encoder);

  verbose = false;
  encoder.declare_accu();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::declare_mem =================================================

TEST(btor2_Encoder, declare_mem)
{
  auto encoder = create<E>(dummy(3));

  init_declarations(encoder);

  encoder.declare_mem();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.mem_comment;

    encoder.iterate_threads([&encoder, &s] {
      s <<
        btor2::state(
          encoder.nids_mem[encoder.thread],
          encoder.sid_bv,
          encoder.mem_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_declarations(encoder);

  verbose = false;
  encoder.declare_mem();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::declare_sb_adr ==============================================

TEST(btor2_Encoder, declare_sb_adr)
{
  auto encoder = create<E>(dummy(3));

  init_declarations(encoder);

  encoder.declare_sb_adr();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.sb_adr_comment;

    encoder.iterate_threads([&encoder, &s] {
      s <<
        btor2::state(
          encoder.nids_sb_adr[encoder.thread],
          encoder.sid_bv,
          encoder.sb_adr_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_declarations(encoder);

  verbose = false;
  encoder.declare_sb_adr();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::declare_sb_val ==============================================

TEST(btor2_Encoder, declare_sb_val)
{
  auto encoder = create<E>(dummy(3));

  init_declarations(encoder);

  encoder.declare_sb_val();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.sb_val_comment;

    encoder.iterate_threads([&encoder, &s] {
      s <<
        btor2::state(
          encoder.nids_sb_val[encoder.thread],
          encoder.sid_bv,
          encoder.sb_val_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_declarations(encoder);

  verbose = false;
  encoder.declare_sb_val();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::declare_sb_full =============================================

TEST(btor2_Encoder, declare_sb_full)
{
  auto encoder = create<E>(dummy(3));

  init_declarations(encoder);

  encoder.declare_sb_full();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.sb_full_comment;

    encoder.iterate_threads([&encoder, &s] {
      s <<
        btor2::state(
          encoder.nids_sb_full[encoder.thread],
          encoder.sid_bool,
          encoder.sb_full_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_declarations(encoder);

  verbose = false;
  encoder.declare_sb_full();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::declare_stmt ================================================

TEST(btor2_Encoder, declare_stmt)
{
  auto encoder = create<E>(dummy(3, 3));

  init_declarations(encoder);

  encoder.declare_stmt();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.stmt_comment;

    encoder.iterate_programs([&encoder, &s] (const Program & program) {
      word_t & thread = encoder.thread;
      word_t & pc = encoder.pc;

      for (pc = 0; pc < program.size(); pc++)
        s <<
          btor2::state(
            encoder.nids_stmt[thread][pc],
            encoder.sid_bool,
            encoder.stmt_var());

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_declarations(encoder);

  verbose = false;
  encoder.declare_stmt();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::declare_block ===============================================

TEST(btor2_Encoder, declare_block)
{
  const auto code =
    "CHECK 0\n"
    "CHECK 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  init_declarations(encoder);

  encoder.declare_block();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.block_comment;

    for (const auto & [c, threads] : encoder.nids_block)
      {
        for (const auto & [t, nid] : threads)
          s << btor2::state(nid, encoder.sid_bool, encoder.block_var(c, t));

        s << eol;
      }

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_declarations(encoder);

  verbose = false;
  encoder.declare_block();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, declare_block_empty)
{
  auto encoder = create<E>();

  encoder.declare_block();

  ASSERT_EQ("", encoder.formula.str());
}

// btor2::Encoder::declare_halt ================================================
TEST(btor2_Encoder, declare_halt)
{
  auto encoder = create<E>(dummy(3));

  init_declarations(encoder);

  encoder.declare_halt();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.halt_comment;

    encoder.iterate_threads([&encoder, &s] {
      s <<
        btor2::state(
          encoder.nids_halt[encoder.thread],
          encoder.sid_bool,
          encoder.halt_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_declarations(encoder);

  verbose = false;
  encoder.declare_halt();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, declare_halt_empty)
{
  auto encoder = create<E>();

  encoder.declare_halt();

  ASSERT_EQ("", encoder.formula.str());
}

// btor2::Encoder::declare_heap ================================================

TEST(btor2_Encoder, declare_heap)
{
  auto encoder = create<E>();

  init_declarations(encoder);

  encoder.declare_heap();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.heap_comment;

    s << encoder.nid_heap + " state 3 heap\n\n";

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_declarations(encoder);

  verbose = false;
  encoder.declare_heap();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::declare_exit_flag ===========================================

TEST(btor2_Encoder, declare_exit_flag)
{
  auto encoder = create<E>(lst(prog("EXIT 1")));

  init_declarations(encoder);

  encoder.declare_exit_flag();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.exit_flag_comment;

    s << encoder.nid_exit_flag + " state 1 exit\n\n";

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_declarations(encoder);

  verbose = false;
  encoder.declare_exit_flag();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, declare_exit_flag_empty)
{
  auto encoder = create<E>();

  encoder.declare_exit_flag();

  ASSERT_EQ("", encoder.formula.str());
}

// btor2::Encoder::declare_exit_code ===========================================

TEST(btor2_Encoder, declare_exit_code)
{
  auto encoder = create<E>(lst(prog("EXIT 1")));

  init_declarations(encoder);

  encoder.declare_exit_code();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.exit_code_comment;

    s << encoder.nid_exit_code + " state 2 exit-code\n\n";

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_declarations(encoder);

  verbose = false;
  encoder.declare_exit_code();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::declare_thread ==============================================

TEST(btor2_Encoder, declare_thread)
{
  auto encoder = create<E>(dummy(3));

  init_declarations(encoder);

  encoder.declare_thread();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.thread_comment;

    encoder.iterate_threads([&encoder, &s] {
      s <<
        btor2::input(
          encoder.nids_thread[encoder.thread],
          encoder.sid_bool,
          encoder.thread_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_declarations(encoder);

  verbose = false;
  encoder.declare_thread();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::declare_flush ===============================================

TEST(btor2_Encoder, declare_flush)
{
  auto encoder = create<E>(dummy(3));

  init_declarations(encoder);

  encoder.declare_flush();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.flush_comment;

    encoder.iterate_threads([&encoder, &s] {
      s <<
        btor2::input(
          encoder.nids_flush[encoder.thread],
          encoder.sid_bool,
          encoder.flush_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_declarations(encoder);

  verbose = false;
  encoder.declare_flush();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::define_exec =================================================

TEST(btor2_Encoder, define_exec)
{
  auto encoder = create<E>(dummy(3, 3));

  init_definitions(encoder);

  encoder.define_exec();

  auto expected = [&encoder] {
    std::ostringstream s;

    if (verbose)
      s << encoder.exec_comment;

    encoder.iterate_programs([&encoder, &s] (const Program & program) {
      word_t & thread = encoder.thread;
      word_t & pc = encoder.pc;

      for (pc = 0; pc < program.size(); pc++)
        s <<
          btor2::land(
            encoder.nids_exec[thread][pc],
            encoder.sid_bool,
            encoder.nids_stmt[thread][pc],
            encoder.nids_thread[thread],
            encoder.exec_var());

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_definitions(encoder);

  verbose = false;
  encoder.define_exec();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::define_check ================================================

TEST(btor2_Encoder, define_check)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  init_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_check();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.check_comment;

    std::vector<std::string> blocks;

    for (const auto & [c, threads] : encoder.nids_block)
      for (const auto & [t, nid_block] : threads)
        blocks.push_back(nid_block);

    s << btor2::land(nid, encoder.sid_bool, blocks, encoder.check_var(1));
    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_check();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_check_empty)
{
  auto encoder = create<E>();

  encoder.define_check();

  ASSERT_EQ("", encoder.formula.str());
}

// btor2::Encoder::define_accu =================================================

TEST(btor2_Encoder, define_accu)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_accu();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.accu_comment;

    encoder.iterate_threads([&encoder, &nid, &s] {
      word_t & thread = encoder.thread;
      word_t & pc = encoder.pc = 0;
      word_t address = 1;

      // init
      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_accu[thread],
          encoder.nids_const[0]);
      nid++;

      // LOAD
      if (!thread)
        {
          s <<
            btor2::read(
              encoder.nids_read[address],
              encoder.sid_bv,
              encoder.nid_heap,
              encoder.nids_const[address]);
          nid++;
        }

      s <<
        btor2::eq(
          encoder.nids_eq_sb_adr_adr[thread][address],
          encoder.sid_bool,
          encoder.nids_sb_adr[thread],
          encoder.nids_const[address]);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_sb_full[thread],
          encoder.nids_eq_sb_adr_adr[thread][address]);
      nid++;
      s <<
        btor2::ite(
          encoder.nids_load[thread][address],
          encoder.sid_bv,
          std::to_string(nid - 1),
          encoder.nids_sb_val[thread],
          encoder.nids_read[address]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_exec[thread][pc],
          encoder.nids_load[thread][address],
          encoder.nids_accu[thread],
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;

      // ADD
      pc = 2;

      s <<
        btor2::add(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_accu[thread],
          encoder.nids_load[thread][address]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;

      // ADDI
      pc = 3;

      s <<
        btor2::add(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_accu[thread],
          encoder.nids_const[1]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;

      // SUB
      pc = 4;

      s <<
        btor2::sub(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_accu[thread],
          encoder.nids_load[thread][address]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;

      // SUBI
      pc = 5;

      s <<
        btor2::sub(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_accu[thread],
          encoder.nids_const[1]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;

      // MUL
      pc = 6;

      s <<
        btor2::mul(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_accu[thread],
          encoder.nids_load[thread][address]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;

      // MULI
      pc = 7;

      s <<
        btor2::mul(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_accu[thread],
          encoder.nids_const[1]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;

      // CMP
      pc = 8;

      s <<
        btor2::sub(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_accu[thread],
          encoder.nids_load[thread][address]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;

      // MEM
      pc = 15;

      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_exec[thread][pc],
          encoder.nids_load[thread][address],
          std::to_string(nid - 1),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;

      // CAS
      pc = 16;

      s <<
        btor2::eq(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_mem[thread],
          encoder.nids_load[thread][address]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bv,
          std::to_string(nid - 1),
          encoder.nids_const[1],
          encoder.nids_const[0]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 3),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;

      // next
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_accu[thread],
          std::to_string(nid - 1),
          encoder.accu_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_accu();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::define_sb_adr ===============================================

TEST(btor2_Encoder, define_sb_adr)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_sb_adr();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.sb_adr_comment;

    encoder.iterate_threads([&encoder, &nid, &s] {
      word_t & thread = encoder.thread;
      word_t & pc = encoder.pc = 1; // STORE

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_sb_adr[thread],
          encoder.nids_const[0]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_exec[thread][pc],
          encoder.nids_const[1],
          encoder.nids_sb_adr[thread],
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_sb_adr[thread],
          std::to_string(nid - 1),
          encoder.sb_adr_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_sb_adr();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::define_sb_val ===============================================

TEST(btor2_Encoder, define_sb_val)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_sb_val();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.sb_val_comment;

    encoder.iterate_threads([&encoder, &nid, &s] {
      word_t & thread = encoder.thread;
      word_t & pc = encoder.pc = 1; // STORE

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_sb_val[thread],
          encoder.nids_const[0]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_exec[thread][pc],
          encoder.nids_accu[thread],
          encoder.nids_sb_val[thread],
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bv,
          encoder.nids_sb_val[thread],
          std::to_string(nid - 1),
          encoder.sb_val_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_sb_val();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::define_sb_full ==============================================

TEST(btor2_Encoder, define_sb_full)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_sb_full();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.sb_full_comment;

    encoder.iterate_threads([&encoder, &nid, &s] {
      word_t & thread = encoder.thread;
      word_t & pc = encoder.pc = 1; // STORE

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_sb_full[thread],
          encoder.nid_false);
      nid++;
      s <<
        btor2::lor(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_exec[thread][pc],
          encoder.nids_sb_full[thread]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_flush[thread],
          encoder.nid_false,
          std::to_string(nid - 1));
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_sb_full[thread],
          std::to_string(nid - 1),
          encoder.sb_full_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_sb_full();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::define_stmt =================================================

TEST(btor2_Encoder, define_stmt)
{
  auto encoder = create<E>(dummy(3, 2));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_stmt();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.stmt_comment;

    encoder.iterate_threads([&encoder, &nid, &s] {
      word_t & thread = encoder.thread;
      word_t & pc = encoder.pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_true);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // ADDI 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          encoder.nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // HALT
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          encoder.nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_stmt();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_stmt_jmp)
{
  const auto code =
    "ADDI 1\n"
    "STORE 1\n"
    "JMP 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_stmt();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.stmt_comment;

    encoder.iterate_threads([&encoder, &nid, &s] {
      word_t & thread = encoder.thread;
      word_t & pc = encoder.pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_true);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // STORE 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          encoder.nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][2],
          encoder.nids_exec[thread][2],
          std::to_string(nid - 1),
          verbose ? encoder.debug_symbol(thread, 2) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // JMP 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          encoder.nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_stmt();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_stmt_jmp_conditional)
{
  const auto code =
    "ADDI 1\n"
    "STORE 1\n"
    "JNZ 1\n"
    "EXIT 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_stmt();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.stmt_comment;

    encoder.iterate_threads([&encoder, &nid, &s] {
      word_t & thread = encoder.thread;
      word_t & pc = encoder.pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_true);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // STORE 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          encoder.nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::neq(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_accu[thread],
          encoder.nids_const[0]);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_exec[thread][2],
          std::to_string(nid - 1));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][2],
          std::to_string(nid - 1),
          std::to_string(nid - 3),
          verbose ? encoder.debug_symbol(thread, 2) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // JNZ 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          encoder.nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // EXIT 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_exec[thread][2],
          btor2::lnot(std::to_string(nid - 10)));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_stmt();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_stmt_jmp_start)
{
  const auto code =
    "ADDI 1\n"
    "STORE 1\n"
    "JNZ 0\n"
    "EXIT 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_stmt();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.stmt_comment;

    encoder.iterate_threads([&encoder, &nid, &s] {
      word_t & thread = encoder.thread;
      word_t & pc = encoder.pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_true);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::neq(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_accu[thread],
          encoder.nids_const[0]);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_exec[thread][2],
          std::to_string(nid - 1));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][2],
          std::to_string(nid - 1),
          std::to_string(nid - 3),
          verbose ? encoder.debug_symbol(thread, 2) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // STORE 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          encoder.nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // JNZ 0
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          encoder.nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // EXIT 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_exec[thread][2],
          btor2::lnot(std::to_string(nid - 14)));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_stmt();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_stmt_jmp_twice)
{
  const auto code =
    "ADDI 1\n"
    "STORE 1\n"
    "JZ 1\n"
    "JNZ 1\n"
    "EXIT 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_stmt();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.stmt_comment;

    encoder.iterate_threads([&encoder, &nid, &s] {
      word_t & thread = encoder.thread;
      word_t & pc = encoder.pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_true);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // STORE 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          encoder.nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::eq(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_accu[thread],
          encoder.nids_const[0]);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_exec[thread][2],
          std::to_string(nid - 1));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][2],
          std::to_string(nid - 1),
          std::to_string(nid - 3),
          verbose ? encoder.debug_symbol(thread, 2) : "");
      nid++;
      s <<
        btor2::neq(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_accu[thread],
          encoder.nids_const[0]);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_exec[thread][3],
          std::to_string(nid - 1));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][3],
          std::to_string(nid - 1),
          std::to_string(nid - 3),
          verbose ? encoder.debug_symbol(thread, 3) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // JZ 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          encoder.nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // JNZ 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_exec[thread][2],
          btor2::lnot(std::to_string(nid - 13)));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;

      // EXIT 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          encoder.nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          btor2::lnot(encoder.nids_exec[thread][pc]),
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_exec[thread][3],
          btor2::lnot(std::to_string(nid - 15)));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc - 1u],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder.debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder.stmt_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_stmt();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::define_block ================================================

TEST(btor2_Encoder, define_block)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_block();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.block_comment;

    encoder.iterate_threads([&encoder, &nid, &s] {
      word_t & thread = encoder.thread;
      word_t & pc = encoder.pc = 17; // CHECK

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_block[1][thread],
          encoder.nid_false);
      nid++;
      s <<
        btor2::lor(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_exec[thread][pc],
          encoder.nids_block[1][thread]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_check[1],
          encoder.nid_false,
          std::to_string(nid - 1));
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_block[1][thread],
          std::to_string(nid - 1),
          encoder.block_var(1, thread));
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_block();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_block_empty)
{
  auto encoder = create<E>();

  encoder.define_block();

  ASSERT_EQ("", encoder.formula.str());
}

// btor2::Encoder::define_halt =================================================

TEST(btor2_Encoder, define_halt)
{
  const auto code =
    "ADDI 1\n"
    "JNZ 3\n"
    "HALT\n"
    "SUBI 1\n"
    "HALT\n";

  auto encoder = create<E>(dup(prog(code), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_halt();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.halt_comment;

    encoder.iterate_threads([&encoder, &nid, &s] {
      const word_t & thread = encoder.thread;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_halt[thread],
          encoder.nid_false);
      nid++;
      s <<
        btor2::lor(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_exec[thread][2],
          encoder.nids_exec[thread][4]);
      nid++;
      s <<
        btor2::lor(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_halt[thread],
          std::to_string(nid - 1));
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_halt[thread],
          std::to_string(nid - 1),
          encoder.halt_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_halt();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_halt_empty)
{
  auto encoder = create<E>();

  encoder.define_halt();

  ASSERT_EQ("", encoder.formula.str());
}

// btor2::Encoder::define_heap =================================================

TEST(btor2_Encoder, define_heap)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_heap();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    std::string nid_next = encoder.nid_heap;

    if (verbose)
      s << encoder.heap_comment;

    encoder.iterate_threads([&encoder, &nid, &s, &nid_next] {
      word_t & thread = encoder.thread;
      word_t & pc = encoder.pc = 16; // CAS
      word_t address = 1;

      s <<
        btor2::write(
          std::to_string(nid),
          encoder.sid_heap,
          encoder.nid_heap,
          encoder.nids_sb_adr[thread],
          encoder.nids_sb_val[thread]);
      nid++;
      std::string nid_prev = std::move(nid_next);
      nid_next = std::to_string(nid);
      s <<
        btor2::ite(
          nid_next,
          encoder.sid_heap,
          encoder.nids_flush[thread],
          std::to_string(nid - 1),
          nid_prev,
          verbose ? encoder.flush_var() : "");
      nid++;

      if (!thread)
        {
          s <<
            btor2::read(
              encoder.nids_read[address],
              encoder.sid_bv,
              encoder.nid_heap,
              encoder.nids_const[address]);
          nid++;
        }

      s <<
        btor2::eq(
          encoder.nids_eq_sb_adr_adr[thread][address],
          encoder.sid_bool,
          encoder.nids_sb_adr[thread],
          encoder.nids_const[address]);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_sb_full[thread],
          encoder.nids_eq_sb_adr_adr[thread][address]);
      nid++;
      s <<
        btor2::ite(
          encoder.nids_load[thread][address],
          encoder.sid_bv,
          std::to_string(nid - 1),
          encoder.nids_sb_val[thread],
          encoder.nids_read[address]);
      nid++;
      s <<
        btor2::eq(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_mem[thread],
          encoder.nids_load[thread][address]);
      nid++;
      s <<
        btor2::write(
          std::to_string(nid),
          encoder.sid_heap,
          encoder.nid_heap,
          encoder.nids_const[address],
          encoder.nids_accu[thread]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_heap,
          std::to_string(nid - 2),
          std::to_string(nid - 1),
          encoder.nid_heap);
      nid++;
      nid_prev = std::move(nid_next);
      nid_next = std::to_string(nid);
      s <<
        btor2::ite(
          nid_next,
          encoder.sid_heap,
          encoder.nids_exec[thread][pc],
          std::to_string(nid - 1),
          nid_prev,
          verbose ? encoder.debug_symbol(thread, pc) : "");
      nid++;
    });

    s <<
      btor2::next(
        std::to_string(nid),
        encoder.sid_heap,
        encoder.nid_heap,
        nid_next,
        encoder.heap_sym);
    nid++;

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_heap();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_heap_mmap)
{
  auto encoder = create<E>(lst(), mmap({{0, 0}, {1, 0}}));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_heap();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.heap_comment;

    s <<
      btor2::init(
        std::to_string(nid++),
        encoder.sid_heap,
        encoder.nid_heap,
        encoder.nid_mmap);
    s <<
      btor2::next(
        std::to_string(nid),
        encoder.sid_heap,
        encoder.nid_heap,
        encoder.nid_heap,
        encoder.heap_sym);

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

// btor2::Encoder::define_exit_flag ============================================

TEST(btor2_Encoder, define_exit_flag)
{
  const auto code =
    "JNZ 2\n"
    "HALT\n"
    "EXIT 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  init_state_definitions(encoder, false);
  encoder.define_halt();
  encoder.formula.str("");

  btor2::nid_t nid = encoder.node;

  encoder.define_exit_flag();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.exit_flag_comment;

    s <<
      btor2::init(
        std::to_string(nid),
        encoder.sid_bool,
        encoder.nid_exit_flag,
        encoder.nid_false);
    nid++;
    s <<
      btor2::land(
        std::to_string(nid),
        encoder.sid_bool,
        encoder.nids_halt_next[0],
        encoder.nids_halt_next[1]);
    nid++;
    s <<
      btor2::land(
        std::to_string(nid),
        encoder.sid_bool,
        encoder.nids_halt_next[2],
        std::to_string(nid - 1));
    nid++;
    s <<
      btor2::lor(
        std::to_string(nid),
        encoder.sid_bool,
        encoder.nid_exit_flag,
        std::to_string(nid - 1));
    nid++;
    s <<
      btor2::lor(
        std::to_string(nid),
        encoder.sid_bool,
        encoder.nids_exec[0][2],
        std::to_string(nid - 1));
    nid++;
    s <<
      btor2::lor(
        std::to_string(nid),
        encoder.sid_bool,
        encoder.nids_exec[1][2],
        std::to_string(nid - 1));
    nid++;
    s <<
      btor2::lor(
        std::to_string(nid),
        encoder.sid_bool,
        encoder.nids_exec[2][2],
        std::to_string(nid - 1));
    nid++;
    s <<
      btor2::next(
        std::to_string(nid),
        encoder.sid_bool,
        encoder.nid_exit_flag,
        std::to_string(nid - 1),
        encoder.exit_flag_sym);
    nid++;

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder, false);
  encoder.define_halt();
  encoder.formula.str("");

  verbose = false;
  nid = encoder.node;
  encoder.define_exit_flag();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_exit_flag_empty)
{
  auto encoder = create<E>();

  encoder.define_exit_flag();

  ASSERT_EQ("", encoder.formula.str());
}

// btor2::Encoder::define_exit_code ============================================

TEST(btor2_Encoder, define_exit_code)
{
  auto encoder = create<E>(lst(prog("EXIT 0"), prog("EXIT 1"), prog("EXIT 2")));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_exit_code();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder.exit_code_comment;

    s <<
      btor2::init(
        std::to_string(nid),
        encoder.sid_bv,
        encoder.nid_exit_code,
        encoder.nids_const[0]);
    nid++;
    s <<
      btor2::ite(
        std::to_string(nid),
        encoder.sid_bv,
        encoder.nids_exec[0][0],
        encoder.nids_const[0],
        encoder.nid_exit_code,
        verbose ? encoder.debug_symbol(0, 0) : "");
    nid++;
    s <<
      btor2::ite(
        std::to_string(nid),
        encoder.sid_bv,
        encoder.nids_exec[1][0],
        encoder.nids_const[1],
        std::to_string(nid - 1),
        verbose ? encoder.debug_symbol(1, 0) : "");
    nid++;
    s <<
      btor2::ite(
        std::to_string(nid),
        encoder.sid_bv,
        encoder.nids_exec[2][0],
        encoder.nids_const[2],
        std::to_string(nid - 1),
        verbose ? encoder.debug_symbol(2, 0) : "");
    nid++;
    s <<
      btor2::next(
        std::to_string(nid),
        encoder.sid_bv,
        encoder.nid_exit_code,
        std::to_string(nid - 1),
        encoder.exit_code_sym);
    nid++;

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_exit_code();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::define_scheduling_constraints ===============================

TEST(btor2_Encoder, define_scheduling_constraints)
{
  auto encoder = create<E>(dummy(2));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_scheduling_constraints();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("scheduling constraints");

    std::vector<std::string> args;

    args.insert(
      args.end(),
      encoder.nids_thread.begin(),
      encoder.nids_thread.end());

    args.insert(
      args.end(),
      encoder.nids_flush.begin(),
      encoder.nids_flush.end());

    args.push_back(encoder.nid_exit_flag);

    s << btor2::card_constraint_naive(nid, encoder.sid_bool, args) << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_scheduling_constraints();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_scheduling_constraints_exit)
{
  auto encoder = create<E>(dup(prog("EXIT 1"), 2));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_scheduling_constraints();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("scheduling constraints");

    std::vector<std::string> args;

    args.insert(
      args.end(),
      encoder.nids_thread.begin(),
      encoder.nids_thread.end());

    args.insert(
      args.end(),
      encoder.nids_flush.begin(),
      encoder.nids_flush.end());

    args.push_back(encoder.nid_exit_flag);

    s << btor2::card_constraint_naive(nid, encoder.sid_bool, args) << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_scheduling_constraints();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_scheduling_constraints_single_thread)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_scheduling_constraints();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("scheduling constraints");

    std::vector<std::string> args;

    args.reserve(encoder.num_threads * 2);

    args.insert(
      args.end(),
      encoder.nids_thread.begin(),
      encoder.nids_thread.end());

    args.insert(
      args.end(),
      encoder.nids_flush.begin(),
      encoder.nids_flush.end());

    args.push_back(encoder.nid_exit_flag);

    s << btor2::card_constraint_naive(nid, encoder.sid_bool, args) << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_scheduling_constraints();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::define_store_buffer_constraints =============================

TEST(btor2_Encoder, define_store_buffer_constraints)
{
  const auto code =
    "STORE 1\n"
    "FENCE\n"
    "CAS 1\n"
    "HALT\n";

  auto encoder = create<E>(dup(prog(code), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_store_buffer_constraints();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("store buffer constraints");

    encoder.iterate_threads([&encoder, &nid, &s] {
      s <<
        btor2::lor(nid, encoder.sid_bool, encoder.nids_stmt[encoder.thread]);
      s <<
        btor2::implies(
          std::to_string(nid),
          encoder.sid_bool,
          std::to_string(nid - 1),
          btor2::lnot(encoder.nids_thread[encoder.thread]));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder.sid_bool,
          encoder.nids_sb_full[encoder.thread],
          std::to_string(nid - 1),
          btor2::lnot(encoder.nids_flush[encoder.thread]));
      nid++;
      s << btor2::constraint(nid, encoder.flush_var());
      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_store_buffer_constraints();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_store_buffer_constraints_no_barrier)
{
  auto encoder = create<E>(dup(prog("JMP 0"), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_store_buffer_constraints();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("store buffer constraints");

    encoder.iterate_threads([&encoder, &nid, &s] {
      s <<
        btor2::implies(
          std::to_string(nid),
          encoder.sid_bool,
          btor2::lnot(encoder.nids_sb_full[encoder.thread]),
          btor2::lnot(encoder.nids_flush[encoder.thread]));
      nid++;
      s << btor2::constraint(nid, encoder.flush_var());
      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_store_buffer_constraints();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::define_checkpoint_constraints ===============================

TEST(btor2_Encoder, define_checkpoint_constraints)
{
  auto encoder = create<E>(dup(prog("CHECK 1"), 3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_checkpoint_constraints();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("checkpoint constraints");

    for (const auto & [id, threads] : encoder.nids_block)
      {
        std::string nid_not_check = btor2::lnot(encoder.nids_check[1]);

        for (const auto & [thread, nid_block] : threads)
          {
            s <<
              btor2::land(
                std::to_string(nid),
                encoder.sid_bool,
                nid_block,
                nid_not_check);
            nid++;
            s <<
              btor2::implies(
                std::to_string(nid),
                encoder.sid_bool,
                std::to_string(nid - 1),
                btor2::lnot(encoder.nids_thread[thread]));
            nid++;
            s << btor2::constraint(nid, encoder.block_var(id, thread));

            s << eol;
          }
      }

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_checkpoint_constraints();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_checkpoint_constraints_empty)
{
  auto encoder = create<E>();

  encoder.define_checkpoint_constraints();

  ASSERT_EQ("", encoder.formula.str());
}

// btor2::Encoder::define_halt_constraints =====================================

TEST(btor2_Encoder, define_halt_constraints)
{
  auto encoder = create<E>(dummy(3));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_halt_constraints();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("halt constraints");

    for (const auto & [t, nid_halt] : encoder.nids_halt)
      {
        s <<
          btor2::implies(
            std::to_string(nid),
            encoder.sid_bool,
            nid_halt,
            btor2::lnot(encoder.nids_thread[t]));
        nid++;
        s << btor2::constraint(nid, encoder.halt_var(t));

        s << eol;
      }

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_halt_constraints();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

TEST(btor2_Encoder, define_halt_constraints_empty)
{
  auto encoder = create<E>();

  encoder.define_checkpoint_constraints();

  ASSERT_EQ("", encoder.formula.str());
}

// btor2::Encoder::define_bound ================================================

TEST(btor2_Encoder, define_bound)
{
  auto encoder = create<E>();

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  encoder.define_bound();

  auto expected = [&encoder, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("bound")
        << btor2::comment("step counter")
        << eol;

    std::string nid_ctr = std::to_string(nid);

    s << btor2::state(nid_ctr, encoder.sid_bv, "k");
    nid++;
    s <<
      btor2::init(
        std::to_string(nid),
        encoder.sid_bv,
        nid_ctr,
        encoder.nids_const[0]);
    nid++;
    s <<
      btor2::add(
        std::to_string(nid),
        encoder.sid_bv,
        encoder.nids_const[1],
        nid_ctr);
    nid++;
    s <<
      btor2::next(
        std::to_string(nid),
        encoder.sid_bv,
        nid_ctr,
        std::to_string(nid - 1));
    nid++;
    s << eol;
    if (verbose)
      s << btor2::comment("bound (" + std::to_string(encoder.bound) + ")")
        << eol;
    s <<
      btor2::eq(
        std::to_string(nid),
        encoder.sid_bool,
        encoder.nids_const[encoder.bound],
        nid_ctr);
    nid++;
    s << btor2::bad(std::to_string(nid), std::to_string(nid - 1));

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());

  // verbosity
  reset(encoder);
  init_state_definitions(encoder);

  verbose = false;
  nid = encoder.node;
  encoder.define_bound();
  ASSERT_EQ(expected(), encoder.formula.str());
  verbose = true;
}

// btor2::Encoder::encode ======================================================

TEST(btor2_Encoder, encode_check) { encode_check<E>(); }
TEST(btor2_Encoder, encode_cas) { encode_cas<E>(); }
TEST(btor2_Encoder, encode_indirect) { encode_indirect<E>(); }
TEST(btor2_Encoder, encode_halt) { encode_halt<E>(); }

TEST(btor2_Encoder, encode_litmus_intel_1) { encode_litmus_intel_1<E>(); }
TEST(btor2_Encoder, encode_litmus_intel_2) { encode_litmus_intel_2<E>(); }
TEST(btor2_Encoder, encode_litmus_intel_3) { encode_litmus_intel_3<E>(); }
TEST(btor2_Encoder, encode_litmus_intel_4) { encode_litmus_intel_4<E>(); }
TEST(btor2_Encoder, encode_litmus_intel_5) { encode_litmus_intel_5<E>(); }
TEST(btor2_Encoder, encode_litmus_intel_6) { encode_litmus_intel_6<E>(); }
TEST(btor2_Encoder, encode_litmus_intel_7) { encode_litmus_intel_7<E>(); }
TEST(btor2_Encoder, encode_litmus_intel_8) { encode_litmus_intel_8<E>(); }
TEST(btor2_Encoder, encode_litmus_intel_9) { encode_litmus_intel_9<E>(); }
TEST(btor2_Encoder, encode_litmus_intel_10) { encode_litmus_intel_10<E>(); }

TEST(btor2_Encoder, encode_litmus_amd_1) { encode_litmus_amd_1<E>(); }
TEST(btor2_Encoder, encode_litmus_amd_2) { encode_litmus_amd_2<E>(); }
TEST(btor2_Encoder, encode_litmus_amd_3) { encode_litmus_amd_3<E>(); }
TEST(btor2_Encoder, encode_litmus_amd_4) { encode_litmus_amd_4<E>(); }
TEST(btor2_Encoder, encode_litmus_amd_5) { encode_litmus_amd_5<E>(); }
TEST(btor2_Encoder, encode_litmus_amd_6) { encode_litmus_amd_6<E>(); }
TEST(btor2_Encoder, encode_litmus_amd_7) { encode_litmus_amd_7<E>(); }
TEST(btor2_Encoder, encode_litmus_amd_8) { encode_litmus_amd_8<E>(); }
TEST(btor2_Encoder, encode_litmus_amd_9) { encode_litmus_amd_9<E>(); }

TEST(btor2_Encoder, LOAD)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Load load {Instruction::Type::none, address};

  ASSERT_EQ(
    encoder.nids_load[encoder.thread][address],
    encoder.encode(load));
  ASSERT_EQ(expected_load(encoder, nid, address), encoder.formula.str());
}

TEST(btor2_Encoder, LOAD_indirect)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Load load {Instruction::Type::none, address, true};

  ASSERT_EQ(
    encoder.nids_load_indirect[encoder.thread][address],
    encoder.encode(load));
  ASSERT_EQ(
    expected_load_indirect(encoder, nid, address),
    encoder.formula.str());
}

TEST(btor2_Encoder, STORE)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  word_t address = 0;

  Instruction::Store store {Instruction::Type::none, address};

  encoder.update = E::Update::sb_adr;
  ASSERT_EQ(encoder.nids_const[address], encoder.encode(store));

  encoder.update = E::Update::sb_val;
  ASSERT_EQ(encoder.nids_accu[0], encoder.encode(store));
}

TEST(btor2_Encoder, STORE_indirect)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Store store {Instruction::Type::none, address, true};

  encoder.update = E::Update::sb_adr;
  ASSERT_EQ(
    encoder.nids_load[encoder.thread][address],
    encoder.encode(store));
  ASSERT_EQ(expected_load(encoder, nid, address), encoder.formula.str());

  encoder.update = E::Update::sb_val;
  ASSERT_EQ(encoder.nids_accu[0], encoder.encode(store));
}

TEST(btor2_Encoder, ADD)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Add add {Instruction::Type::none, address};

  std::string nid_add = encoder.encode(add);

  auto expected = [&encoder, &nid, &address, &nid_add] {
    std::ostringstream s;

    s << expected_load(encoder, nid, address);
    s <<
      btor2::add(
        nid_add,
        encoder.sid_bv,
        encoder.nids_accu[encoder.thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, ADD_indirect)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Add add {Instruction::Type::none, address, true};

  std::string nid_add = encoder.encode(add);

  auto expected = [&encoder, &nid, &address, &nid_add] {
    std::ostringstream s;

    s << expected_load_indirect(encoder, nid, address);
    s <<
      btor2::add(
        nid_add,
        encoder.sid_bv,
        encoder.nids_accu[encoder.thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, ADDI)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t value = 0;

  Instruction::Addi addi {Instruction::Type::none, value};

  std::string nid_addi = encoder.encode(addi);

  auto expected = [&encoder, &nid, &value, &nid_addi] {
    std::ostringstream s;

    s <<
      btor2::add(
        nid_addi,
        encoder.sid_bv,
        encoder.nids_accu[encoder.thread],
        encoder.nids_const[value]);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, SUB)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Sub sub {Instruction::Type::none, address};

  std::string nid_sub = encoder.encode(sub);

  auto expected = [&encoder, &nid, &address, &nid_sub] {
    std::ostringstream s;

    s << expected_load(encoder, nid, address);
    s <<
      btor2::sub(
        nid_sub,
        encoder.sid_bv,
        encoder.nids_accu[encoder.thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, SUB_indirect)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Sub sub {Instruction::Type::none, address, true};

  std::string nid_sub = encoder.encode(sub);

  auto expected = [&encoder, &nid, &address, &nid_sub] {
    std::ostringstream s;

    s << expected_load_indirect(encoder, nid, address);
    s <<
      btor2::sub(
        nid_sub,
        encoder.sid_bv,
        encoder.nids_accu[encoder.thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, SUBI)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t value = 0;

  Instruction::Subi subi {Instruction::Type::none, value};

  std::string nid_subi = encoder.encode(subi);

  auto expected = [&encoder, &nid, &value, &nid_subi] {
    std::ostringstream s;

    s <<
      btor2::sub(
        nid_subi,
        encoder.sid_bv,
        encoder.nids_accu[encoder.thread],
        encoder.nids_const[value]);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, MUL)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Mul mul {Instruction::Type::none, address};

  std::string nid_mul = encoder.encode(mul);

  auto expected = [&encoder, &nid, &address, &nid_mul] {
    std::ostringstream s;

    s << expected_load(encoder, nid, address);
    s <<
      btor2::mul(
        nid_mul,
        encoder.sid_bv,
        encoder.nids_accu[encoder.thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, MUL_indirect)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Mul mul {Instruction::Type::none, address, true};

  std::string nid_mul = encoder.encode(mul);

  auto expected = [&encoder, &nid, &address, &nid_mul] {
    std::ostringstream s;

    s << expected_load_indirect(encoder, nid, address);
    s <<
      btor2::mul(
        nid_mul,
        encoder.sid_bv,
        encoder.nids_accu[encoder.thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, MULI)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t value = 0;

  Instruction::Muli muli {Instruction::Type::none, value};

  std::string nid_muli = encoder.encode(muli);

  auto expected = [&encoder, &nid, &value, &nid_muli] {
    std::ostringstream s;

    s <<
      btor2::mul(
        nid_muli,
        encoder.sid_bv,
        encoder.nids_accu[encoder.thread],
        encoder.nids_const[value]);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, CMP)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Cmp cmp {Instruction::Type::none, address};

  std::string nid_cmp = encoder.encode(cmp);

  auto expected = [&encoder, &nid, &address, &nid_cmp] {
    std::ostringstream s;

    s << expected_load(encoder, nid, address);
    s <<
      btor2::sub(
        nid_cmp,
        encoder.sid_bv,
        encoder.nids_accu[encoder.thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, CMP_indirect)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Cmp cmp {Instruction::Type::none, address, true};

  std::string nid_cmp = encoder.encode(cmp);

  auto expected = [&encoder, &nid, &address, &nid_cmp] {
    std::ostringstream s;

    s << expected_load_indirect(encoder, nid, address);
    s <<
      btor2::sub(
        nid_cmp,
        encoder.sid_bv,
        encoder.nids_accu[encoder.thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, JMP)
{
  auto encoder = create<E>(dummy(1));

  Instruction::Jmp jmp {Instruction::Type::none, 0};

  ASSERT_EQ("", encoder.encode(jmp));
  ASSERT_EQ("", encoder.formula.str());
}

TEST(btor2_Encoder, JZ)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  Instruction::Jz jz {Instruction::Type::none, 0};

  std::string nid_jz = encoder.encode(jz);

  auto expected = [&encoder, &nid, &nid_jz] {
    std::ostringstream s;

    s <<
      btor2::eq(
        nid_jz,
        encoder.sid_bool,
        encoder.nids_accu[encoder.thread],
        encoder.nids_const[0]);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, JNZ)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  Instruction::Jnz jnz {Instruction::Type::none, 0};

  std::string nid_jnz = encoder.encode(jnz);

  auto expected = [&encoder, &nid, &nid_jnz] {
    std::ostringstream s;

    s <<
      btor2::neq(
        nid_jnz,
        encoder.sid_bool,
        encoder.nids_accu[encoder.thread],
        encoder.nids_const[0]);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, JS)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  Instruction::Js js {Instruction::Type::none, 0};

  std::string nid_js = encoder.encode(js);

  auto expected = [&encoder, &nid, &nid_js] {
    std::ostringstream s;

    s <<
      btor2::slice(
        nid_js,
        encoder.sid_bool,
        encoder.nids_accu[encoder.thread],
        encoder.msb,
        encoder.msb);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, JNS)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  Instruction::Jns jns {Instruction::Type::none, 0};

  std::string nid_jns = encoder.encode(jns);

  auto expected = [&encoder, &nid, &nid_jns] {
    std::ostringstream s;

    s <<
      btor2::slice(
        nid_jns.substr(1),
        encoder.sid_bool,
        encoder.nids_accu[encoder.thread],
        encoder.msb,
        encoder.msb);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, JNZNS)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  Instruction::Jnzns jnzns {Instruction::Type::none, 0};

  std::string nid_jnzns = encoder.encode(jnzns);

  auto expected = [&encoder, &nid, &nid_jnzns] {
    std::ostringstream s;

    s <<
      btor2::neq(
        std::to_string(nid),
        encoder.sid_bool,
        encoder.nids_accu[encoder.thread],
        encoder.nids_const[0]);
    nid++;
    s <<
      btor2::slice(
        std::to_string(nid),
        encoder.sid_bool,
        encoder.nids_accu[encoder.thread],
        encoder.msb,
        encoder.msb);
    nid++;
    s <<
      btor2::land(
        nid_jnzns,
        encoder.sid_bool,
        std::to_string(nid - 2),
        btor2::lnot(std::to_string(nid - 1)));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, MEM)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Mem mem {Instruction::Type::none, address};

  ASSERT_EQ(
    encoder.nids_load[encoder.thread][address],
    encoder.encode(mem));
  ASSERT_EQ(expected_load(encoder, nid, address), encoder.formula.str());
}

TEST(btor2_Encoder, MEM_indirect)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Mem mem {Instruction::Type::none, address, true};

  ASSERT_EQ(
    encoder.nids_load_indirect[encoder.thread][address],
    encoder.encode(mem));
  ASSERT_EQ(
    expected_load_indirect(encoder, nid, address),
    encoder.formula.str());
}

TEST(btor2_Encoder, CAS)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Cas cas {Instruction::Type::none, address};

  std::string nid_cas;

  auto expected = [&encoder, &nid, &address, &nid_cas] {
    std::ostringstream s;

    if (encoder.update == E::Update::accu)
      {
        s << expected_load(encoder, nid, address);
        s <<
          btor2::eq(
            encoder.nids_cas[encoder.thread][address],
            encoder.sid_bool,
            encoder.nids_mem[encoder.thread],
            encoder.nids_load[encoder.thread][address]);
        nid++;
        s <<
          btor2::ite(
            nid_cas,
            encoder.sid_bv,
            encoder.nids_cas[encoder.thread][address],
            encoder.nids_const[1],
            encoder.nids_const[0]);
        nid++;
      }
    else if (encoder.update == E::Update::heap)
      {
        s <<
          btor2::write(
            std::to_string(nid),
            encoder.sid_heap,
            encoder.nid_heap,
            encoder.nids_const[address],
            encoder.nids_accu[encoder.thread]);
        nid++;
        s <<
          btor2::ite(
            nid_cas,
            encoder.sid_heap,
            encoder.nids_cas[encoder.thread][address],
            std::to_string(nid - 1),
            encoder.nid_heap);
        nid++;
      }

    return s.str();
  };

  encoder.update = E::Update::accu;
  nid_cas = encoder.encode(cas);
  ASSERT_EQ(expected(), encoder.formula.str());

  encoder.formula.str("");

  encoder.update = E::Update::heap;
  nid_cas = encoder.encode(cas);
  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, CAS_indirect)
{
  auto encoder = create<E>(dummy(1));

  init_state_definitions(encoder);

  btor2::nid_t nid = encoder.node;

  word_t address = 0;

  Instruction::Cas cas {Instruction::Type::none, address, true};

  std::string nid_cas;

  auto expected = [&encoder, &nid, &address, &nid_cas] {
    std::ostringstream s;

    if (encoder.update == E::Update::accu)
      {
        s << expected_load(encoder, nid, address);
        s <<
          btor2::eq(
            encoder.nids_cas_indirect[encoder.thread][address],
            encoder.sid_bool,
            encoder.nids_mem[encoder.thread],
            encoder.nids_load[encoder.thread][address]);
        nid++;
        s <<
          btor2::ite(
            nid_cas,
            encoder.sid_bv,
            encoder.nids_cas_indirect[encoder.thread][address],
            encoder.nids_const[1],
            encoder.nids_const[0]);
        nid++;
      }
    else if (encoder.update == E::Update::heap)
      {
        s <<
          btor2::write(
            std::to_string(nid),
            encoder.sid_heap,
            encoder.nid_heap,
            encoder.nids_load[encoder.thread][address],
            encoder.nids_accu[encoder.thread]);
        nid++;
        s <<
          btor2::ite(
            nid_cas,
            encoder.sid_heap,
            encoder.nids_cas_indirect[encoder.thread][address],
            std::to_string(nid - 1),
            encoder.nid_heap);
        nid++;
      }

    return s.str();
  };

  encoder.update = E::Update::accu;
  nid_cas = encoder.encode(cas);
  ASSERT_EQ(expected(), encoder.formula.str());

  encoder.formula.str("");

  encoder.update = E::Update::heap;
  nid_cas = encoder.encode(cas);
  ASSERT_EQ(expected(), encoder.formula.str());
}

TEST(btor2_Encoder, EXIT)
{
  auto encoder = create<E>(dummy(1));

  Instruction::Exit exit {Instruction::Type::none, 1};

  ASSERT_EQ(encoder.nids_const[1], encoder.encode(exit));
  ASSERT_EQ("", encoder.formula.str());
}

} // namespace ConcuBinE::test
