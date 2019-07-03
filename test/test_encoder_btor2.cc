#include "test_encoder.hh"

#include <functional>

#include "btor2.hh"
#include "btormc.hh"

namespace test {

//==============================================================================
// helper
//==============================================================================

// TODO remove - debug only
void evaluate (const std::string & formula)
{
  BtorMC btormc(20);
  std::cout << "running btormc..." << eol;
  btormc.sat(formula);
}

//==============================================================================
// btor2::Encoder tests
//==============================================================================

struct btor2_Encoder : public encoder::Encoder<btor2::Encoder>
{
  void init_declarations (const bool clear_formula = true)
    {
      encoder->declare_sorts();
      encoder->declare_constants();

      encoder->thread = encoder->pc = 0;

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_definitions (const bool clear_formula = true)
    {
      init_declarations(clear_formula);

      encoder->declare_states();
      encoder->declare_inputs();

      encoder->thread = encoder->pc = 0;

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_state_definitions (const bool clear_formula = true)
    {
      init_definitions(clear_formula);

      encoder->define_transitions();

      encoder->thread = encoder->pc = 0;

      if (clear_formula)
        encoder->formula.str("");
    }

  std::function<std::string()> expected = [] { return ""; };

  std::string expected_load (btor2::nid_t & nid, const word_t address)
    {
      std::ostringstream s;
      const word_t & thread = encoder->thread;

      if (!thread)
        {
          s <<
            btor2::read(
              encoder->nids_read[address],
              encoder->sid_bv,
              encoder->nid_heap,
              encoder->nids_const[address]);
          nid++;
        }

      s <<
        btor2::eq(
          encoder->nids_eq_sb_adr_adr[thread][address],
          encoder->sid_bool,
          encoder->nids_sb_adr[thread],
          encoder->nids_const[address]);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_full[thread],
          encoder->nids_eq_sb_adr_adr[thread][address]);
      nid++;
      s <<
        btor2::ite(
          encoder->nids_load[thread][address],
          encoder->sid_bv,
          std::to_string(nid - 1),
          encoder->nids_sb_val[thread],
          encoder->nids_read[address]);
      nid++;

      return s.str();
    }

  std::string expected_load_indirect (btor2::nid_t & nid, const word_t address)
    {
      std::ostringstream s;
      const word_t & thread = encoder->thread;

      if (!thread)
        {
          s <<
            btor2::read(
              encoder->nids_read[address],
              encoder->sid_bv,
              encoder->nid_heap,
              encoder->nids_const[address]);
          nid++;
        }

      s <<
        btor2::eq(
          encoder->nids_eq_sb_adr_adr[thread][address],
          encoder->sid_bool,
          encoder->nids_sb_adr[thread],
          encoder->nids_const[address]);
      nid++;

      if (!thread)
        {
          s <<
            btor2::read(
              encoder->nids_read_indirect[address],
              encoder->sid_bv,
              encoder->nid_heap,
              encoder->nids_read[address]);
          nid++;
        }

      s <<
        btor2::eq(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_adr[thread],
          encoder->nids_read[address]);
      nid++;

      std::string nid_ite_eq_sb_adr_read_adr = std::to_string(nid);

      s <<
        btor2::ite(
          nid_ite_eq_sb_adr_read_adr,
          encoder->sid_bv,
          std::to_string(nid - 1),
          encoder->nids_sb_val[thread],
          encoder->nids_read_indirect[address]);
      nid++;

      if (!address || thread)
        {
          s <<
            btor2::read(
              std::to_string(nid),
              encoder->sid_bv,
              encoder->nid_heap,
              encoder->nids_sb_val[thread]);
          nid++;
          s <<
            btor2::read(
              std::to_string(nid),
              encoder->sid_bv,
              encoder->nid_heap,
              std::to_string(nid - 1));
          nid++;
          s <<
            btor2::eq(
              std::to_string(nid),
              encoder->sid_bool,
              encoder->nids_sb_adr[thread],
              std::to_string(nid - 2));
          nid++;
          s<<
            btor2::ite(
              encoder->nids_ite_eq_sb_adr_read_sb_val[thread],
              encoder->sid_bv,
              std::to_string(nid - 1),
              encoder->nids_sb_val[thread],
              std::to_string(nid - 2));
          nid++;
        }

      s <<
        btor2::eq(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_val[thread],
          encoder->nids_const[address]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bv,
          std::to_string(nid - 1),
          encoder->nids_sb_val[thread],
          encoder->nids_ite_eq_sb_adr_read_sb_val[thread]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_eq_sb_adr_adr[thread][address],
          std::to_string(nid - 1),
          nid_ite_eq_sb_adr_read_adr);
      nid++;
      s <<
        btor2::ite(
          encoder->nids_load_indirect[thread][address],
          encoder->sid_bv,
          encoder->nids_sb_full[thread],
          std::to_string(nid - 1),
          encoder->nids_read_indirect[address]);
      nid++;

      return s.str();
    }
};

// btor2::Encoder::load ========================================================

TEST_F(btor2_Encoder, load)
{
  add_dummy_programs(2);
  reset_encoder();
  init_definitions();

  btor2::nid_t nid = encoder->node;
  word_t & thread = encoder->thread;
  word_t address = 0;

  ASSERT_EQ(encoder->nids_load[thread][address], encoder->load(address));
  ASSERT_EQ(expected_load(nid, address), encoder->str());
  encoder->formula.str("");

  // another load with the same address
  ASSERT_EQ(encoder->nids_load[thread][address], encoder->load(address));
  ASSERT_EQ("", encoder->str());

  // another load with a different address
  address = 1;
  ASSERT_EQ(encoder->nids_load[thread][address], encoder->load(address));
  ASSERT_EQ(expected_load(nid, address), encoder->str());
  encoder->formula.str("");

  // another load from a different thread
  thread = 1;
  ASSERT_EQ(encoder->nids_load[thread][address], encoder->load(address));
  ASSERT_EQ(expected_load(nid, address), encoder->str());
}

TEST_F(btor2_Encoder, load_indirect)
{
  add_dummy_programs(2);
  reset_encoder();
  init_definitions();

  btor2::nid_t nid = encoder->node;
  word_t & thread = encoder->thread;
  word_t address = 0;

  ASSERT_EQ(
    encoder->nids_load_indirect[thread][address],
    encoder->load(address, true));
  ASSERT_EQ(expected_load_indirect(nid, address), encoder->str());
  encoder->formula.str("");

  // another load with the same address
  ASSERT_EQ(
    encoder->nids_load_indirect[thread][address],
    encoder->load(address, true));
  ASSERT_EQ("", encoder->str());

  // another load with a different address
  address = 1;
  ASSERT_EQ(
    encoder->nids_load_indirect[thread][address],
    encoder->load(address, true));
  ASSERT_EQ(expected_load_indirect(nid, address), encoder->str());
  encoder->formula.str("");

  // another load from a different thread
  thread = 1;
  ASSERT_EQ(
    encoder->nids_load_indirect[thread][address],
    encoder->load(address, true));
  ASSERT_EQ(expected_load_indirect(nid, address), encoder->str());
}

// btor2::Encoder::declare_sorts ===============================================

TEST_F(btor2_Encoder, declare_sorts)
{
  encoder->declare_sorts();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("sorts");

    s << encoder->sid_bool << " sort bitvec 1\n"
      << encoder->sid_bv << " sort bitvec 16\n"
      << encoder->sid_heap << " sort array 2 2\n"
      << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_sorts();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::declare_constants ===========================================

TEST_F(btor2_Encoder, declare_constants)
{
  programs.resize(3);
  for (size_t thread = 0; thread < 3; thread++)
    for (size_t pc = 0; pc < 3; pc++)
      programs[thread].push_back(
        Instruction::create("ADDI", thread + pc + 1));

  reset_encoder();

  encoder->declare_sorts();
  encoder->formula.str("");

  encoder->declare_constants();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("constants");

    s << encoder->nid_false << " zero 1\n"
      << encoder->nid_true << " one 1\n"
      << eol
      << encoder->nids_const[0] << " zero 2\n"
      << encoder->nids_const[1] << " one 2\n"
      << encoder->nids_const[2] << " constd 2 2\n"
      << encoder->nids_const[3] << " constd 2 3\n"
      << encoder->nids_const[4] << " constd 2 4\n"
      << encoder->nids_const[5] << " constd 2 5\n"
      << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();

  encoder->declare_sorts();
  encoder->formula.str("");

  verbose = false;
  encoder->declare_constants();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::declare_accu ================================================

TEST_F(btor2_Encoder, declare_accu)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_accu();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << encoder->accu_comment;

    encoder->iterate_threads([this, &s] {
      s <<
        btor2::state(
          encoder->nids_accu[encoder->thread],
          encoder->sid_bv,
          encoder->accu_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_declarations();

  verbose = false;
  encoder->declare_accu();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::declare_mem =================================================

TEST_F(btor2_Encoder, declare_mem)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_mem();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << encoder->mem_comment;

    encoder->iterate_threads([this, &s] {
      s <<
        btor2::state(
          encoder->nids_mem[encoder->thread],
          encoder->sid_bv,
          encoder->mem_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_declarations();

  verbose = false;
  encoder->declare_mem();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::declare_sb_adr ==============================================

TEST_F(btor2_Encoder, declare_sb_adr)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_sb_adr();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << encoder->sb_adr_comment;

    encoder->iterate_threads([this, &s] {
      s <<
        btor2::state(
          encoder->nids_sb_adr[encoder->thread],
          encoder->sid_bv,
          encoder->sb_adr_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_declarations();

  verbose = false;
  encoder->declare_sb_adr();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::declare_sb_val ==============================================

TEST_F(btor2_Encoder, declare_sb_val)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_sb_val();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << encoder->sb_val_comment;

    encoder->iterate_threads([this, &s] {
      s <<
        btor2::state(
          encoder->nids_sb_val[encoder->thread],
          encoder->sid_bv,
          encoder->sb_val_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_declarations();

  verbose = false;
  encoder->declare_sb_val();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::declare_sb_full =============================================

TEST_F(btor2_Encoder, declare_sb_full)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_sb_full();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << encoder->sb_full_comment;

    encoder->iterate_threads([this, &s] {
      s <<
        btor2::state(
          encoder->nids_sb_full[encoder->thread],
          encoder->sid_bool,
          encoder->sb_full_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_declarations();

  verbose = false;
  encoder->declare_sb_full();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::declare_stmt ================================================

TEST_F(btor2_Encoder, declare_stmt)
{
  add_dummy_programs(3, 3);
  reset_encoder();
  init_declarations();

  encoder->declare_stmt();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << encoder->stmt_comment;

    encoder->iterate_programs([this, &s] (const Program & program) {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc;

      for (pc = 0; pc < program.size(); pc++)
        s <<
          btor2::state(
            encoder->nids_stmt[thread][pc],
            encoder->sid_bool,
            encoder->stmt_var());

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_declarations();

  verbose = false;
  encoder->declare_stmt();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::declare_block ===============================================

TEST_F(btor2_Encoder, declare_block)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(
      create_program(
        "CHECK 0\n"
        "CHECK 1\n"
      ));

  reset_encoder();
  init_declarations();

  encoder->declare_block();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << encoder->block_comment;

    for (const auto & [c, threads] : encoder->nids_block)
      {
        for (const auto & [t, nid] : threads)
          s << btor2::state(nid, encoder->sid_bool, encoder->block_var(c, t));

        s << eol;
      }

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_declarations();

  verbose = false;
  encoder->declare_block();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(btor2_Encoder, declare_block_empty)
{
  encoder->declare_block();

  ASSERT_EQ("", encoder->str());
}

// btor2::Encoder::declare_heap ================================================

TEST_F(btor2_Encoder, declare_heap)
{
  init_declarations();

  encoder->declare_heap();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << encoder->heap_comment;

    s << encoder->nid_heap + " state 3 heap\n\n";

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_declarations();

  verbose = false;
  encoder->declare_heap();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::declare_exit_flag ===========================================

TEST_F(btor2_Encoder, declare_exit_flag)
{
  programs.push_back(create_program("EXIT 1\n"));
  reset_encoder();
  init_declarations();

  encoder->declare_exit_flag();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << encoder->exit_flag_comment;

    s << encoder->nid_exit_flag + " state 1 exit\n\n";

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_declarations();

  verbose = false;
  encoder->declare_exit_flag();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(btor2_Encoder, declare_exit_flag_empty)
{
  encoder->declare_exit_flag();

  ASSERT_EQ("", encoder->str());
}

// btor2::Encoder::declare_exit_code ===========================================

TEST_F(btor2_Encoder, declare_exit_code)
{
  programs.push_back(create_program("EXIT 1\n"));
  reset_encoder();
  init_declarations();

  encoder->declare_exit_code();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << encoder->exit_code_comment;

    s << encoder->nid_exit_code + " state 2 exit-code\n\n";

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_declarations();

  verbose = false;
  encoder->declare_exit_code();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::declare_thread ==============================================

TEST_F(btor2_Encoder, declare_thread)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_thread();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << encoder->thread_comment;

    encoder->iterate_threads([this, &s] {
      s <<
        btor2::input(
          encoder->nids_thread[encoder->thread],
          encoder->sid_bool,
          encoder->thread_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_declarations();

  verbose = false;
  encoder->declare_thread();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::declare_flush ===============================================

TEST_F(btor2_Encoder, declare_flush)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_flush();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << encoder->flush_comment;

    encoder->iterate_threads([this, &s] {
      s <<
        btor2::input(
          encoder->nids_flush[encoder->thread],
          encoder->sid_bool,
          encoder->flush_var());
    });

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_declarations();

  verbose = false;
  encoder->declare_flush();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::define_exec =================================================

TEST_F(btor2_Encoder, define_exec)
{
  add_dummy_programs(3, 3);
  reset_encoder();
  init_definitions();

  encoder->define_exec();

  expected = [this] {
    std::ostringstream s;

    if (verbose)
      s << encoder->exec_comment;

    encoder->iterate_programs([this, &s] (const Program & program) {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc;

      for (pc = 0; pc < program.size(); pc++)
        s <<
          btor2::land(
            encoder->nids_exec[thread][pc],
            encoder->sid_bool,
            encoder->nids_stmt[thread][pc],
            encoder->nids_thread[thread],
            encoder->exec_var());

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_definitions();

  verbose = false;
  encoder->define_exec();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::define_check ================================================

TEST_F(btor2_Encoder, define_check)
{
  add_instruction_set(3);
  reset_encoder();
  init_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_check();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder->check_comment;

    std::vector<std::string> blocks;

    for (const auto & [c, threads] : encoder->nids_block)
      for (const auto & [t, nid_block] : threads)
        blocks.push_back(nid_block);

    s << btor2::land(nid, encoder->sid_bool, blocks, encoder->check_var(1));
    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_check();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(btor2_Encoder, define_check_empty)
{
  encoder->define_check();
  ASSERT_EQ("", encoder->str());
}

// btor2::Encoder::define_accu =================================================

TEST_F(btor2_Encoder, define_accu)
{
  add_instruction_set(3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_accu();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder->accu_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 0;
      word_t address = 1;

      // init
      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_accu[thread],
          encoder->nids_const[0]);
      nid++;

      // LOAD
      if (!thread)
        {
          s <<
            btor2::read(
              encoder->nids_read[address],
              encoder->sid_bv,
              encoder->nid_heap,
              encoder->nids_const[address]);
          nid++;
        }

      s <<
        btor2::eq(
          encoder->nids_eq_sb_adr_adr[thread][address],
          encoder->sid_bool,
          encoder->nids_sb_adr[thread],
          encoder->nids_const[address]);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_full[thread],
          encoder->nids_eq_sb_adr_adr[thread][address]);
      nid++;
      s <<
        btor2::ite(
          encoder->nids_load[thread][address],
          encoder->sid_bv,
          std::to_string(nid - 1),
          encoder->nids_sb_val[thread],
          encoder->nids_read[address]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          encoder->nids_load[thread][address],
          encoder->nids_accu[thread],
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // ADD
      pc = 2;

      s <<
        btor2::add(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_accu[thread],
          encoder->nids_load[thread][address]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // ADDI
      pc = 3;

      s <<
        btor2::add(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_accu[thread],
          encoder->nids_const[1]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // SUB
      pc = 4;

      s <<
        btor2::sub(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_accu[thread],
          encoder->nids_load[thread][address]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // SUBI
      pc = 5;

      s <<
        btor2::sub(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_accu[thread],
          encoder->nids_const[1]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // CMP
      pc = 6;

      s <<
        btor2::sub(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_accu[thread],
          encoder->nids_load[thread][address]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // MEM
      pc = 13;

      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          encoder->nids_load[thread][address],
          std::to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // CAS
      pc = 14;

      s <<
        btor2::eq(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_mem[thread],
          encoder->nids_load[thread][address]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bv,
          std::to_string(nid - 1),
          encoder->nids_const[1],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          std::to_string(nid - 1),
          std::to_string(nid - 3),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // next
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_accu[thread],
          std::to_string(nid - 1),
          encoder->accu_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_accu();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::define_sb_adr ===============================================

TEST_F(btor2_Encoder, define_sb_adr)
{
  add_instruction_set(3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_sb_adr();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder->sb_adr_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 1; // STORE

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_sb_adr[thread],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          encoder->nids_const[1],
          encoder->nids_sb_adr[thread],
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_sb_adr[thread],
          std::to_string(nid - 1),
          encoder->sb_adr_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_sb_adr();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::define_sb_val ===============================================

TEST_F(btor2_Encoder, define_sb_val)
{
  add_instruction_set(3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_sb_val();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder->sb_val_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 1; // STORE

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_sb_val[thread],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          encoder->nids_accu[thread],
          encoder->nids_sb_val[thread],
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bv,
          encoder->nids_sb_val[thread],
          std::to_string(nid - 1),
          encoder->sb_val_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_sb_val();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::define_sb_full ==============================================

TEST_F(btor2_Encoder, define_sb_full)
{
  add_instruction_set(3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_sb_full();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder->sb_full_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 1; // STORE

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_full[thread],
          encoder->nid_false);
      nid++;
      s <<
        btor2::lor(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][pc],
          encoder->nids_sb_full[thread]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_flush[thread],
          encoder->nid_false,
          std::to_string(nid - 1));
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_full[thread],
          std::to_string(nid - 1),
          encoder->sb_full_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_sb_full();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::define_stmt =================================================

TEST_F(btor2_Encoder, define_stmt)
{
  add_dummy_programs(3, 3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_stmt();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder->stmt_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_true);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // ADDI 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // ADDI 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_stmt();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(btor2_Encoder, define_stmt_jmp)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
      "JMP 1\n"
    ));

  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_stmt();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder->stmt_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_true);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // STORE 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][2],
          encoder->nids_exec[thread][2],
          std::to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, 2) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // JMP 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_stmt();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(btor2_Encoder, define_stmt_jmp_conditional)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
      "JNZ 1\n"
      "EXIT 1\n"
    ));

  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_stmt();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder->stmt_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_true);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // STORE 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::ne(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_accu[thread],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][2],
          std::to_string(nid - 1));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][2],
          std::to_string(nid - 1),
          std::to_string(nid - 3),
          verbose ? encoder->debug_symbol(thread, 2) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // JNZ 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // EXIT 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][2],
          btor2::lnot(std::to_string(nid - 10)));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_stmt();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(btor2_Encoder, define_stmt_jmp_start)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
      "JNZ 0\n"
      "EXIT 1\n"
    ));

  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_stmt();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder->stmt_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_true);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ne(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_accu[thread],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][2],
          std::to_string(nid - 1));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][2],
          std::to_string(nid - 1),
          std::to_string(nid - 3),
          verbose ? encoder->debug_symbol(thread, 2) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // STORE 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // JNZ 0
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // EXIT 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][2],
          btor2::lnot(std::to_string(nid - 14)));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_stmt();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(btor2_Encoder, define_stmt_jmp_twice)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
      "JZ 1\n"
      "JNZ 1\n"
      "EXIT 1\n"
    ));

  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_stmt();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder->stmt_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_true);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // STORE 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::eq(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_accu[thread],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][2],
          std::to_string(nid - 1));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][2],
          std::to_string(nid - 1),
          std::to_string(nid - 3),
          verbose ? encoder->debug_symbol(thread, 2) : "");
      nid++;
      s <<
        btor2::ne(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_accu[thread],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][3],
          std::to_string(nid - 1));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][3],
          std::to_string(nid - 1),
          std::to_string(nid - 3),
          verbose ? encoder->debug_symbol(thread, 3) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // JZ 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          std::to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // JNZ 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][2],
          btor2::lnot(std::to_string(nid - 13)));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // EXIT 1
      pc++;

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][3],
          btor2::lnot(std::to_string(nid - 15)));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          std::to_string(nid - 1),
          std::to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          std::to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_stmt();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::define_block ================================================

TEST_F(btor2_Encoder, define_block)
{
  add_instruction_set(3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_block();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder->block_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 15; // CHECK

      s <<
        btor2::init(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_block[1][thread],
          encoder->nid_false);
      nid++;
      s <<
        btor2::lor(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][pc],
          encoder->nids_block[1][thread]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_check[1],
          encoder->nid_false,
          std::to_string(nid - 1));
      nid++;
      s <<
        btor2::next(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_block[1][thread],
          std::to_string(nid - 1),
          encoder->block_var(1, thread));
      nid++;

      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_block();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(btor2_Encoder, define_block_empty)
{
  encoder->define_block();
  ASSERT_EQ("", encoder->str());
}

// btor2::Encoder::define_heap =================================================

TEST_F(btor2_Encoder, define_heap)
{
  add_instruction_set(3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_heap();

  expected = [this, &nid] {
    std::ostringstream s;

    std::string nid_next = encoder->nid_heap;

    if (verbose)
      s << encoder->heap_comment;

    encoder->iterate_threads([this, &nid, &s, &nid_next] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 14; // CAS
      word_t address = 1;

      s <<
        btor2::write(
          std::to_string(nid),
          encoder->sid_heap,
          encoder->nid_heap,
          encoder->nids_sb_adr[thread],
          encoder->nids_sb_val[thread]);
      nid++;
      s <<
        btor2::ite(
          nid_next = std::to_string(nid),
          encoder->sid_heap,
          encoder->nids_flush[thread],
          std::to_string(nid - 1),
          nid_next,
          verbose ? encoder->flush_var() : "");
      nid++;

      if (!thread)
        {
          s <<
            btor2::read(
              encoder->nids_read[address],
              encoder->sid_bv,
              encoder->nid_heap,
              encoder->nids_const[address]);
          nid++;
        }

      s <<
        btor2::eq(
          encoder->nids_eq_sb_adr_adr[thread][address],
          encoder->sid_bool,
          encoder->nids_sb_adr[thread],
          encoder->nids_const[address]);
      nid++;
      s <<
        btor2::land(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_full[thread],
          encoder->nids_eq_sb_adr_adr[thread][address]);
      nid++;
      s <<
        btor2::ite(
          encoder->nids_load[thread][address],
          encoder->sid_bv,
          std::to_string(nid - 1),
          encoder->nids_sb_val[thread],
          encoder->nids_read[address]);
      nid++;
      s <<
        btor2::eq(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_mem[thread],
          encoder->nids_load[thread][address]);
      nid++;
      s <<
        btor2::write(
          std::to_string(nid),
          encoder->sid_heap,
          encoder->nid_heap,
          encoder->nids_const[address],
          encoder->nids_accu[thread]);
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_heap,
          std::to_string(nid - 2),
          std::to_string(nid - 1),
          encoder->nid_heap);
      nid++;
      s <<
        btor2::ite(
          nid_next = std::to_string(nid),
          encoder->sid_heap,
          encoder->nids_exec[thread][pc],
          std::to_string(nid - 1),
          nid_next,
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
    });

    s <<
      btor2::next(
        std::to_string(nid),
        encoder->sid_heap,
        encoder->nid_heap,
        nid_next,
        encoder->heap_sym);
    nid++;

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_heap();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::define_exit_flag ============================================

TEST_F(btor2_Encoder, define_exit_flag)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("EXIT " + std::to_string(i) + eol));

  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_exit_flag();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder->exit_flag_comment;

    s <<
      btor2::init(
        std::to_string(nid),
        encoder->sid_bool,
        encoder->nid_exit_flag,
        encoder->nid_false);
    nid++;
    s <<
      btor2::lor(
        std::to_string(nid),
        encoder->sid_bool,
        encoder->nid_exit_flag,
        encoder->nids_exec[0][0]);
    nid++;
    s <<
      btor2::lor(
        std::to_string(nid),
        encoder->sid_bool,
        encoder->nids_exec[1][0],
        std::to_string(nid - 1));
    nid++;
    s <<
      btor2::lor(
        std::to_string(nid),
        encoder->sid_bool,
        encoder->nids_exec[2][0],
        std::to_string(nid - 1));
    nid++;
    s <<
      btor2::next(
        std::to_string(nid),
        encoder->sid_bool,
        encoder->nid_exit_flag,
        std::to_string(nid - 1),
        encoder->exit_flag_sym);
    nid++;

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_exit_flag();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(btor2_Encoder, define_exit_flag_empty)
{
  encoder->define_exit_flag();
  ASSERT_EQ("", encoder->str());
}

// btor2::Encoder::define_exit_code ============================================

TEST_F(btor2_Encoder, define_exit_code)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("EXIT " + std::to_string(i) + eol));

  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_exit_code();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << encoder->exit_code_comment;

    s <<
      btor2::init(
        std::to_string(nid),
        encoder->sid_bv,
        encoder->nid_exit_code,
        encoder->nids_const[0]);
    nid++;
    s <<
      btor2::ite(
        std::to_string(nid),
        encoder->sid_bv,
        encoder->nids_exec[0][0],
        encoder->nids_const[0],
        encoder->nid_exit_code,
        verbose ? encoder->debug_symbol(0, 0) : "");
    nid++;
    s <<
      btor2::ite(
        std::to_string(nid),
        encoder->sid_bv,
        encoder->nids_exec[1][0],
        encoder->nids_const[1],
        std::to_string(nid - 1),
        verbose ? encoder->debug_symbol(1, 0) : "");
    nid++;
    s <<
      btor2::ite(
        std::to_string(nid),
        encoder->sid_bv,
        encoder->nids_exec[2][0],
        encoder->nids_const[2],
        std::to_string(nid - 1),
        verbose ? encoder->debug_symbol(2, 0) : "");
    nid++;
    s <<
      btor2::next(
        std::to_string(nid),
        encoder->sid_bv,
        encoder->nid_exit_code,
        std::to_string(nid - 1),
        encoder->exit_code_sym);
    nid++;

    s << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_exit_code();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(btor2_Encoder, define_exit_code_empty)
{
  encoder->define_exit_code();
  ASSERT_EQ("", encoder->str());
}

// btor2::Encoder::define_scheduling_constraints ===============================

TEST_F(btor2_Encoder, define_scheduling_constraints)
{
  add_dummy_programs(2);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_scheduling_constraints();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("scheduling constraints");

    std::vector<std::string> args;

    args.insert(
      args.end(),
      encoder->nids_thread.begin(),
      encoder->nids_thread.end());

    args.insert(
      args.end(),
      encoder->nids_flush.begin(),
      encoder->nids_flush.end());

    s << btor2::card_constraint_naive(nid, encoder->sid_bool, args) << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_scheduling_constraints();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(btor2_Encoder, define_scheduling_constraints_exit)
{
  programs.push_back(create_program("EXIT 1"));
  programs.push_back(create_program("EXIT 1"));
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_scheduling_constraints();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("scheduling constraints");

    std::vector<std::string> args;

    args.insert(
      args.end(),
      encoder->nids_thread.begin(),
      encoder->nids_thread.end());

    args.insert(
      args.end(),
      encoder->nids_flush.begin(),
      encoder->nids_flush.end());

    args.push_back(encoder->nid_exit_flag);

    s << btor2::card_constraint_naive(nid, encoder->sid_bool, args) << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_scheduling_constraints();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(btor2_Encoder, define_scheduling_constraints_single_thread)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_scheduling_constraints();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("scheduling constraints");

    std::vector<std::string> args;

    args.reserve(encoder->num_threads * 2);

    args.insert(
      args.end(),
      encoder->nids_thread.begin(),
      encoder->nids_thread.end());

    args.insert(
      args.end(),
      encoder->nids_flush.begin(),
      encoder->nids_flush.end());

    s << btor2::card_constraint_naive(nid, encoder->sid_bool, args) << eol;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_scheduling_constraints();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::define_store_buffer_constraints =============================

TEST_F(btor2_Encoder, define_store_buffer_constraints)
{
  // add_instruction_set(3);
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "STORE 1\n"
      "FENCE\n"
      "CAS 1\n"
    ));
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_store_buffer_constraints();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("store buffer constraints");

    encoder->iterate_threads([this, &nid, &s] {
      s <<
        btor2::lor(nid, encoder->sid_bool, encoder->nids_stmt[encoder->thread]);
      s <<
        btor2::implies(
          std::to_string(nid),
          encoder->sid_bool,
          std::to_string(nid - 1),
          btor2::lnot(encoder->nids_thread[encoder->thread]));
      nid++;
      s <<
        btor2::ite(
          std::to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_full[encoder->thread],
          std::to_string(nid - 1),
          btor2::lnot(encoder->nids_flush[encoder->thread]));
      nid++;
      s << btor2::constraint(nid);
      s << eol;
    });

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_store_buffer_constraints();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::define_checkpoint_contraints ================================

TEST_F(btor2_Encoder, define_checkpoint_contraints)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("CHECK 1\n"));
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_checkpoint_constraints();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("checkpoint constraints");

    for (const auto & [id, threads] : encoder->nids_block)
      {
        std::string nid_not_check = btor2::lnot(encoder->nids_check[1]);

        for (const auto & [thread, nid_block] : threads)
          {
            s <<
              btor2::land(
                std::to_string(nid),
                encoder->sid_bool,
                nid_block,
                nid_not_check);
            nid++;
            s <<
              btor2::implies(
                std::to_string(nid),
                encoder->sid_bool,
                std::to_string(nid - 1),
                btor2::lnot(encoder->nids_thread[thread]));
            nid++;
            s << btor2::constraint(nid, encoder->block_var(id, thread));

            s << eol;
          }
      }

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_checkpoint_constraints();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(btor2_Encoder, define_checkpoint_contraints_empty)
{
  encoder->define_checkpoint_constraints();
  ASSERT_EQ("", encoder->str());
}

// btor2::Encoder::define_bound ================================================

TEST_F(btor2_Encoder, define_bound)
{
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_bound();

  expected = [this, &nid] {
    std::ostringstream s;

    if (verbose)
      s << btor2::comment_section("bound")
        << btor2::comment("step counter")
        << eol;

    std::string nid_ctr = std::to_string(nid);

    s << btor2::state(nid_ctr, encoder->sid_bv, "k");
    nid++;
    s <<
      btor2::init(
        std::to_string(nid),
        encoder->sid_bv,
        nid_ctr,
        encoder->nids_const[0]);
    nid++;
    s <<
      btor2::add(
        std::to_string(nid),
        encoder->sid_bv,
        encoder->nids_const[1],
        nid_ctr);
    nid++;
    s <<
      btor2::next(
        std::to_string(nid),
        encoder->sid_bv,
        nid_ctr,
        std::to_string(nid - 1));
    nid++;
    s << eol;
    if (verbose)
      s << btor2::comment("bound (" + std::to_string(encoder->bound) + ")")
        << eol;
    s <<
      btor2::eq(
        std::to_string(nid),
        encoder->sid_bool,
        encoder->nids_const[encoder->bound],
        nid_ctr);
    nid++;
    s << btor2::bad(std::to_string(nid), std::to_string(nid - 1));

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());

  // verbosity
  reset_encoder();
  init_state_definitions();

  verbose = false;
  nid = encoder->node;
  encoder->define_bound();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

// btor2::Encoder::encode ======================================================

TEST_F(btor2_Encoder, encode_check)
{
  // concurrent increment using CHECK
  encode(
    {"increment.check.thread.0.asm", "increment.check.thread.n.asm"},
    "increment.check.t2.k16.btor2",
    16);
}

TEST_F(btor2_Encoder, encode_cas)
{
  // concurrent increment using CAS
  encode(
    {"increment.cas.asm", "increment.cas.asm"},
    "increment.cas.t2.k16.btor2",
    16);
}

TEST_F(btor2_Encoder, LOAD)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Load load {Type::none, address};

  ASSERT_EQ(
    encoder->nids_load[encoder->thread][address],
    encoder->encode(load));
  ASSERT_EQ(expected_load(nid, address), encoder->str());
}

TEST_F(btor2_Encoder, LOAD_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Load load {Type::none, address, true};

  ASSERT_EQ(
    encoder->nids_load_indirect[encoder->thread][address],
    encoder->encode(load));
  ASSERT_EQ(expected_load_indirect(nid, address), encoder->str());
}

TEST_F(btor2_Encoder, STORE)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  word_t address = 0;

  Instruction::Store store {Type::none, address};

  encoder->update = ::Encoder::State::sb_adr;
  ASSERT_EQ(encoder->nids_const[address], encoder->encode(store));

  encoder->update = ::Encoder::State::sb_val;
  ASSERT_EQ(encoder->nids_accu[0], encoder->encode(store));
}

TEST_F(btor2_Encoder, STORE_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Store store {Type::none, address, true};

  encoder->update = ::Encoder::State::sb_adr;
  ASSERT_EQ(
    encoder->nids_load[encoder->thread][address],
    encoder->encode(store));
  ASSERT_EQ(expected_load(nid, address), encoder->str());

  encoder->update = ::Encoder::State::sb_val;
  ASSERT_EQ(encoder->nids_accu[0], encoder->encode(store));
}

TEST_F(btor2_Encoder, ADD)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Add add {Type::none, address};

  std::string nid_add = encoder->encode(add);

  expected = [this, &nid, &address, &nid_add] {
    std::ostringstream s;

    s << expected_load(nid, address);
    s <<
      btor2::add(
        nid_add,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, ADD_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Add add {Type::none, address, true};

  std::string nid_add = encoder->encode(add);

  expected = [this, &nid, &address, &nid_add] {
    std::ostringstream s;

    s << expected_load_indirect(nid, address);
    s <<
      btor2::add(
        nid_add,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, ADDI)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t value = 0;

  Instruction::Addi addi {Type::none, value};

  std::string nid_addi = encoder->encode(addi);

  expected = [this, &nid, &value, &nid_addi] {
    std::ostringstream s;

    s <<
      btor2::add(
        nid_addi,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        encoder->nids_const[value]);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, SUB)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Sub sub {Type::none, address};

  std::string nid_sub = encoder->encode(sub);

  expected = [this, &nid, &address, &nid_sub] {
    std::ostringstream s;

    s << expected_load(nid, address);
    s <<
      btor2::sub(
        nid_sub,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, SUB_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Sub sub {Type::none, address, true};

  std::string nid_sub = encoder->encode(sub);

  expected = [this, &nid, &address, &nid_sub] {
    std::ostringstream s;

    s << expected_load_indirect(nid, address);
    s <<
      btor2::sub(
        nid_sub,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, SUBI)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t value = 0;

  Instruction::Subi subi {Type::none, value};

  std::string nid_subi = encoder->encode(subi);

  expected = [this, &nid, &value, &nid_subi] {
    std::ostringstream s;

    s <<
      btor2::sub(
        nid_subi,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        encoder->nids_const[value]);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, MUL)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Mul mul {Type::none, address};

  std::string nid_mul = encoder->encode(mul);

  expected = [this, &nid, &address, &nid_mul] {
    std::ostringstream s;

    s << expected_load(nid, address);
    s <<
      btor2::mul(
        nid_mul,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, MUL_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Mul mul {Type::none, address, true};

  std::string nid_mul = encoder->encode(mul);

  expected = [this, &nid, &address, &nid_mul] {
    std::ostringstream s;

    s << expected_load_indirect(nid, address);
    s <<
      btor2::mul(
        nid_mul,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, MULI)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t value = 0;

  Instruction::Muli muli {Type::none, value};

  std::string nid_muli = encoder->encode(muli);

  expected = [this, &nid, &value, &nid_muli] {
    std::ostringstream s;

    s <<
      btor2::mul(
        nid_muli,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        encoder->nids_const[value]);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, CMP)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Cmp cmp {Type::none, address};

  std::string nid_cmp = encoder->encode(cmp);

  expected = [this, &nid, &address, &nid_cmp] {
    std::ostringstream s;

    s << expected_load(nid, address);
    s <<
      btor2::sub(
        nid_cmp,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, CMP_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Cmp cmp {Type::none, address, true};

  std::string nid_cmp = encoder->encode(cmp);

  expected = [this, &nid, &address, &nid_cmp] {
    std::ostringstream s;

    s << expected_load_indirect(nid, address);
    s <<
      btor2::sub(
        nid_cmp,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        std::to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, JMP)
{
  Instruction::Jmp jmp {Type::none, 0};

  ASSERT_EQ("", encoder->encode(jmp));
  ASSERT_EQ("", encoder->str());
}

TEST_F(btor2_Encoder, JZ)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  Instruction::Jz jz {Type::none, 0};

  std::string nid_jz = encoder->encode(jz);

  expected = [this, &nid, &nid_jz] {
    std::ostringstream s;

    s <<
      btor2::eq(
        nid_jz,
        encoder->sid_bool,
        encoder->nids_accu[encoder->thread],
        encoder->nids_const[0]);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, JNZ)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  Instruction::Jnz jnz {Type::none, 0};

  std::string nid_jnz = encoder->encode(jnz);

  expected = [this, &nid, &nid_jnz] {
    std::ostringstream s;

    s <<
      btor2::ne(
        nid_jnz,
        encoder->sid_bool,
        encoder->nids_accu[encoder->thread],
        encoder->nids_const[0]);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, JS)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  Instruction::Js js {Type::none, 0};

  std::string nid_js = encoder->encode(js);

  expected = [this, &nid, &nid_js] {
    std::ostringstream s;

    s <<
      btor2::slice(
        nid_js,
        encoder->sid_bool,
        encoder->nids_accu[encoder->thread],
        encoder->msb,
        encoder->msb);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, JNS)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  Instruction::Jns jns {Type::none, 0};

  std::string nid_jns = encoder->encode(jns);

  expected = [this, &nid, &nid_jns] {
    std::ostringstream s;

    s <<
      btor2::slice(
        nid_jns.substr(1),
        encoder->sid_bool,
        encoder->nids_accu[encoder->thread],
        encoder->msb,
        encoder->msb);
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, JNZNS)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  Instruction::Jnzns jnzns {Type::none, 0};

  std::string nid_jnzns = encoder->encode(jnzns);

  expected = [this, &nid, &nid_jnzns] {
    std::ostringstream s;

    s <<
      btor2::ne(
        std::to_string(nid),
        encoder->sid_bool,
        encoder->nids_accu[encoder->thread],
        encoder->nids_const[0]);
    nid++;
    s <<
      btor2::slice(
        std::to_string(nid),
        encoder->sid_bool,
        encoder->nids_accu[encoder->thread],
        encoder->msb,
        encoder->msb);
    nid++;
    s <<
      btor2::land(
        nid_jnzns,
        encoder->sid_bool,
        std::to_string(nid - 2),
        btor2::lnot(std::to_string(nid - 1)));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, MEM)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Mem mem {Type::none, address};

  ASSERT_EQ(
    encoder->nids_load[encoder->thread][address],
    encoder->encode(mem));
  ASSERT_EQ(expected_load(nid, address), encoder->str());
}

TEST_F(btor2_Encoder, MEM_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Mem mem {Type::none, address, true};

  ASSERT_EQ(
    encoder->nids_load_indirect[encoder->thread][address],
    encoder->encode(mem));
  ASSERT_EQ(expected_load_indirect(nid, address), encoder->str());
}

TEST_F(btor2_Encoder, CAS)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Cas cas {Type::none, address};

  std::string nid_cas;

  expected = [this, &nid, &address, &nid_cas] {
    std::ostringstream s;

    if (encoder->update == ::Encoder::State::accu)
      {
        s << expected_load(nid, address);
        s <<
          btor2::eq(
            encoder->nids_cas[encoder->thread][address],
            encoder->sid_bool,
            encoder->nids_mem[encoder->thread],
            encoder->nids_load[encoder->thread][address]);
        nid++;
        s <<
          btor2::ite(
            nid_cas,
            encoder->sid_bv,
            encoder->nids_cas[encoder->thread][address],
            encoder->nids_const[1],
            encoder->nids_const[0]);
        nid++;
      }
    else if (encoder->update == ::Encoder::State::heap)
      {
        s <<
          btor2::write(
            std::to_string(nid),
            encoder->sid_heap,
            encoder->nid_heap,
            encoder->nids_const[address],
            encoder->nids_accu[encoder->thread]);
        nid++;
        s <<
          btor2::ite(
            nid_cas,
            encoder->sid_heap,
            encoder->nids_cas[encoder->thread][address],
            std::to_string(nid - 1),
            encoder->nid_heap);
        nid++;
      }

    return s.str();
  };

  encoder->update = ::Encoder::State::accu;
  nid_cas = encoder->encode(cas);
  ASSERT_EQ(expected(), encoder->str());

  encoder->formula.str("");

  encoder->update = ::Encoder::State::heap;
  nid_cas = encoder->encode(cas);
  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, CAS_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Instruction::Cas cas {Type::none, address, true};

  std::string nid_cas;

  expected = [this, &nid, &address, &nid_cas] {
    std::ostringstream s;

    if (encoder->update == ::Encoder::State::accu)
      {
        s << expected_load(nid, address);
        s <<
          btor2::eq(
            encoder->nids_cas_indirect[encoder->thread][address],
            encoder->sid_bool,
            encoder->nids_mem[encoder->thread],
            encoder->nids_load[encoder->thread][address]);
        nid++;
        s <<
          btor2::ite(
            nid_cas,
            encoder->sid_bv,
            encoder->nids_cas_indirect[encoder->thread][address],
            encoder->nids_const[1],
            encoder->nids_const[0]);
        nid++;
      }
    else if (encoder->update == ::Encoder::State::heap)
      {
        s <<
          btor2::write(
            std::to_string(nid),
            encoder->sid_heap,
            encoder->nid_heap,
            encoder->nids_load[encoder->thread][address],
            encoder->nids_accu[encoder->thread]);
        nid++;
        s <<
          btor2::ite(
            nid_cas,
            encoder->sid_heap,
            encoder->nids_cas_indirect[encoder->thread][address],
            std::to_string(nid - 1),
            encoder->nid_heap);
        nid++;
      }

    return s.str();
  };

  encoder->update = ::Encoder::State::accu;
  nid_cas = encoder->encode(cas);
  ASSERT_EQ(expected(), encoder->str());

  encoder->formula.str("");

  encoder->update = ::Encoder::State::heap;
  nid_cas = encoder->encode(cas);
  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(btor2_Encoder, CHECK)
{
  Instruction::Check check {Type::none, 1};

  ASSERT_EQ("", encoder->encode(check));
  ASSERT_EQ("", encoder->str());
}

TEST_F(btor2_Encoder, EXIT)
{
  Instruction::Exit exit {Type::none, 1};

  ASSERT_EQ(encoder->nids_const[1], encoder->encode(exit));
  ASSERT_EQ("", encoder->str());
}

} // namespace test
