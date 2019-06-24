#include "test_encoder.hh"

#include <functional>

using namespace std;

// TODO remove - debug only
#include "btor2.hh"
#include "btormc.hh"
void evaluate (string & formula)
{
  BtorMC btormc(20);
  cout << "running btormc..." << eol;
  btormc.sat(formula);
}

struct Btor2_Encoder_Test : public Test::Encoder<Btor2_Encoder>
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

  function<string()> expected = [] { return ""; };

  string expected_load (btor2::nid_t & nid, const word_t address)
    {
      ostringstream s;
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
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_full[thread],
          encoder->nids_eq_sb_adr_adr[thread][address]);
      nid++;
      s <<
        btor2::ite(
          encoder->nids_load[thread][address],
          encoder->sid_bv,
          to_string(nid - 1),
          encoder->nids_sb_val[thread],
          encoder->nids_read[address]);
      nid++;

      return s.str();
    }

  string expected_load_indirect (btor2::nid_t & nid, const word_t address)
    {
      ostringstream s;
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
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_adr[thread],
          encoder->nids_read[address]);
      nid++;

      string nid_ite_eq_sb_adr_read_adr = to_string(nid);

      s <<
        btor2::ite(
          nid_ite_eq_sb_adr_read_adr,
          encoder->sid_bv,
          to_string(nid - 1),
          encoder->nids_sb_val[thread],
          encoder->nids_read_indirect[address]);
      nid++;

      if (!address || thread)
        {
          s <<
            btor2::read(
              to_string(nid),
              encoder->sid_bv,
              encoder->nid_heap,
              encoder->nids_sb_val[thread]);
          nid++;
          s <<
            btor2::read(
              to_string(nid),
              encoder->sid_bv,
              encoder->nid_heap,
              to_string(nid - 1));
          nid++;
          s <<
            btor2::eq(
              to_string(nid),
              encoder->sid_bool,
              encoder->nids_sb_adr[thread],
              to_string(nid - 2));
          nid++;
          s<<
            btor2::ite(
              encoder->nids_ite_eq_sb_adr_read_sb_val[thread],
              encoder->sid_bv,
              to_string(nid - 1),
              encoder->nids_sb_val[thread],
              to_string(nid - 2));
          nid++;
        }

      s <<
        btor2::eq(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_val[thread],
          encoder->nids_const[address]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bv,
          to_string(nid - 1),
          encoder->nids_sb_val[thread],
          encoder->nids_ite_eq_sb_adr_read_sb_val[thread]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_eq_sb_adr_adr[thread][address],
          to_string(nid - 1),
          nid_ite_eq_sb_adr_read_adr);
      nid++;
      s <<
        btor2::ite(
          encoder->nids_load_indirect[thread][address],
          encoder->sid_bv,
          encoder->nids_sb_full[thread],
          to_string(nid - 1),
          encoder->nids_read_indirect[address]);
      nid++;

      return s.str();
    }
};

/* Btor2_Encoder::load ********************************************************/
TEST_F(Btor2_Encoder_Test, load)
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

TEST_F(Btor2_Encoder_Test, load_indirect)
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

/* Btor2_Encoder::declare_sorts ***********************************************/
TEST_F(Btor2_Encoder_Test, declare_sorts)
{
  encoder->declare_sorts();

  expected = [this] {
    ostringstream s;

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

/* Btor2_Encoder::declare_constants *******************************************/
TEST_F(Btor2_Encoder_Test, declare_constants)
{
  for (size_t thread = 0; thread < 3; thread++)
    {
      Program_ptr program = make_shared<Program>();

      programs.push_back(program);

      for (size_t pc = 0; pc < 3; pc++)
        program->push_back(Instruction::Set::create("ADDI", thread + pc + 1));
    }

  reset_encoder();

  encoder->declare_sorts();
  encoder->formula.str("");

  encoder->declare_constants();

  expected = [this] {
    ostringstream s;

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

/* Btor2_Encoder::declare_accu ************************************************/
TEST_F(Btor2_Encoder_Test, declare_accu)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_accu();

  expected = [this] {
    ostringstream s;

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

/* Btor2_Encoder::declare_mem *************************************************/
TEST_F(Btor2_Encoder_Test, declare_mem)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_mem();

  expected = [this] {
    ostringstream s;

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

/* Btor2_Encoder::declare_sb_adr **********************************************/
TEST_F(Btor2_Encoder_Test, declare_sb_adr)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_sb_adr();

  expected = [this] {
    ostringstream s;

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

/* Btor2_Encoder::declare_sb_val **********************************************/
TEST_F(Btor2_Encoder_Test, declare_sb_val)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_sb_val();

  expected = [this] {
    ostringstream s;

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

/* Btor2_Encoder::declare_sb_full *********************************************/
TEST_F(Btor2_Encoder_Test, declare_sb_full)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_sb_full();

  expected = [this] {
    ostringstream s;

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

/* Btor2_Encoder::declare_stmt ************************************************/
TEST_F(Btor2_Encoder_Test, declare_stmt)
{
  add_dummy_programs(3, 3);
  reset_encoder();
  init_declarations();

  encoder->declare_stmt();

  expected = [this] {
    ostringstream s;

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

/* Btor2_Encoder::declare_block ***********************************************/
TEST_F(Btor2_Encoder_Test, declare_block)
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
    ostringstream s;

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

TEST_F(Btor2_Encoder_Test, declare_block_empty)
{
  encoder->declare_block();

  ASSERT_EQ("", encoder->str());
}

/* Btor2_Encoder::declare_heap ************************************************/
TEST_F(Btor2_Encoder_Test, declare_heap)
{
  init_declarations();

  encoder->declare_heap();

  expected = [this] {
    ostringstream s;

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

/* Btor2_Encoder::declare_exit_flag *******************************************/
TEST_F(Btor2_Encoder_Test, declare_exit_flag)
{
  programs.push_back(create_program("EXIT 1\n"));
  reset_encoder();
  init_declarations();

  encoder->declare_exit_flag();

  expected = [this] {
    ostringstream s;

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

TEST_F(Btor2_Encoder_Test, declare_exit_flag_empty)
{
  encoder->declare_exit_flag();

  ASSERT_EQ("", encoder->str());
}

/* Btor2_Encoder::declare_exit_code *******************************************/
TEST_F(Btor2_Encoder_Test, declare_exit_code)
{
  programs.push_back(create_program("EXIT 1\n"));
  reset_encoder();
  init_declarations();

  encoder->declare_exit_code();

  expected = [this] {
    ostringstream s;

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

/* Btor2_Encoder::declare_thread **********************************************/
TEST_F(Btor2_Encoder_Test, declare_thread)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_thread();

  expected = [this] {
    ostringstream s;

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

/* Btor2_Encoder::declare_flush ***********************************************/
TEST_F(Btor2_Encoder_Test, declare_flush)
{
  add_dummy_programs(3);
  reset_encoder();
  init_declarations();

  encoder->declare_flush();

  expected = [this] {
    ostringstream s;

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

/* Btor2_Encoder::define_exec *************************************************/
TEST_F(Btor2_Encoder_Test, define_exec)
{
  add_dummy_programs(3, 3);
  reset_encoder();
  init_definitions();

  encoder->define_exec();

  expected = [this] {
    ostringstream s;

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

/* Btor2_Encoder::define_check ************************************************/
TEST_F(Btor2_Encoder_Test, define_check)
{
  add_instruction_set(3);
  reset_encoder();
  init_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_check();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << encoder->check_comment;

    vector<string> blocks;

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

TEST_F(Btor2_Encoder_Test, define_check_empty)
{
  encoder->define_check();
  ASSERT_EQ("", encoder->str());
}

/* Btor2_Encoder::define_accu *************************************************/
TEST_F(Btor2_Encoder_Test, define_accu)
{
  add_instruction_set(3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_accu();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << encoder->accu_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 0;
      word_t address = 1;

      // init
      s <<
        btor2::init(
          to_string(nid),
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
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_full[thread],
          encoder->nids_eq_sb_adr_adr[thread][address]);
      nid++;
      s <<
        btor2::ite(
          encoder->nids_load[thread][address],
          encoder->sid_bv,
          to_string(nid - 1),
          encoder->nids_sb_val[thread],
          encoder->nids_read[address]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
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
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_accu[thread],
          encoder->nids_load[thread][address]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          to_string(nid - 1),
          to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // ADDI
      pc = 3;

      s <<
        btor2::add(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_accu[thread],
          encoder->nids_const[1]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          to_string(nid - 1),
          to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // SUB
      pc = 4;

      s <<
        btor2::sub(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_accu[thread],
          encoder->nids_load[thread][address]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          to_string(nid - 1),
          to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // SUBI
      pc = 5;

      s <<
        btor2::sub(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_accu[thread],
          encoder->nids_const[1]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          to_string(nid - 1),
          to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // CMP
      pc = 6;

      s <<
        btor2::sub(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_accu[thread],
          encoder->nids_load[thread][address]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          to_string(nid - 1),
          to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // MEM
      pc = 13;

      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          encoder->nids_load[thread][address],
          to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // CAS
      pc = 14;

      s <<
        btor2::eq(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_mem[thread],
          encoder->nids_load[thread][address]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bv,
          to_string(nid - 1),
          encoder->nids_const[1],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          to_string(nid - 1),
          to_string(nid - 3),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;

      // next
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_accu[thread],
          to_string(nid - 1),
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

/* Btor2_Encoder::define_sb_adr ***********************************************/
TEST_F(Btor2_Encoder_Test, define_sb_adr)
{
  add_instruction_set(3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_sb_adr();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << encoder->sb_adr_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 1; // STORE

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_sb_adr[thread],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          encoder->nids_const[1],
          encoder->nids_sb_adr[thread],
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_sb_adr[thread],
          to_string(nid - 1),
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

/* Btor2_Encoder::define_sb_val ***********************************************/
TEST_F(Btor2_Encoder_Test, define_sb_val)
{
  add_instruction_set(3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_sb_val();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << encoder->sb_val_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 1; // STORE

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_sb_val[thread],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_exec[thread][pc],
          encoder->nids_accu[thread],
          encoder->nids_sb_val[thread],
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bv,
          encoder->nids_sb_val[thread],
          to_string(nid - 1),
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

/* Btor2_Encoder::define_sb_full **********************************************/
TEST_F(Btor2_Encoder_Test, define_sb_full)
{
  add_instruction_set(3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_sb_full();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << encoder->sb_full_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 1; // STORE

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_full[thread],
          encoder->nid_false);
      nid++;
      s <<
        btor2::lor(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][pc],
          encoder->nids_sb_full[thread]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_flush[thread],
          encoder->nid_false,
          to_string(nid - 1));
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_full[thread],
          to_string(nid - 1),
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

/* Btor2_Encoder::define_stmt *************************************************/
TEST_F(Btor2_Encoder_Test, define_stmt)
{
  add_dummy_programs(3, 3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_stmt();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << encoder->stmt_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_true);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // ADDI 1
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // ADDI 1
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
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

TEST_F(Btor2_Encoder_Test, define_stmt_jmp)
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
    ostringstream s;

    if (verbose)
      s << encoder->stmt_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_true);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // STORE 1
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][2],
          encoder->nids_exec[thread][2],
          to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, 2) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // JMP 1
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
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

TEST_F(Btor2_Encoder_Test, define_stmt_jmp_conditional)
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
    ostringstream s;

    if (verbose)
      s << encoder->stmt_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_true);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // STORE 1
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::ne(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_accu[thread],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][2],
          to_string(nid - 1));
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][2],
          to_string(nid - 1),
          to_string(nid - 3),
          verbose ? encoder->debug_symbol(thread, 2) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // JNZ 1
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // EXIT 1
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][2],
          btor2::lnot(to_string(nid - 10)));
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          to_string(nid - 1),
          to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
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

TEST_F(Btor2_Encoder_Test, define_stmt_jmp_start)
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
    ostringstream s;

    if (verbose)
      s << encoder->stmt_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_true);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ne(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_accu[thread],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][2],
          to_string(nid - 1));
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][2],
          to_string(nid - 1),
          to_string(nid - 3),
          verbose ? encoder->debug_symbol(thread, 2) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // STORE 1
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // JNZ 0
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // EXIT 1
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][2],
          btor2::lnot(to_string(nid - 14)));
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          to_string(nid - 1),
          to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
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

TEST_F(Btor2_Encoder_Test, define_stmt_jmp_twice)
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
    ostringstream s;

    if (verbose)
      s << encoder->stmt_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 0;

      // ADDI 1
      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_true);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // STORE 1
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::eq(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_accu[thread],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][2],
          to_string(nid - 1));
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][2],
          to_string(nid - 1),
          to_string(nid - 3),
          verbose ? encoder->debug_symbol(thread, 2) : "");
      nid++;
      s <<
        btor2::ne(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_accu[thread],
          encoder->nids_const[0]);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][3],
          to_string(nid - 1));
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][3],
          to_string(nid - 1),
          to_string(nid - 3),
          verbose ? encoder->debug_symbol(thread, 3) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // JZ 1
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          encoder->nids_exec[thread][pc - 1u],
          to_string(nid - 1),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // JNZ 1
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][2],
          btor2::lnot(to_string(nid - 13)));
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          to_string(nid - 1),
          to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
          encoder->stmt_var());
      nid++;

      s << eol;

      // EXIT 1
      pc++;

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          encoder->nid_false);
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          btor2::lnot(encoder->nids_exec[thread][pc]),
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
      s <<
        btor2::land(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][3],
          btor2::lnot(to_string(nid - 15)));
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc - 1u],
          to_string(nid - 1),
          to_string(nid - 2),
          verbose ? encoder->debug_symbol(thread, pc - 1u) : "");
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_stmt[thread][pc],
          to_string(nid - 1),
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

/* Btor2_Encoder::define_block ************************************************/
TEST_F(Btor2_Encoder_Test, define_block)
{
  add_instruction_set(3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_block();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << encoder->block_comment;

    encoder->iterate_threads([this, &nid, &s] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 15; // CHECK

      s <<
        btor2::init(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_block[1][thread],
          encoder->nid_false);
      nid++;
      s <<
        btor2::lor(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_exec[thread][pc],
          encoder->nids_block[1][thread]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_check[1],
          encoder->nid_false,
          to_string(nid - 1));
      nid++;
      s <<
        btor2::next(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_block[1][thread],
          to_string(nid - 1),
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

TEST_F(Btor2_Encoder_Test, define_block_empty)
{
  encoder->define_block();
  ASSERT_EQ("", encoder->str());
}

/* Btor2_Encoder::define_heap *************************************************/
TEST_F(Btor2_Encoder_Test, define_heap)
{
  add_instruction_set(3);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_heap();

  expected = [this, &nid] {
    ostringstream s;

    string nid_next = encoder->nid_heap;

    if (verbose)
      s << encoder->heap_comment;

    encoder->iterate_threads([this, &nid, &s, &nid_next] {
      word_t & thread = encoder->thread;
      word_t & pc = encoder->pc = 14; // CAS
      word_t address = 1;

      s <<
        btor2::write(
          to_string(nid),
          encoder->sid_heap,
          encoder->nid_heap,
          encoder->nids_sb_adr[thread],
          encoder->nids_sb_val[thread]);
      nid++;
      s <<
        btor2::ite(
          nid_next = to_string(nid),
          encoder->sid_heap,
          encoder->nids_flush[thread],
          to_string(nid - 1),
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
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_full[thread],
          encoder->nids_eq_sb_adr_adr[thread][address]);
      nid++;
      s <<
        btor2::ite(
          encoder->nids_load[thread][address],
          encoder->sid_bv,
          to_string(nid - 1),
          encoder->nids_sb_val[thread],
          encoder->nids_read[address]);
      nid++;
      s <<
        btor2::eq(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_mem[thread],
          encoder->nids_load[thread][address]);
      nid++;
      s <<
        btor2::write(
          to_string(nid),
          encoder->sid_heap,
          encoder->nid_heap,
          encoder->nids_const[address],
          encoder->nids_accu[thread]);
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_heap,
          to_string(nid - 2),
          to_string(nid - 1),
          encoder->nid_heap);
      nid++;
      s <<
        btor2::ite(
          nid_next = to_string(nid),
          encoder->sid_heap,
          encoder->nids_exec[thread][pc],
          to_string(nid - 1),
          nid_next,
          verbose ? encoder->debug_symbol(thread, pc) : "");
      nid++;
    });

    s <<
      btor2::next(
        to_string(nid),
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

/* Btor2_Encoder::define_exit_flag ********************************************/
TEST_F(Btor2_Encoder_Test, define_exit_flag)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("EXIT " + to_string(i) + eol));

  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_exit_flag();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << encoder->exit_flag_comment;

    s <<
      btor2::init(
        to_string(nid),
        encoder->sid_bool,
        encoder->nid_exit_flag,
        encoder->nid_false);
    nid++;
    s <<
      btor2::lor(
        to_string(nid),
        encoder->sid_bool,
        encoder->nid_exit_flag,
        encoder->nids_exec[0][0]);
    nid++;
    s <<
      btor2::lor(
        to_string(nid),
        encoder->sid_bool,
        encoder->nids_exec[1][0],
        to_string(nid - 1));
    nid++;
    s <<
      btor2::lor(
        to_string(nid),
        encoder->sid_bool,
        encoder->nids_exec[2][0],
        to_string(nid - 1));
    nid++;
    s <<
      btor2::next(
        to_string(nid),
        encoder->sid_bool,
        encoder->nid_exit_flag,
        to_string(nid - 1),
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

TEST_F(Btor2_Encoder_Test, define_exit_flag_empty)
{
  encoder->define_exit_flag();
  ASSERT_EQ("", encoder->str());
}

/* Btor2_Encoder::define_exit_code ********************************************/
TEST_F(Btor2_Encoder_Test, define_exit_code)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("EXIT " + to_string(i) + eol));

  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_exit_code();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << encoder->exit_code_comment;

    s <<
      btor2::init(
        to_string(nid),
        encoder->sid_bv,
        encoder->nid_exit_code,
        encoder->nids_const[0]);
    nid++;
    s <<
      btor2::ite(
        to_string(nid),
        encoder->sid_bv,
        encoder->nids_exec[0][0],
        encoder->nids_const[0],
        encoder->nid_exit_code,
        verbose ? encoder->debug_symbol(0, 0) : "");
    nid++;
    s <<
      btor2::ite(
        to_string(nid),
        encoder->sid_bv,
        encoder->nids_exec[1][0],
        encoder->nids_const[1],
        to_string(nid - 1),
        verbose ? encoder->debug_symbol(1, 0) : "");
    nid++;
    s <<
      btor2::ite(
        to_string(nid),
        encoder->sid_bv,
        encoder->nids_exec[2][0],
        encoder->nids_const[2],
        to_string(nid - 1),
        verbose ? encoder->debug_symbol(2, 0) : "");
    nid++;
    s <<
      btor2::next(
        to_string(nid),
        encoder->sid_bv,
        encoder->nid_exit_code,
        to_string(nid - 1),
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

TEST_F(Btor2_Encoder_Test, define_exit_code_empty)
{
  encoder->define_exit_code();
  ASSERT_EQ("", encoder->str());
}

/* Btor2_Encoder::define_scheduling_constraints *******************************/
TEST_F(Btor2_Encoder_Test, define_scheduling_constraints)
{
  add_dummy_programs(2);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_scheduling_constraints();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << btor2::comment_section("scheduling constraints");

    vector<string> args;

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

TEST_F(Btor2_Encoder_Test, define_scheduling_constraints_exit)
{
  programs.push_back(create_program("EXIT 1"));
  programs.push_back(create_program("EXIT 1"));
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_scheduling_constraints();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << btor2::comment_section("scheduling constraints");

    vector<string> args;

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

TEST_F(Btor2_Encoder_Test, define_scheduling_constraints_single_thread)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_scheduling_constraints();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << btor2::comment_section("scheduling constraints");

    vector<string> args;

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

/* Btor2_Encoder::define_store_buffer_constraints *****************************/
TEST_F(Btor2_Encoder_Test, define_store_buffer_constraints)
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
    ostringstream s;

    if (verbose)
      s << btor2::comment_section("store buffer constraints");

    encoder->iterate_threads([this, &nid, &s] {
      s <<
        btor2::lor(nid, encoder->sid_bool, encoder->nids_stmt[encoder->thread]);
      s <<
        btor2::implies(
          to_string(nid),
          encoder->sid_bool,
          to_string(nid - 1),
          btor2::lnot(encoder->nids_thread[encoder->thread]));
      nid++;
      s <<
        btor2::ite(
          to_string(nid),
          encoder->sid_bool,
          encoder->nids_sb_full[encoder->thread],
          to_string(nid - 1),
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

/* Btor2_Encoder::define_checkpoint_contraints ********************************/
TEST_F(Btor2_Encoder_Test, define_checkpoint_contraints)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("CHECK 1\n"));
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_checkpoint_contraints();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << btor2::comment_section("checkpoint constraints");

    for (const auto & [id, threads] : encoder->nids_block)
      {
        string nid_not_check = btor2::lnot(encoder->nids_check[1]);

        for (const auto & [thread, nid_block] : threads)
          {
            s <<
              btor2::land(
                to_string(nid),
                encoder->sid_bool,
                nid_block,
                nid_not_check);
            nid++;
            s <<
              btor2::implies(
                to_string(nid),
                encoder->sid_bool,
                to_string(nid - 1),
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
  encoder->define_checkpoint_contraints();
  ASSERT_EQ(expected(), encoder->str());
  verbose = true;
}

TEST_F(Btor2_Encoder_Test, define_checkpoint_contraints_empty)
{
  encoder->define_checkpoint_contraints();
  ASSERT_EQ("", encoder->str());
}

/* Btor2_Encoder::define_bound ************************************************/
TEST_F(Btor2_Encoder_Test, define_bound)
{
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  encoder->define_bound();

  expected = [this, &nid] {
    ostringstream s;

    if (verbose)
      s << btor2::comment_section("bound")
        << btor2::comment("step counter")
        << eol;

    string nid_ctr = to_string(nid);

    s << btor2::state(nid_ctr, encoder->sid_bv, "k");
    nid++;
    s <<
      btor2::init(
        to_string(nid),
        encoder->sid_bv,
        nid_ctr,
        encoder->nids_const[0]);
    nid++;
    s <<
      btor2::add(
        to_string(nid),
        encoder->sid_bv,
        encoder->nids_const[1],
        nid_ctr);
    nid++;
    s <<
      btor2::next(
        to_string(nid),
        encoder->sid_bv,
        nid_ctr,
        to_string(nid - 1));
    nid++;
    s << eol;
    if (verbose)
      s << btor2::comment("bound (" + to_string(encoder->bound) + ")") << eol;
    s <<
      btor2::eq(
        to_string(nid),
        encoder->sid_bool,
        encoder->nids_const[encoder->bound],
        nid_ctr);
    nid++;
    s << btor2::bad(to_string(nid), to_string(nid - 1));

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

/* Btor2_Encoder::encode ******************************************************/
TEST_F(Btor2_Encoder_Test, encode_check)
{
  // concurrent increment using CHECK
  encode(
    {"increment.check.thread.0.asm", "increment.check.thread.n.asm"},
    "increment.check.t2.k16.btor2",
    16);
}

TEST_F(Btor2_Encoder_Test, encode_cas)
{
  // concurrent increment using CAS
  encode(
    {"increment.cas.asm", "increment.cas.asm"},
    "increment.cas.t2.k16.btor2",
    16);
}

TEST_F(Btor2_Encoder_Test, LOAD)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Load load {address};

  ASSERT_EQ(
    encoder->nids_load[encoder->thread][address],
    encoder->encode(load));
  ASSERT_EQ(expected_load(nid, address), encoder->str());
}

TEST_F(Btor2_Encoder_Test, LOAD_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Load load {address, true};

  ASSERT_EQ(
    encoder->nids_load_indirect[encoder->thread][address],
    encoder->encode(load));
  ASSERT_EQ(expected_load_indirect(nid, address), encoder->str());
}

TEST_F(Btor2_Encoder_Test, STORE)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  word_t address = 0;

  Store store {address};

  encoder->update = ::Encoder::Update::sb_adr;
  ASSERT_EQ(encoder->nids_const[address], encoder->encode(store));

  encoder->update = ::Encoder::Update::sb_val;
  ASSERT_EQ(encoder->nids_accu[0], encoder->encode(store));
}

TEST_F(Btor2_Encoder_Test, STORE_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Store store {address, true};

  encoder->update = ::Encoder::Update::sb_adr;
  ASSERT_EQ(
    encoder->nids_load[encoder->thread][address],
    encoder->encode(store));
  ASSERT_EQ(expected_load(nid, address), encoder->str());

  encoder->update = ::Encoder::Update::sb_val;
  ASSERT_EQ(encoder->nids_accu[0], encoder->encode(store));
}

TEST_F(Btor2_Encoder_Test, ADD)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Add add {address};

  string nid_add = encoder->encode(add);

  expected = [this, &nid, &address, &nid_add] {
    ostringstream s;

    s << expected_load(nid, address);
    s <<
      btor2::add(
        nid_add,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(Btor2_Encoder_Test, ADD_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Add add {address, true};

  string nid_add = encoder->encode(add);

  expected = [this, &nid, &address, &nid_add] {
    ostringstream s;

    s << expected_load_indirect(nid, address);
    s <<
      btor2::add(
        nid_add,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(Btor2_Encoder_Test, ADDI)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t value = 0;

  Addi addi {value};

  string nid_addi = encoder->encode(addi);

  expected = [this, &nid, &value, &nid_addi] {
    ostringstream s;

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

TEST_F(Btor2_Encoder_Test, SUB)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Sub sub {address};

  string nid_sub = encoder->encode(sub);

  expected = [this, &nid, &address, &nid_sub] {
    ostringstream s;

    s << expected_load(nid, address);
    s <<
      btor2::sub(
        nid_sub,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(Btor2_Encoder_Test, SUB_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Sub sub {address, true};

  string nid_sub = encoder->encode(sub);

  expected = [this, &nid, &address, &nid_sub] {
    ostringstream s;

    s << expected_load_indirect(nid, address);
    s <<
      btor2::sub(
        nid_sub,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(Btor2_Encoder_Test, SUBI)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t value = 0;

  Subi subi {value};

  string nid_subi = encoder->encode(subi);

  expected = [this, &nid, &value, &nid_subi] {
    ostringstream s;

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

TEST_F(Btor2_Encoder_Test, CMP)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Cmp cmp {address};

  string nid_cmp = encoder->encode(cmp);

  expected = [this, &nid, &address, &nid_cmp] {
    ostringstream s;

    s << expected_load(nid, address);
    s <<
      btor2::sub(
        nid_cmp,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(Btor2_Encoder_Test, CMP_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Cmp cmp {address, true};

  string nid_cmp = encoder->encode(cmp);

  expected = [this, &nid, &address, &nid_cmp] {
    ostringstream s;

    s << expected_load_indirect(nid, address);
    s <<
      btor2::sub(
        nid_cmp,
        encoder->sid_bv,
        encoder->nids_accu[encoder->thread],
        to_string(nid - 1));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(Btor2_Encoder_Test, JMP)
{
  Jmp jmp {0};

  ASSERT_EQ("", encoder->encode(jmp));
  ASSERT_EQ("", encoder->str());
}

TEST_F(Btor2_Encoder_Test, JZ)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  Jz jz {0};

  string nid_jz = encoder->encode(jz);

  expected = [this, &nid, &nid_jz] {
    ostringstream s;

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

TEST_F(Btor2_Encoder_Test, JNZ)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  Jnz jnz {0};

  string nid_jnz = encoder->encode(jnz);

  expected = [this, &nid, &nid_jnz] {
    ostringstream s;

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

TEST_F(Btor2_Encoder_Test, JS)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  Js js {0};

  string nid_js = encoder->encode(js);

  expected = [this, &nid, &nid_js] {
    ostringstream s;

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

TEST_F(Btor2_Encoder_Test, JNS)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  Jns jns {0};

  string nid_jns = encoder->encode(jns);

  expected = [this, &nid, &nid_jns] {
    ostringstream s;

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

TEST_F(Btor2_Encoder_Test, JNZNS)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  Jnzns jnzns {0};

  string nid_jnzns = encoder->encode(jnzns);

  expected = [this, &nid, &nid_jnzns] {
    ostringstream s;

    s <<
      btor2::ne(
        to_string(nid),
        encoder->sid_bool,
        encoder->nids_accu[encoder->thread],
        encoder->nids_const[0]);
    nid++;
    s <<
      btor2::slice(
        to_string(nid),
        encoder->sid_bool,
        encoder->nids_accu[encoder->thread],
        encoder->msb,
        encoder->msb);
    nid++;
    s <<
      btor2::land(
        nid_jnzns,
        encoder->sid_bool,
        to_string(nid - 2),
        btor2::lnot(to_string(nid - 1)));
    nid++;

    return s.str();
  };

  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(Btor2_Encoder_Test, MEM)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Mem mem {address};

  ASSERT_EQ(
    encoder->nids_load[encoder->thread][address],
    encoder->encode(mem));
  ASSERT_EQ(expected_load(nid, address), encoder->str());
}

TEST_F(Btor2_Encoder_Test, MEM_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Mem mem {address, true};

  ASSERT_EQ(
    encoder->nids_load_indirect[encoder->thread][address],
    encoder->encode(mem));
  ASSERT_EQ(expected_load_indirect(nid, address), encoder->str());
}

TEST_F(Btor2_Encoder_Test, CAS)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Cas cas {address};

  string nid_cas;

  expected = [this, &nid, &address, &nid_cas] {
    ostringstream s;

    if (encoder->update == ::Encoder::Update::accu)
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
    else if (encoder->update == ::Encoder::Update::heap)
      {
        s <<
          btor2::write(
            to_string(nid),
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
            to_string(nid - 1),
            encoder->nid_heap);
        nid++;
      }

    return s.str();
  };

  encoder->update = ::Encoder::Update::accu;
  nid_cas = encoder->encode(cas);
  ASSERT_EQ(expected(), encoder->str());

  encoder->formula.str("");

  encoder->update = ::Encoder::Update::heap;
  nid_cas = encoder->encode(cas);
  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(Btor2_Encoder_Test, CAS_indirect)
{
  add_dummy_programs(1);
  reset_encoder();
  init_state_definitions();

  btor2::nid_t nid = encoder->node;

  word_t address = 0;

  Cas cas {address, true};

  string nid_cas;

  expected = [this, &nid, &address, &nid_cas] {
    ostringstream s;

    if (encoder->update == ::Encoder::Update::accu)
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
    else if (encoder->update == ::Encoder::Update::heap)
      {
        s <<
          btor2::write(
            to_string(nid),
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
            to_string(nid - 1),
            encoder->nid_heap);
        nid++;
      }

    return s.str();
  };

  encoder->update = ::Encoder::Update::accu;
  nid_cas = encoder->encode(cas);
  ASSERT_EQ(expected(), encoder->str());

  encoder->formula.str("");

  encoder->update = ::Encoder::Update::heap;
  nid_cas = encoder->encode(cas);
  ASSERT_EQ(expected(), encoder->str());
}

TEST_F(Btor2_Encoder_Test, CHECK)
{
  Check check {1};

  ASSERT_EQ("", encoder->encode(check));
  ASSERT_EQ("", encoder->str());
}

TEST_F(Btor2_Encoder_Test, EXIT)
{
  Exit exit {1};

  ASSERT_EQ(encoder->nids_const[1], encoder->encode(exit));
  ASSERT_EQ("", encoder->str());
}
