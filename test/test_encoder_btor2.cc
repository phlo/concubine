#include "test_encoder.hh"

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
  string            nid;
  // Program_list_ptr  programs {make_shared<Program_list>()};
  // Btor2Encoder_ptr  encoder {create_encoder(1)};

  // Btor2Encoder_ptr create_encoder (const word_t bound)
    // {
      // return make_shared<Btor2_Encoder>(programs, bound, false);
    // }
//
  // void reset_encoder (const word_t bound)
    // {
      // encoder = create_encoder(bound);
    // }
//
  // void add_dummy_programs (unsigned num, unsigned size)
    // {
      // for (size_t i = 0; i < num; i++)
        // {
          // Instruction_ptr op = Instruction::Set::create("ADDI", i + 1);
          // programs->push_back(shared_ptr<Program>(new Program()));
          // for (size_t j = 0; j < size; j++)
            // (*programs)[i]->push_back(op);
        // }
//
      // encoder = create_encoder(1);
    // }
//
  // void add_instruction_set (unsigned num)
    // {
      // for (size_t i = 0; i < num; i++)
        // {
          // programs->push_back(shared_ptr<Program>(new Program()));
//
          // (*programs)[i]->push_back(Instruction::Set::create("LOAD", 1));  // 0
          // (*programs)[i]->push_back(Instruction::Set::create("STORE", 1)); // 1
          // (*programs)[i]->push_back(Instruction::Set::create("ADD", 1));   // 2
          // (*programs)[i]->push_back(Instruction::Set::create("ADDI", 1));  // 3
          // (*programs)[i]->push_back(Instruction::Set::create("SUB", 1));   // 4
          // (*programs)[i]->push_back(Instruction::Set::create("SUBI", 1));  // 5
          // (*programs)[i]->push_back(Instruction::Set::create("CMP", 1));   // 6
          // (*programs)[i]->push_back(Instruction::Set::create("JMP", 1));   // 7
          // (*programs)[i]->push_back(Instruction::Set::create("JZ", 1));    // 8
          // (*programs)[i]->push_back(Instruction::Set::create("JNZ", 1));   // 9
          // (*programs)[i]->push_back(Instruction::Set::create("JS", 1));    // 10
          // (*programs)[i]->push_back(Instruction::Set::create("JNS", 1));   // 11
          // (*programs)[i]->push_back(Instruction::Set::create("JNZNS", 1)); // 12
          // (*programs)[i]->push_back(Instruction::Set::create("MEM", 1));   // 13
          // (*programs)[i]->push_back(Instruction::Set::create("CAS", 1));   // 14
          // (*programs)[i]->push_back(Instruction::Set::create("CHECK", 1)); // 15
          // (*programs)[i]->push_back(Instruction::Set::create("EXIT", 1));  // 16
        // }
//
      // reset_encoder(1);
    // }

  void init_machine_state_declarations (bool clear_formula)
    {
      encoder->add_sorts();
      encoder->add_constants();

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_thread_scheduling (bool clear_formula)
    {
      init_machine_state_declarations(false);

      encoder->add_machine_state_declarations();

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_statement_execution (bool clear_formula)
    {
      init_thread_scheduling(false);

      encoder->add_thread_scheduling();

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_statement_activation (bool clear_formula)
    {
      init_statement_execution(false);

      encoder->add_statement_execution();

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_register_definitions (bool clear_formula)
    {
      init_statement_activation(false);

      encoder->add_statement_activation();

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_heap_definition (bool clear_formula)
    {
      init_register_definitions(false);

      encoder->add_register_definitions();

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_exit_definitions (bool clear_formula)
    {
      init_heap_definition(false);

      encoder->add_heap_definition();

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_checkpoint_constraints (bool clear_formula)
    {
      init_exit_definitions(false);

      encoder->add_exit_definitions();

      if (clear_formula)
        encoder->formula.str("");
    }
};

// void Btor2_Encoder::add_sorts ()
TEST_F(Btor2_Encoder_Test, add_sorts)
{
  encoder->add_sorts();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; sorts\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    + encoder->sid_bool + " sort bitvec 1\n"
    + encoder->sid_bv + " sort bitvec 16\n"
    + encoder->sid_heap + " sort array 2 2\n\n",
    encoder->str());

  /* verbosity */
  reset_encoder();

  verbose = false;
  encoder->add_sorts();
  verbose = true;

  ASSERT_EQ(
    encoder->sid_bool + " sort bitvec 1\n"
    + encoder->sid_bv + " sort bitvec 16\n"
    + encoder->sid_heap + " sort array 2 2\n\n",
    encoder->str());
}

// void Btor2_Encoder::add_constants ()
TEST_F(Btor2_Encoder_Test, add_constants)
{
  for (size_t thread = 0; thread < 3; thread++)
    {
      Program_ptr program = make_shared<Program>();

      programs.push_back(program);

      for (size_t pc = 0; pc < 3; pc++)
        program->push_back(Instruction::Set::create("ADDI", thread + pc + 1));
    }

  reset_encoder();

  encoder->add_sorts();

  encoder->formula.str("");

  encoder->add_constants();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; constants\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    + encoder->nid_false + " zero 1\n"
    + encoder->nid_true + " one 1\n"
    "\n"
    + encoder->nids_const[0] + " zero 2\n"
    + encoder->nids_const[1] + " one 2\n"
    + encoder->nids_const[2] + " constd 2 2\n"
    + encoder->nids_const[3] + " constd 2 3\n"
    + encoder->nids_const[4] + " constd 2 4\n"
    + encoder->nids_const[5] + " constd 2 5\n"
    "\n",
    encoder->str());

  /* verbosity */
  reset_encoder();

  encoder->add_sorts();

  encoder->formula.str("");

  verbose = false;
  encoder->add_constants();
  verbose = true;

  ASSERT_EQ(
    encoder->nid_false + " zero 1\n"
    + encoder->nid_true + " one 1\n"
    "\n"
    + encoder->nids_const[0] + " zero 2\n"
    + encoder->nids_const[1] + " one 2\n"
    + encoder->nids_const[2] + " constd 2 2\n"
    + encoder->nids_const[3] + " constd 2 3\n"
    + encoder->nids_const[4] + " constd 2 4\n"
    + encoder->nids_const[5] + " constd 2 5\n"
    "\n",
    encoder->str());
}

// void Btor2_Encoder::add_machine_state_declarations ()
TEST_F(Btor2_Encoder_Test, add_machine_state_declarations)
{
  add_dummy_programs(2, 3);
  reset_encoder();

  init_machine_state_declarations(true);

  encoder->add_machine_state_declarations();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; machine state declarations\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; heap\n"
    + encoder->nid_heap + " state " + encoder->sid_heap + " heap\n"
    "\n"
    "; accumulator registers - accu_<thread>\n"
    + encoder->nids_accu[0] + " state 2 accu_0\n"
    + encoder->nids_accu[1] + " state 2 accu_1\n"
    "\n"
    "; CAS memory registers - mem_<thread>\n"
    + encoder->nids_mem[0] + " state 2 mem_0\n"
    + encoder->nids_mem[1] + " state 2 mem_1\n"
    "\n"
    "; statement activation flags - stmt_<thread>_<pc>\n"
    + encoder->nids_stmt[0][0] + " state 1 stmt_0_0\n"
    + encoder->nids_stmt[0][1] + " state 1 stmt_0_1\n"
    + encoder->nids_stmt[0][2] + " state 1 stmt_0_2\n"
    "\n"
    + encoder->nids_stmt[1][0] + " state 1 stmt_1_0\n"
    + encoder->nids_stmt[1][1] + " state 1 stmt_1_1\n"
    + encoder->nids_stmt[1][2] + " state 1 stmt_1_2\n"
    "\n"
    "; exit flag\n"
    + encoder->nid_exit_flag + " state 1 exit\n"
    "\n",
    encoder->str());

  /* verbosity */
  reset_encoder();

  init_machine_state_declarations(true);

  verbose = false;
  encoder->add_machine_state_declarations();
  verbose = true;

  ASSERT_EQ(
    encoder->nid_heap + " state " + encoder->sid_heap + " heap\n"
    "\n"
    + encoder->nids_accu[0] + " state 2 accu_0\n"
    + encoder->nids_accu[1] + " state 2 accu_1\n"
    "\n"
    + encoder->nids_mem[0] + " state 2 mem_0\n"
    + encoder->nids_mem[1] + " state 2 mem_1\n"
    "\n"
    + encoder->nids_stmt[0][0] + " state 1 stmt_0_0\n"
    + encoder->nids_stmt[0][1] + " state 1 stmt_0_1\n"
    + encoder->nids_stmt[0][2] + " state 1 stmt_0_2\n"
    "\n"
    + encoder->nids_stmt[1][0] + " state 1 stmt_1_0\n"
    + encoder->nids_stmt[1][1] + " state 1 stmt_1_1\n"
    + encoder->nids_stmt[1][2] + " state 1 stmt_1_2\n"
    "\n"
    + encoder->nid_exit_flag + " state 1 exit\n"
    "\n",
    encoder->str());
}

// void Btor2_Encoder::add_thread_scheduling ()
TEST_F(Btor2_Encoder_Test, add_thread_scheduling)
{
  add_dummy_programs(3, 3);
  reset_encoder();

  init_thread_scheduling(true);

  encoder->add_thread_scheduling();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; thread scheduling\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    + encoder->nids_thread[0] + " input 1 thread_0\n"
    + encoder->nids_thread[1] + " input 1 thread_1\n"
    + encoder->nids_thread[2] + " input 1 thread_2\n"
    "\n"
    "; cardinality constraint\n"
    "30 or 1 " + encoder->nids_thread[0] + " " + encoder->nids_thread[1] + "\n"
    "31 or 1 " + encoder->nids_thread[2] + " 30\n"
    "32 or 1 " + encoder->nid_exit_flag + " 31\n"
    "33 constraint 32\n"
    "34 nand 1 " + encoder->nids_thread[0] + " " + encoder->nids_thread[1] + "\n"
    "35 nand 1 " + encoder->nids_thread[0] + " " + encoder->nids_thread[2] + "\n"
    "36 nand 1 " + encoder->nids_thread[0] + " " + encoder->nid_exit_flag + "\n"
    "37 nand 1 " + encoder->nids_thread[1] + " " + encoder->nids_thread[2] + "\n"
    "38 nand 1 " + encoder->nids_thread[1] + " " + encoder->nid_exit_flag + "\n"
    "39 nand 1 " + encoder->nids_thread[2] + " " + encoder->nid_exit_flag + "\n"
    "40 and 1 34 35\n"
    "41 and 1 36 40\n"
    "42 and 1 37 41\n"
    "43 and 1 38 42\n"
    "44 and 1 39 43\n"
    "45 constraint 44\n\n",
    encoder->str());

  /* verbosity */
  reset_encoder();

  init_thread_scheduling(true);

  verbose = false;
  encoder->add_thread_scheduling();
  verbose = true;

  ASSERT_EQ(
    encoder->nids_thread[0] + " input 1 thread_0\n"
    + encoder->nids_thread[1] + " input 1 thread_1\n"
    + encoder->nids_thread[2] + " input 1 thread_2\n"
    "\n"
    "30 or 1 " + encoder->nids_thread[0] + " " + encoder->nids_thread[1] + "\n"
    "31 or 1 " + encoder->nids_thread[2] + " 30\n"
    "32 or 1 " + encoder->nid_exit_flag + " 31\n"
    "33 constraint 32\n"
    "34 nand 1 " + encoder->nids_thread[0] + " " + encoder->nids_thread[1] + "\n"
    "35 nand 1 " + encoder->nids_thread[0] + " " + encoder->nids_thread[2] + "\n"
    "36 nand 1 " + encoder->nids_thread[0] + " " + encoder->nid_exit_flag + "\n"
    "37 nand 1 " + encoder->nids_thread[1] + " " + encoder->nids_thread[2] + "\n"
    "38 nand 1 " + encoder->nids_thread[1] + " " + encoder->nid_exit_flag + "\n"
    "39 nand 1 " + encoder->nids_thread[2] + " " + encoder->nid_exit_flag + "\n"
    "40 and 1 34 35\n"
    "41 and 1 36 40\n"
    "42 and 1 37 41\n"
    "43 and 1 38 42\n"
    "44 and 1 39 43\n"
    "45 constraint 44\n\n",
    encoder->str());
}

// void Btor2_Encoder::add_statement_execution ()
TEST_F(Btor2_Encoder_Test, add_statement_execution)
{
  add_dummy_programs(3, 3);
  reset_encoder();

  init_statement_execution(true);

  encoder->add_statement_execution();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; statement execution - exec_<thread>_<pc>\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "46 and 1 " + encoder->nids_stmt[0][0] + " " + encoder->nids_thread[0] + " exec_0_0\n"
    "47 and 1 " + encoder->nids_stmt[0][1] + " " + encoder->nids_thread[0] + " exec_0_1\n"
    "48 and 1 " + encoder->nids_stmt[0][2] + " " + encoder->nids_thread[0] + " exec_0_2\n"
    "\n"
    "49 and 1 " + encoder->nids_stmt[1][0] + " " + encoder->nids_thread[1] + " exec_1_0\n"
    "50 and 1 " + encoder->nids_stmt[1][1] + " " + encoder->nids_thread[1] + " exec_1_1\n"
    "51 and 1 " + encoder->nids_stmt[1][2] + " " + encoder->nids_thread[1] + " exec_1_2\n"
    "\n"
    "52 and 1 " + encoder->nids_stmt[2][0] + " " + encoder->nids_thread[2] + " exec_2_0\n"
    "53 and 1 " + encoder->nids_stmt[2][1] + " " + encoder->nids_thread[2] + " exec_2_1\n"
    "54 and 1 " + encoder->nids_stmt[2][2] + " " + encoder->nids_thread[2] + " exec_2_2\n"
    "\n",
    encoder->str());

  /* verbosity */
  reset_encoder();

  init_statement_execution(true);

  verbose = false;
  encoder->add_statement_execution();
  verbose = true;

  ASSERT_EQ(
    "46 and 1 " + encoder->nids_stmt[0][0] + " " + encoder->nids_thread[0] + " exec_0_0\n"
    "47 and 1 " + encoder->nids_stmt[0][1] + " " + encoder->nids_thread[0] + " exec_0_1\n"
    "48 and 1 " + encoder->nids_stmt[0][2] + " " + encoder->nids_thread[0] + " exec_0_2\n"
    "\n"
    "49 and 1 " + encoder->nids_stmt[1][0] + " " + encoder->nids_thread[1] + " exec_1_0\n"
    "50 and 1 " + encoder->nids_stmt[1][1] + " " + encoder->nids_thread[1] + " exec_1_1\n"
    "51 and 1 " + encoder->nids_stmt[1][2] + " " + encoder->nids_thread[1] + " exec_1_2\n"
    "\n"
    "52 and 1 " + encoder->nids_stmt[2][0] + " " + encoder->nids_thread[2] + " exec_2_0\n"
    "53 and 1 " + encoder->nids_stmt[2][1] + " " + encoder->nids_thread[2] + " exec_2_1\n"
    "54 and 1 " + encoder->nids_stmt[2][2] + " " + encoder->nids_thread[2] + " exec_2_2\n"
    "\n",
    encoder->str());
}

// void Btor2_Encoder::add_statement_activation ()
TEST_F(Btor2_Encoder_Test, add_statement_activation)
{
  add_dummy_programs(3, 2);
  reset_encoder();

  init_statement_activation(true);

  encoder->add_statement_activation();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; statement activation state definitions\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_0_0\n"
    "49 init 1 " + encoder->nids_stmt[0][0] + " " + encoder->nid_true + "\n"
    "50 and 1 " + encoder->nids_stmt[0][0] + " -" + encoder->nids_exec[0][0] + "\n"
    "51 next 1 " + encoder->nids_stmt[0][0] + " 50 0:0:ADDI:1\n"
    "\n"
    "; stmt_0_1\n"
    "52 init 1 " + encoder->nids_stmt[0][1] + " " + encoder->nid_false + "\n"
    "53 and 1 " + encoder->nids_stmt[0][1] + " -" + encoder->nids_exec[0][1] + "\n"
    "54 ite 1 " + encoder->nids_stmt[0][0] + " " + encoder->nids_exec[0][0] + " 53 0:0:ADDI:1\n"
    "55 next 1 " + encoder->nids_stmt[0][1] + " 54 0:1:ADDI:1\n"
    "\n"
    "; stmt_1_0\n"
    "56 init 1 " + encoder->nids_stmt[1][0] + " " + encoder->nid_true + "\n"
    "57 and 1 " + encoder->nids_stmt[1][0] + " -" + encoder->nids_exec[1][0] + "\n"
    "58 next 1 " + encoder->nids_stmt[1][0] + " 57 1:0:ADDI:2\n"
    "\n"
    "; stmt_1_1\n"
    "59 init 1 " + encoder->nids_stmt[1][1] + " " + encoder->nid_false + "\n"
    "60 and 1 " + encoder->nids_stmt[1][1] + " -" + encoder->nids_exec[1][1] + "\n"
    "61 ite 1 " + encoder->nids_stmt[1][0] + " " + encoder->nids_exec[1][0] + " 60 1:0:ADDI:2\n"
    "62 next 1 " + encoder->nids_stmt[1][1] + " 61 1:1:ADDI:2\n"
    "\n"
    "; stmt_2_0\n"
    "63 init 1 " + encoder->nids_stmt[2][0] + " " + encoder->nid_true + "\n"
    "64 and 1 " + encoder->nids_stmt[2][0] + " -" + encoder->nids_exec[2][0] + "\n"
    "65 next 1 " + encoder->nids_stmt[2][0] + " 64 2:0:ADDI:3\n"
    "\n"
    "; stmt_2_1\n"
    "66 init 1 " + encoder->nids_stmt[2][1] + " " + encoder->nid_false + "\n"
    "67 and 1 " + encoder->nids_stmt[2][1] + " -" + encoder->nids_exec[2][1] + "\n"
    "68 ite 1 " + encoder->nids_stmt[2][0] + " " + encoder->nids_exec[2][0] + " 67 2:0:ADDI:3\n"
    "69 next 1 " + encoder->nids_stmt[2][1] + " 68 2:1:ADDI:3\n"
    "\n",
    encoder->str());

  /* verbosity */
  reset_encoder(1);

  init_statement_activation(true);

  verbose = false;
  encoder->add_statement_activation();
  verbose = true;

  ASSERT_EQ(
    "49 init 1 " + encoder->nids_stmt[0][0] + " " + encoder->nid_true + "\n"
    "50 and 1 " + encoder->nids_stmt[0][0] + " -" + encoder->nids_exec[0][0] + "\n"
    "51 next 1 " + encoder->nids_stmt[0][0] + " 50\n"
    "\n"
    "52 init 1 " + encoder->nids_stmt[0][1] + " " + encoder->nid_false + "\n"
    "53 and 1 " + encoder->nids_stmt[0][1] + " -" + encoder->nids_exec[0][1] + "\n"
    "54 ite 1 " + encoder->nids_stmt[0][0] + " " + encoder->nids_exec[0][0] + " 53\n"
    "55 next 1 " + encoder->nids_stmt[0][1] + " 54\n"
    "\n"
    "56 init 1 " + encoder->nids_stmt[1][0] + " " + encoder->nid_true + "\n"
    "57 and 1 " + encoder->nids_stmt[1][0] + " -" + encoder->nids_exec[1][0] + "\n"
    "58 next 1 " + encoder->nids_stmt[1][0] + " 57\n"
    "\n"
    "59 init 1 " + encoder->nids_stmt[1][1] + " " + encoder->nid_false + "\n"
    "60 and 1 " + encoder->nids_stmt[1][1] + " -" + encoder->nids_exec[1][1] + "\n"
    "61 ite 1 " + encoder->nids_stmt[1][0] + " " + encoder->nids_exec[1][0] + " 60\n"
    "62 next 1 " + encoder->nids_stmt[1][1] + " 61\n"
    "\n"
    "63 init 1 " + encoder->nids_stmt[2][0] + " " + encoder->nid_true + "\n"
    "64 and 1 " + encoder->nids_stmt[2][0] + " -" + encoder->nids_exec[2][0] + "\n"
    "65 next 1 " + encoder->nids_stmt[2][0] + " 64\n"
    "\n"
    "66 init 1 " + encoder->nids_stmt[2][1] + " " + encoder->nid_false + "\n"
    "67 and 1 " + encoder->nids_stmt[2][1] + " -" + encoder->nids_exec[2][1] + "\n"
    "68 ite 1 " + encoder->nids_stmt[2][0] + " " + encoder->nids_exec[2][0] + " 67\n"
    "69 next 1 " + encoder->nids_stmt[2][1] + " 68\n"
    "\n",
    encoder->str());
}

TEST_F(Btor2_Encoder_Test, add_statement_activation_jmp)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(
      create_program(
        "ADDI 1\n"
        "STORE 1\n"
        "JMP 1\n"
        "EXIT 1\n"));

  reset_encoder();

  init_statement_activation(true);

  encoder->add_statement_activation();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; statement activation state definitions\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_0_0\n"
    "59 init 1 " + encoder->nids_stmt[0][0] + " " + encoder->nid_true + "\n"
    "60 and 1 " + encoder->nids_stmt[0][0] + " -" + encoder->nids_exec[0][0] + "\n"
    "61 next 1 " + encoder->nids_stmt[0][0] + " 60 0:0:ADDI:1\n"
    "\n"
    "; stmt_0_1\n"
    "62 init 1 " + encoder->nids_stmt[0][1] + " " + encoder->nid_false + "\n"
    "63 and 1 " + encoder->nids_stmt[0][1] + " -" + encoder->nids_exec[0][1] + "\n"
    "64 ite 1 " + encoder->nids_stmt[0][0] + " " + encoder->nids_exec[0][0] + " 63 0:0:ADDI:1\n"
    "65 ite 1 " + encoder->nids_stmt[0][2] + " " + encoder->nids_exec[0][2] + " 64 0:2:JMP:1\n"
    "66 next 1 " + encoder->nids_stmt[0][1] + " 65 0:1:STORE:1\n"
    "\n"
    "; stmt_0_2\n"
    "67 init 1 " + encoder->nids_stmt[0][2] + " " + encoder->nid_false + "\n"
    "68 and 1 " + encoder->nids_stmt[0][2] + " -" + encoder->nids_exec[0][2] + "\n"
    "69 ite 1 " + encoder->nids_stmt[0][1] + " " + encoder->nids_exec[0][1] + " 68 0:1:STORE:1\n"
    "70 next 1 " + encoder->nids_stmt[0][2] + " 69 0:2:JMP:1\n"
    "\n"
    "; stmt_0_3\n" // unreachable
    "71 init 1 " + encoder->nids_stmt[0][3] + " " + encoder->nid_false + "\n"
    "72 and 1 " + encoder->nids_stmt[0][3] + " -" + encoder->nids_exec[0][3] + "\n"
    "73 next 1 " + encoder->nids_stmt[0][3] + " 72 0:3:EXIT:1\n"
    "\n"
    "; stmt_1_0\n"
    "74 init 1 " + encoder->nids_stmt[1][0] + " " + encoder->nid_true + "\n"
    "75 and 1 " + encoder->nids_stmt[1][0] + " -" + encoder->nids_exec[1][0] + "\n"
    "76 next 1 " + encoder->nids_stmt[1][0] + " 75 1:0:ADDI:1\n"
    "\n"
    "; stmt_1_1\n"
    "77 init 1 " + encoder->nids_stmt[1][1] + " " + encoder->nid_false + "\n"
    "78 and 1 " + encoder->nids_stmt[1][1] + " -" + encoder->nids_exec[1][1] + "\n"
    "79 ite 1 " + encoder->nids_stmt[1][0] + " " + encoder->nids_exec[1][0] + " 78 1:0:ADDI:1\n"
    "80 ite 1 " + encoder->nids_stmt[1][2] + " " + encoder->nids_exec[1][2] + " 79 1:2:JMP:1\n"
    "81 next 1 " + encoder->nids_stmt[1][1] + " 80 1:1:STORE:1\n"
    "\n"
    "; stmt_1_2\n"
    "82 init 1 " + encoder->nids_stmt[1][2] + " " + encoder->nid_false + "\n"
    "83 and 1 " + encoder->nids_stmt[1][2] + " -" + encoder->nids_exec[1][2] + "\n"
    "84 ite 1 " + encoder->nids_stmt[1][1] + " " + encoder->nids_exec[1][1] + " 83 1:1:STORE:1\n"
    "85 next 1 " + encoder->nids_stmt[1][2] + " 84 1:2:JMP:1\n"
    "\n"
    "; stmt_1_3\n" // unreachable
    "86 init 1 " + encoder->nids_stmt[1][3] + " " + encoder->nid_false + "\n"
    "87 and 1 " + encoder->nids_stmt[1][3] + " -" + encoder->nids_exec[1][3] + "\n"
    "88 next 1 " + encoder->nids_stmt[1][3] + " 87 1:3:EXIT:1\n"
    "\n"
    "; stmt_2_0\n"
    "89 init 1 " + encoder->nids_stmt[2][0] + " " + encoder->nid_true + "\n"
    "90 and 1 " + encoder->nids_stmt[2][0] + " -" + encoder->nids_exec[2][0] + "\n"
    "91 next 1 " + encoder->nids_stmt[2][0] + " 90 2:0:ADDI:1\n"
    "\n"
    "; stmt_2_1\n"
    "92 init 1 " + encoder->nids_stmt[2][1] + " " + encoder->nid_false + "\n"
    "93 and 1 " + encoder->nids_stmt[2][1] + " -" + encoder->nids_exec[2][1] + "\n"
    "94 ite 1 " + encoder->nids_stmt[2][0] + " " + encoder->nids_exec[2][0] + " 93 2:0:ADDI:1\n"
    "95 ite 1 " + encoder->nids_stmt[2][2] + " " + encoder->nids_exec[2][2] + " 94 2:2:JMP:1\n"
    "96 next 1 " + encoder->nids_stmt[2][1] + " 95 2:1:STORE:1\n"
    "\n"
    "; stmt_2_2\n"
    "97 init 1 " + encoder->nids_stmt[2][2] + " " + encoder->nid_false + "\n"
    "98 and 1 " + encoder->nids_stmt[2][2] + " -" + encoder->nids_exec[2][2] + "\n"
    "99 ite 1 " + encoder->nids_stmt[2][1] + " " + encoder->nids_exec[2][1] + " 98 2:1:STORE:1\n"
    "100 next 1 " + encoder->nids_stmt[2][2] + " 99 2:2:JMP:1\n"
    "\n"
    "; stmt_2_3\n" // unreachable
    "101 init 1 " + encoder->nids_stmt[2][3] + " " + encoder->nid_false + "\n"
    "102 and 1 " + encoder->nids_stmt[2][3] + " -" + encoder->nids_exec[2][3] + "\n"
    "103 next 1 " + encoder->nids_stmt[2][3] + " 102 2:3:EXIT:1\n"
    "\n",
    encoder->str());
}

TEST_F(Btor2_Encoder_Test, add_statement_activation_jmp_conditional)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(
      create_program(
        "ADDI 1\n"
        "STORE 1\n"
        "JNZ 1\n"
        "EXIT 1\n"));

  reset_encoder(3);

  init_statement_activation(true);

  encoder->add_statement_activation();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; statement activation state definitions\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_0_0\n"
    "60 init 1 " + encoder->nids_stmt[0][0] + " " + encoder->nid_true + "\n"
    "61 and 1 " + encoder->nids_stmt[0][0] + " -" + encoder->nids_exec[0][0] + "\n"
    "62 next 1 " + encoder->nids_stmt[0][0] + " 61 0:0:ADDI:1\n"
    "\n"
    "; stmt_0_1\n"
    "63 init 1 " + encoder->nids_stmt[0][1] + " " + encoder->nid_false + "\n"
    "64 and 1 " + encoder->nids_stmt[0][1] + " -" + encoder->nids_exec[0][1] + "\n"
    "65 ite 1 " + encoder->nids_stmt[0][0] + " " + encoder->nids_exec[0][0] + " 64 0:0:ADDI:1\n"
    "66 ne 1 " + encoder->nids_accu[0] + " " + encoder->nids_const[0] + "\n"
    "67 and 1 " + encoder->nids_exec[0][2] + " 66\n"
    "68 ite 1 " + encoder->nids_stmt[0][2] + " 67 65 0:2:JNZ:1\n"
    "69 next 1 " + encoder->nids_stmt[0][1] + " 68 0:1:STORE:1\n"
    "\n"
    "; stmt_0_2\n"
    "70 init 1 " + encoder->nids_stmt[0][2] + " " + encoder->nid_false + "\n"
    "71 and 1 " + encoder->nids_stmt[0][2] + " -" + encoder->nids_exec[0][2] + "\n"
    "72 ite 1 " + encoder->nids_stmt[0][1] + " " + encoder->nids_exec[0][1] + " 71 0:1:STORE:1\n"
    "73 next 1 " + encoder->nids_stmt[0][2] + " 72 0:2:JNZ:1\n"
    "\n"
    "; stmt_0_3\n"
    "74 init 1 " + encoder->nids_stmt[0][3] + " " + encoder->nid_false + "\n"
    "75 and 1 " + encoder->nids_stmt[0][3] + " -" + encoder->nids_exec[0][3] + "\n"
    "76 and 1 " + encoder->nids_exec[0][2] + " -66\n"
    "77 ite 1 " + encoder->nids_stmt[0][2] + " 76 75 0:2:JNZ:1\n"
    "78 next 1 " + encoder->nids_stmt[0][3] + " 77 0:3:EXIT:1\n"
    "\n"
    "; stmt_1_0\n"
    "79 init 1 " + encoder->nids_stmt[1][0] + " " + encoder->nid_true + "\n"
    "80 and 1 " + encoder->nids_stmt[1][0] + " -" + encoder->nids_exec[1][0] + "\n"
    "81 next 1 " + encoder->nids_stmt[1][0] + " 80 1:0:ADDI:1\n"
    "\n"
    "; stmt_1_1\n"
    "82 init 1 " + encoder->nids_stmt[1][1] + " " + encoder->nid_false + "\n"
    "83 and 1 " + encoder->nids_stmt[1][1] + " -" + encoder->nids_exec[1][1] + "\n"
    "84 ite 1 " + encoder->nids_stmt[1][0] + " " + encoder->nids_exec[1][0] + " 83 1:0:ADDI:1\n"
    "85 ne 1 " + encoder->nids_accu[1] + " " + encoder->nids_const[0] + "\n"
    "86 and 1 " + encoder->nids_exec[1][2] + " 85\n"
    "87 ite 1 " + encoder->nids_stmt[1][2] + " 86 84 1:2:JNZ:1\n"
    "88 next 1 " + encoder->nids_stmt[1][1] + " 87 1:1:STORE:1\n"
    "\n"
    "; stmt_1_2\n"
    "89 init 1 " + encoder->nids_stmt[1][2] + " " + encoder->nid_false + "\n"
    "90 and 1 " + encoder->nids_stmt[1][2] + " -" + encoder->nids_exec[1][2] + "\n"
    "91 ite 1 " + encoder->nids_stmt[1][1] + " " + encoder->nids_exec[1][1] + " 90 1:1:STORE:1\n"
    "92 next 1 " + encoder->nids_stmt[1][2] + " 91 1:2:JNZ:1\n"
    "\n"
    "; stmt_1_3\n"
    "93 init 1 " + encoder->nids_stmt[1][3] + " " + encoder->nid_false + "\n"
    "94 and 1 " + encoder->nids_stmt[1][3] + " -" + encoder->nids_exec[1][3] + "\n"
    "95 and 1 " + encoder->nids_exec[1][2] + " -85\n"
    "96 ite 1 " + encoder->nids_stmt[1][2] + " 95 94 1:2:JNZ:1\n"
    "97 next 1 " + encoder->nids_stmt[1][3] + " 96 1:3:EXIT:1\n"
    "\n"
    "; stmt_2_0\n"
    "98 init 1 " + encoder->nids_stmt[2][0] + " " + encoder->nid_true + "\n"
    "99 and 1 " + encoder->nids_stmt[2][0] + " -" + encoder->nids_exec[2][0] + "\n"
    "100 next 1 " + encoder->nids_stmt[2][0] + " 99 2:0:ADDI:1\n"
    "\n"
    "; stmt_2_1\n"
    "101 init 1 " + encoder->nids_stmt[2][1] + " " + encoder->nid_false + "\n"
    "102 and 1 " + encoder->nids_stmt[2][1] + " -" + encoder->nids_exec[2][1] + "\n"
    "103 ite 1 " + encoder->nids_stmt[2][0] + " " + encoder->nids_exec[2][0] + " 102 2:0:ADDI:1\n"
    "104 ne 1 " + encoder->nids_accu[2] + " " + encoder->nids_const[0] + "\n"
    "105 and 1 " + encoder->nids_exec[2][2] + " 104\n"
    "106 ite 1 " + encoder->nids_stmt[2][2] + " 105 103 2:2:JNZ:1\n"
    "107 next 1 " + encoder->nids_stmt[2][1] + " 106 2:1:STORE:1\n"
    "\n"
    "; stmt_2_2\n"
    "108 init 1 " + encoder->nids_stmt[2][2] + " " + encoder->nid_false + "\n"
    "109 and 1 " + encoder->nids_stmt[2][2] + " -" + encoder->nids_exec[2][2] + "\n"
    "110 ite 1 " + encoder->nids_stmt[2][1] + " " + encoder->nids_exec[2][1] + " 109 2:1:STORE:1\n"
    "111 next 1 " + encoder->nids_stmt[2][2] + " 110 2:2:JNZ:1\n"
    "\n"
    "; stmt_2_3\n"
    "112 init 1 " + encoder->nids_stmt[2][3] + " " + encoder->nid_false + "\n"
    "113 and 1 " + encoder->nids_stmt[2][3] + " -" + encoder->nids_exec[2][3] + "\n"
    "114 and 1 " + encoder->nids_exec[2][2] + " -104\n"
    "115 ite 1 " + encoder->nids_stmt[2][2] + " 114 113 2:2:JNZ:1\n"
    "116 next 1 " + encoder->nids_stmt[2][3] + " 115 2:3:EXIT:1\n"
    "\n",
    encoder->str());

  /* TODO remove
  reset_encoder(4);

  encoder->declare_sorts();
  encoder->declare_constants();
  encoder->add_bound();
  encoder->declare_states();
  encoder->add_thread_scheduling();
  encoder->add_checkpoint_constraints();
  encoder->add_statement_execution();
  encoder->add_statement_activation();

  string formula = encoder->str() + eol;

  formula +=
    btor2::next(
      encoder->nid(),
      encoder->sid_bv,
      encoder->nids_accu[1],
      encoder->nids_const[1]);

  formula += btor2::constraint(encoder->nid(), encoder->nids_thread[1]);

  cout << formula;

  evaluate(formula);
  */
}

TEST_F(Btor2_Encoder_Test, add_statement_activation_jmp_start)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(
      create_program(
        "ADDI 1\n"
        "STORE 1\n"
        "JNZ 0\n"
        "EXIT 1\n"));

  reset_encoder(3);

  init_statement_activation(true);

  encoder->add_statement_activation();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; statement activation state definitions\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_0_0\n"
    "60 init 1 " + encoder->nids_stmt[0][0] + " " + encoder->nid_true + "\n"
    "61 and 1 " + encoder->nids_stmt[0][0] + " -" + encoder->nids_exec[0][0] + "\n"
    "62 ne 1 " + encoder->nids_accu[0] + " " + encoder->nids_const[0] + "\n"
    "63 and 1 " + encoder->nids_exec[0][2] + " 62\n"
    "64 ite 1 " + encoder->nids_stmt[0][2] + " 63 61 0:2:JNZ:0\n"
    "65 next 1 " + encoder->nids_stmt[0][0] + " 64 0:0:ADDI:1\n"
    "\n"
    "; stmt_0_1\n"
    "66 init 1 " + encoder->nids_stmt[0][1] + " " + encoder->nid_false + "\n"
    "67 and 1 " + encoder->nids_stmt[0][1] + " -" + encoder->nids_exec[0][1] + "\n"
    "68 ite 1 " + encoder->nids_stmt[0][0] + " " + encoder->nids_exec[0][0] + " 67 0:0:ADDI:1\n"
    "69 next 1 " + encoder->nids_stmt[0][1] + " 68 0:1:STORE:1\n"
    "\n"
    "; stmt_0_2\n"
    "70 init 1 " + encoder->nids_stmt[0][2] + " " + encoder->nid_false + "\n"
    "71 and 1 " + encoder->nids_stmt[0][2] + " -" + encoder->nids_exec[0][2] + "\n"
    "72 ite 1 " + encoder->nids_stmt[0][1] + " " + encoder->nids_exec[0][1] + " 71 0:1:STORE:1\n"
    "73 next 1 " + encoder->nids_stmt[0][2] + " 72 0:2:JNZ:0\n"
    "\n"
    "; stmt_0_3\n"
    "74 init 1 " + encoder->nids_stmt[0][3] + " " + encoder->nid_false + "\n"
    "75 and 1 " + encoder->nids_stmt[0][3] + " -" + encoder->nids_exec[0][3] + "\n"
    "76 and 1 " + encoder->nids_exec[0][2] + " -62\n"
    "77 ite 1 " + encoder->nids_stmt[0][2] + " 76 75 0:2:JNZ:0\n"
    "78 next 1 " + encoder->nids_stmt[0][3] + " 77 0:3:EXIT:1\n"
    "\n"
    "; stmt_1_0\n"
    "79 init 1 " + encoder->nids_stmt[1][0] + " " + encoder->nid_true + "\n"
    "80 and 1 " + encoder->nids_stmt[1][0] + " -" + encoder->nids_exec[1][0] + "\n"
    "81 ne 1 " + encoder->nids_accu[1] + " " + encoder->nids_const[0] + "\n"
    "82 and 1 " + encoder->nids_exec[1][2] + " 81\n"
    "83 ite 1 " + encoder->nids_stmt[1][2] + " 82 80 1:2:JNZ:0\n"
    "84 next 1 " + encoder->nids_stmt[1][0] + " 83 1:0:ADDI:1\n"
    "\n"
    "; stmt_1_1\n"
    "85 init 1 " + encoder->nids_stmt[1][1] + " " + encoder->nid_false + "\n"
    "86 and 1 " + encoder->nids_stmt[1][1] + " -" + encoder->nids_exec[1][1] + "\n"
    "87 ite 1 " + encoder->nids_stmt[1][0] + " " + encoder->nids_exec[1][0] + " 86 1:0:ADDI:1\n"
    "88 next 1 " + encoder->nids_stmt[1][1] + " 87 1:1:STORE:1\n"
    "\n"
    "; stmt_1_2\n"
    "89 init 1 " + encoder->nids_stmt[1][2] + " " + encoder->nid_false + "\n"
    "90 and 1 " + encoder->nids_stmt[1][2] + " -" + encoder->nids_exec[1][2] + "\n"
    "91 ite 1 " + encoder->nids_stmt[1][1] + " " + encoder->nids_exec[1][1] + " 90 1:1:STORE:1\n"
    "92 next 1 " + encoder->nids_stmt[1][2] + " 91 1:2:JNZ:0\n"
    "\n"
    "; stmt_1_3\n"
    "93 init 1 " + encoder->nids_stmt[1][3] + " " + encoder->nid_false + "\n"
    "94 and 1 " + encoder->nids_stmt[1][3] + " -" + encoder->nids_exec[1][3] + "\n"
    "95 and 1 " + encoder->nids_exec[1][2] + " -81\n"
    "96 ite 1 " + encoder->nids_stmt[1][2] + " 95 94 1:2:JNZ:0\n"
    "97 next 1 " + encoder->nids_stmt[1][3] + " 96 1:3:EXIT:1\n"
    "\n"
    "; stmt_2_0\n"
    "98 init 1 " + encoder->nids_stmt[2][0] + " " + encoder->nid_true + "\n"
    "99 and 1 " + encoder->nids_stmt[2][0] + " -" + encoder->nids_exec[2][0] + "\n"
    "100 ne 1 " + encoder->nids_accu[2] + " " + encoder->nids_const[0] + "\n"
    "101 and 1 " + encoder->nids_exec[2][2] + " 100\n"
    "102 ite 1 " + encoder->nids_stmt[2][2] + " 101 99 2:2:JNZ:0\n"
    "103 next 1 " + encoder->nids_stmt[2][0] + " 102 2:0:ADDI:1\n"
    "\n"
    "; stmt_2_1\n"
    "104 init 1 " + encoder->nids_stmt[2][1] + " " + encoder->nid_false + "\n"
    "105 and 1 " + encoder->nids_stmt[2][1] + " -" + encoder->nids_exec[2][1] + "\n"
    "106 ite 1 " + encoder->nids_stmt[2][0] + " " + encoder->nids_exec[2][0] + " 105 2:0:ADDI:1\n"
    "107 next 1 " + encoder->nids_stmt[2][1] + " 106 2:1:STORE:1\n"
    "\n"
    "; stmt_2_2\n"
    "108 init 1 " + encoder->nids_stmt[2][2] + " " + encoder->nid_false + "\n"
    "109 and 1 " + encoder->nids_stmt[2][2] + " -" + encoder->nids_exec[2][2] + "\n"
    "110 ite 1 " + encoder->nids_stmt[2][1] + " " + encoder->nids_exec[2][1] + " 109 2:1:STORE:1\n"
    "111 next 1 " + encoder->nids_stmt[2][2] + " 110 2:2:JNZ:0\n"
    "\n"
    "; stmt_2_3\n"
    "112 init 1 " + encoder->nids_stmt[2][3] + " " + encoder->nid_false + "\n"
    "113 and 1 " + encoder->nids_stmt[2][3] + " -" + encoder->nids_exec[2][3] + "\n"
    "114 and 1 " + encoder->nids_exec[2][2] + " -100\n"
    "115 ite 1 " + encoder->nids_stmt[2][2] + " 114 113 2:2:JNZ:0\n"
    "116 next 1 " + encoder->nids_stmt[2][3] + " 115 2:3:EXIT:1\n"
    "\n",
    encoder->str());

  /* TODO remove
  reset_encoder(4);

  encoder->declare_sorts();
  encoder->declare_constants();
  encoder->add_bound();
  encoder->declare_states();
  encoder->add_thread_scheduling();
  encoder->add_checkpoint_constraints();
  encoder->add_statement_execution();
  encoder->add_statement_activation();

  string formula = encoder->str() + eol;

  formula +=
    btor2::next(
      encoder->nid(),
      encoder->sid_bv,
      encoder->nids_accu[1],
      encoder->nids_const[1]);

  formula += btor2::constraint(encoder->nid(), encoder->nids_thread[1]);

  cout << formula;

  evaluate(formula);
  */
}

TEST_F(Btor2_Encoder_Test, add_statement_activation_jmp_twice)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(
      create_program(
        "ADDI 1\n"
        "STORE 1\n"
        "JZ 1\n"
        "JNZ 1\n"
        "EXIT 1\n"));

  reset_encoder(3);

  init_statement_activation(true);

  encoder->add_statement_activation();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; statement activation state definitions\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_0_0\n"
    "66 init 1 " + encoder->nids_stmt[0][0] + " " + encoder->nid_true + "\n"
    "67 and 1 " + encoder->nids_stmt[0][0] + " -" + encoder->nids_exec[0][0] + "\n"
    "68 next 1 " + encoder->nids_stmt[0][0] + " 67 0:0:ADDI:1\n"
    "\n"
    "; stmt_0_1\n"
    "69 init 1 " + encoder->nids_stmt[0][1] + " " + encoder->nid_false + "\n"
    "70 and 1 " + encoder->nids_stmt[0][1] + " -" + encoder->nids_exec[0][1] + "\n"
    "71 ite 1 " + encoder->nids_stmt[0][0] + " " + encoder->nids_exec[0][0] + " 70 0:0:ADDI:1\n"
    "72 eq 1 " + encoder->nids_accu[0] + " " + encoder->nids_const[0] + "\n"
    "73 and 1 " + encoder->nids_exec[0][2] + " 72\n"
    "74 ite 1 " + encoder->nids_stmt[0][2] + " 73 71 0:2:JZ:1\n"
    "75 ne 1 " + encoder->nids_accu[0] + " " + encoder->nids_const[0] + "\n"
    "76 and 1 " + encoder->nids_exec[0][3] + " 75\n"
    "77 ite 1 " + encoder->nids_stmt[0][3] + " 76 74 0:3:JNZ:1\n"
    "78 next 1 " + encoder->nids_stmt[0][1] + " 77 0:1:STORE:1\n"
    "\n"
    "; stmt_0_2\n"
    "79 init 1 " + encoder->nids_stmt[0][2] + " " + encoder->nid_false + "\n"
    "80 and 1 " + encoder->nids_stmt[0][2] + " -" + encoder->nids_exec[0][2] + "\n"
    "81 ite 1 " + encoder->nids_stmt[0][1] + " " + encoder->nids_exec[0][1] + " 80 0:1:STORE:1\n"
    "82 next 1 " + encoder->nids_stmt[0][2] + " 81 0:2:JZ:1\n"
    "\n"
    "; stmt_0_3\n"
    "83 init 1 " + encoder->nids_stmt[0][3] + " " + encoder->nid_false + "\n"
    "84 and 1 " + encoder->nids_stmt[0][3] + " -" + encoder->nids_exec[0][3] + "\n"
    "85 and 1 " + encoder->nids_exec[0][2] + " -72\n"
    "86 ite 1 " + encoder->nids_stmt[0][2] + " 85 84 0:2:JZ:1\n"
    "87 next 1 " + encoder->nids_stmt[0][3] + " 86 0:3:JNZ:1\n"
    "\n"
    "; stmt_0_4\n"
    "88 init 1 " + encoder->nids_stmt[0][4] + " " + encoder->nid_false + "\n"
    "89 and 1 " + encoder->nids_stmt[0][4] + " -" + encoder->nids_exec[0][4] + "\n"
    "90 and 1 " + encoder->nids_exec[0][3] + " -75\n"
    "91 ite 1 " + encoder->nids_stmt[0][3] + " 90 89 0:3:JNZ:1\n"
    "92 next 1 " + encoder->nids_stmt[0][4] + " 91 0:4:EXIT:1\n"
    "\n"
    "; stmt_1_0\n"
    "93 init 1 " + encoder->nids_stmt[1][0] + " " + encoder->nid_true + "\n"
    "94 and 1 " + encoder->nids_stmt[1][0] + " -" + encoder->nids_exec[1][0] + "\n"
    "95 next 1 " + encoder->nids_stmt[1][0] + " 94 1:0:ADDI:1\n"
    "\n"
    "; stmt_1_1\n"
    "96 init 1 " + encoder->nids_stmt[1][1] + " " + encoder->nid_false + "\n"
    "97 and 1 " + encoder->nids_stmt[1][1] + " -" + encoder->nids_exec[1][1] + "\n"
    "98 ite 1 " + encoder->nids_stmt[1][0] + " " + encoder->nids_exec[1][0] + " 97 1:0:ADDI:1\n"
    "99 eq 1 " + encoder->nids_accu[1] + " " + encoder->nids_const[0] + "\n"
    "100 and 1 " + encoder->nids_exec[1][2] + " 99\n"
    "101 ite 1 " + encoder->nids_stmt[1][2] + " 100 98 1:2:JZ:1\n"
    "102 ne 1 " + encoder->nids_accu[1] + " " + encoder->nids_const[0] + "\n"
    "103 and 1 " + encoder->nids_exec[1][3] + " 102\n"
    "104 ite 1 " + encoder->nids_stmt[1][3] + " 103 101 1:3:JNZ:1\n"
    "105 next 1 " + encoder->nids_stmt[1][1] + " 104 1:1:STORE:1\n"
    "\n"
    "; stmt_1_2\n"
    "106 init 1 " + encoder->nids_stmt[1][2] + " " + encoder->nid_false + "\n"
    "107 and 1 " + encoder->nids_stmt[1][2] + " -" + encoder->nids_exec[1][2] + "\n"
    "108 ite 1 " + encoder->nids_stmt[1][1] + " " + encoder->nids_exec[1][1] + " 107 1:1:STORE:1\n"
    "109 next 1 " + encoder->nids_stmt[1][2] + " 108 1:2:JZ:1\n"
    "\n"
    "; stmt_1_3\n"
    "110 init 1 " + encoder->nids_stmt[1][3] + " " + encoder->nid_false + "\n"
    "111 and 1 " + encoder->nids_stmt[1][3] + " -" + encoder->nids_exec[1][3] + "\n"
    "112 and 1 " + encoder->nids_exec[1][2] + " -99\n"
    "113 ite 1 " + encoder->nids_stmt[1][2] + " 112 111 1:2:JZ:1\n"
    "114 next 1 " + encoder->nids_stmt[1][3] + " 113 1:3:JNZ:1\n"
    "\n"
    "; stmt_1_4\n"
    "115 init 1 " + encoder->nids_stmt[1][4] + " " + encoder->nid_false + "\n"
    "116 and 1 " + encoder->nids_stmt[1][4] + " -" + encoder->nids_exec[1][4] + "\n"
    "117 and 1 " + encoder->nids_exec[1][3] + " -102\n"
    "118 ite 1 " + encoder->nids_stmt[1][3] + " 117 116 1:3:JNZ:1\n"
    "119 next 1 " + encoder->nids_stmt[1][4] + " 118 1:4:EXIT:1\n"
    "\n"
    "; stmt_2_0\n"
    "120 init 1 " + encoder->nids_stmt[2][0] + " " + encoder->nid_true + "\n"
    "121 and 1 " + encoder->nids_stmt[2][0] + " -" + encoder->nids_exec[2][0] + "\n"
    "122 next 1 " + encoder->nids_stmt[2][0] + " 121 2:0:ADDI:1\n"
    "\n"
    "; stmt_2_1\n"
    "123 init 1 " + encoder->nids_stmt[2][1] + " " + encoder->nid_false + "\n"
    "124 and 1 " + encoder->nids_stmt[2][1] + " -" + encoder->nids_exec[2][1] + "\n"
    "125 ite 1 " + encoder->nids_stmt[2][0] + " " + encoder->nids_exec[2][0] + " 124 2:0:ADDI:1\n"
    "126 eq 1 " + encoder->nids_accu[2] + " " + encoder->nids_const[0] + "\n"
    "127 and 1 " + encoder->nids_exec[2][2] + " 126\n"
    "128 ite 1 " + encoder->nids_stmt[2][2] + " 127 125 2:2:JZ:1\n"
    "129 ne 1 " + encoder->nids_accu[2] + " " + encoder->nids_const[0] + "\n"
    "130 and 1 " + encoder->nids_exec[2][3] + " 129\n"
    "131 ite 1 " + encoder->nids_stmt[2][3] + " 130 128 2:3:JNZ:1\n"
    "132 next 1 " + encoder->nids_stmt[2][1] + " 131 2:1:STORE:1\n"
    "\n"
    "; stmt_2_2\n"
    "133 init 1 " + encoder->nids_stmt[2][2] + " " + encoder->nid_false + "\n"
    "134 and 1 " + encoder->nids_stmt[2][2] + " -" + encoder->nids_exec[2][2] + "\n"
    "135 ite 1 " + encoder->nids_stmt[2][1] + " " + encoder->nids_exec[2][1] + " 134 2:1:STORE:1\n"
    "136 next 1 " + encoder->nids_stmt[2][2] + " 135 2:2:JZ:1\n"
    "\n"
    "; stmt_2_3\n"
    "137 init 1 " + encoder->nids_stmt[2][3] + " " + encoder->nid_false + "\n"
    "138 and 1 " + encoder->nids_stmt[2][3] + " -" + encoder->nids_exec[2][3] + "\n"
    "139 and 1 " + encoder->nids_exec[2][2] + " -126\n"
    "140 ite 1 " + encoder->nids_stmt[2][2] + " 139 138 2:2:JZ:1\n"
    "141 next 1 " + encoder->nids_stmt[2][3] + " 140 2:3:JNZ:1\n"
    "\n"
    "; stmt_2_4\n"
    "142 init 1 " + encoder->nids_stmt[2][4] + " " + encoder->nid_false + "\n"
    "143 and 1 " + encoder->nids_stmt[2][4] + " -" + encoder->nids_exec[2][4] + "\n"
    "144 and 1 " + encoder->nids_exec[2][3] + " -129\n"
    "145 ite 1 " + encoder->nids_stmt[2][3] + " 144 143 2:3:JNZ:1\n"
    "146 next 1 " + encoder->nids_stmt[2][4] + " 145 2:4:EXIT:1\n"
    "\n",
    encoder->str());

  /* TODO remove
  reset_encoder(10);

  encoder->declare_sorts();
  encoder->declare_constants();
  encoder->add_bound();
  encoder->declare_states();
  encoder->add_thread_scheduling();
  encoder->add_checkpoint_constraints();
  encoder->add_statement_execution();
  encoder->add_statement_activation();

  string formula = encoder->str() + eol;

  formula +=
    btor2::next(
      encoder->nid(),
      encoder->sid_bv,
      encoder->nids_accu[1],
      encoder->nids_const[0]);

  formula += btor2::constraint(encoder->nid(), encoder->nids_thread[1]);

  cout << formula;

  evaluate(formula);
  */
}

// void Btor2_Encoder::add_register_definitions ()
TEST_F(Btor2_Encoder_Test, add_register_definitions)
{
  add_instruction_set(3);
  reset_encoder();

  init_register_definitions(true);

  encoder->add_register_definitions();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; register state definitions\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accumulator definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu_0\n"
    "413 init 2 " + encoder->nids_accu[0] + " " + encoder->nids_const[0] + "\n"
    "414 read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n"
    "415 ite 2 " + encoder->nids_exec[0][0] + " 414 " + encoder->nids_accu[0] + " 0:0:LOAD:1\n"
    "416 add 2 " + encoder->nids_accu[0] + " 414\n"
    "417 ite 2 " + encoder->nids_exec[0][2] + " 416 415 0:2:ADD:1\n"
    "418 add 2 " + encoder->nids_accu[0] + " " + encoder->nids_const[1] + "\n"
    "419 ite 2 " + encoder->nids_exec[0][3] + " 418 417 0:3:ADDI:1\n"
    "420 sub 2 " + encoder->nids_accu[0] + " 414\n"
    "421 ite 2 " + encoder->nids_exec[0][4] + " 420 419 0:4:SUB:1\n"
    "422 sub 2 " + encoder->nids_accu[0] + " " + encoder->nids_const[1] + "\n"
    "423 ite 2 " + encoder->nids_exec[0][5] + " 422 421 0:5:SUBI:1\n"
    "424 sub 2 " + encoder->nids_accu[0] + " 414\n"
    "425 ite 2 " + encoder->nids_exec[0][6] + " 424 423 0:6:CMP:1\n"
    "426 ite 2 " + encoder->nids_exec[0][13] + " 414 425 0:13:MEM:1\n"
    "427 eq 1 " + encoder->nids_mem[0] + " 414\n"
    "428 ite 2 427 " + encoder->nids_const[1] + " " + encoder->nids_const[0] + "\n"
    "429 ite 2 " + encoder->nids_exec[0][14] + " 428 426 0:14:CAS:1\n"
    "430 next 2 " + encoder->nids_accu[0] + " 429 accu_0\n"
    "\n"
    "; accu_1\n"
    "431 init 2 " + encoder->nids_accu[1] + " " + encoder->nids_const[0] + "\n"
    "432 ite 2 " + encoder->nids_exec[1][0] + " 414 " + encoder->nids_accu[1] + " 1:0:LOAD:1\n"
    "433 add 2 " + encoder->nids_accu[1] + " 414\n"
    "434 ite 2 " + encoder->nids_exec[1][2] + " 433 432 1:2:ADD:1\n"
    "435 add 2 " + encoder->nids_accu[1] + " " + encoder->nids_const[1] + "\n"
    "436 ite 2 " + encoder->nids_exec[1][3] + " 435 434 1:3:ADDI:1\n"
    "437 sub 2 " + encoder->nids_accu[1] + " 414\n"
    "438 ite 2 " + encoder->nids_exec[1][4] + " 437 436 1:4:SUB:1\n"
    "439 sub 2 " + encoder->nids_accu[1] + " " + encoder->nids_const[1] + "\n"
    "440 ite 2 " + encoder->nids_exec[1][5] + " 439 438 1:5:SUBI:1\n"
    "441 sub 2 " + encoder->nids_accu[1] + " 414\n"
    "442 ite 2 " + encoder->nids_exec[1][6] + " 441 440 1:6:CMP:1\n"
    "443 ite 2 " + encoder->nids_exec[1][13] + " 414 442 1:13:MEM:1\n"
    "444 eq 1 " + encoder->nids_mem[1] + " 414\n"
    "445 ite 2 444 " + encoder->nids_const[1] + " " + encoder->nids_const[0] + "\n"
    "446 ite 2 " + encoder->nids_exec[1][14] + " 445 443 1:14:CAS:1\n"
    "447 next 2 " + encoder->nids_accu[1] + " 446 accu_1\n"
    "\n"
    "; accu_2\n"
    "448 init 2 " + encoder->nids_accu[2] + " " + encoder->nids_const[0] + "\n"
    "449 ite 2 " + encoder->nids_exec[2][0] + " 414 " + encoder->nids_accu[2] + " 2:0:LOAD:1\n"
    "450 add 2 " + encoder->nids_accu[2] + " 414\n"
    "451 ite 2 " + encoder->nids_exec[2][2] + " 450 449 2:2:ADD:1\n"
    "452 add 2 " + encoder->nids_accu[2] + " " + encoder->nids_const[1] + "\n"
    "453 ite 2 " + encoder->nids_exec[2][3] + " 452 451 2:3:ADDI:1\n"
    "454 sub 2 " + encoder->nids_accu[2] + " 414\n"
    "455 ite 2 " + encoder->nids_exec[2][4] + " 454 453 2:4:SUB:1\n"
    "456 sub 2 " + encoder->nids_accu[2] + " " + encoder->nids_const[1] + "\n"
    "457 ite 2 " + encoder->nids_exec[2][5] + " 456 455 2:5:SUBI:1\n"
    "458 sub 2 " + encoder->nids_accu[2] + " 414\n"
    "459 ite 2 " + encoder->nids_exec[2][6] + " 458 457 2:6:CMP:1\n"
    "460 ite 2 " + encoder->nids_exec[2][13] + " 414 459 2:13:MEM:1\n"
    "461 eq 1 " + encoder->nids_mem[2] + " 414\n"
    "462 ite 2 461 " + encoder->nids_const[1] + " " + encoder->nids_const[0] + "\n"
    "463 ite 2 " + encoder->nids_exec[2][14] + " 462 460 2:14:CAS:1\n"
    "464 next 2 " + encoder->nids_accu[2] + " 463 accu_2\n"
    "\n"
    "; CAS memory register definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; mem_0\n"
    "465 init 2 " + encoder->nids_mem[0] + " " + encoder->nids_const[0] + "\n"
    "466 ite 2 " + encoder->nids_exec[0][13] + " 414 " + encoder->nids_mem[0] + " 0:13:MEM:1\n"
    "467 next 2 " + encoder->nids_mem[0] + " 466 mem_0\n"
    "\n"
    "; mem_1\n"
    "468 init 2 " + encoder->nids_mem[1] + " " + encoder->nids_const[0] + "\n"
    "469 ite 2 " + encoder->nids_exec[1][13] + " 414 " + encoder->nids_mem[1] + " 1:13:MEM:1\n"
    "470 next 2 " + encoder->nids_mem[1] + " 469 mem_1\n"
    "\n"
    "; mem_2\n"
    "471 init 2 " + encoder->nids_mem[2] + " " + encoder->nids_const[0] + "\n"
    "472 ite 2 " + encoder->nids_exec[2][13] + " 414 " + encoder->nids_mem[2] + " 2:13:MEM:1\n"
    "473 next 2 " + encoder->nids_mem[2] + " 472 mem_2\n"
    "\n",
    encoder->str());

  /* verbosity */
  reset_encoder();

  init_register_definitions(true);

  verbose = false;
  encoder->add_register_definitions();
  verbose = true;

  ASSERT_EQ(
    "413 init 2 " + encoder->nids_accu[0] + " " + encoder->nids_const[0] + "\n"
    "414 read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n"
    "415 ite 2 " + encoder->nids_exec[0][0] + " 414 " + encoder->nids_accu[0] + "\n"
    "416 add 2 " + encoder->nids_accu[0] + " 414\n"
    "417 ite 2 " + encoder->nids_exec[0][2] + " 416 415\n"
    "418 add 2 " + encoder->nids_accu[0] + " " + encoder->nids_const[1] + "\n"
    "419 ite 2 " + encoder->nids_exec[0][3] + " 418 417\n"
    "420 sub 2 " + encoder->nids_accu[0] + " 414\n"
    "421 ite 2 " + encoder->nids_exec[0][4] + " 420 419\n"
    "422 sub 2 " + encoder->nids_accu[0] + " " + encoder->nids_const[1] + "\n"
    "423 ite 2 " + encoder->nids_exec[0][5] + " 422 421\n"
    "424 sub 2 " + encoder->nids_accu[0] + " 414\n"
    "425 ite 2 " + encoder->nids_exec[0][6] + " 424 423\n"
    "426 ite 2 " + encoder->nids_exec[0][13] + " 414 425\n"
    "427 eq 1 " + encoder->nids_mem[0] + " 414\n"
    "428 ite 2 427 " + encoder->nids_const[1] + " " + encoder->nids_const[0] + "\n"
    "429 ite 2 " + encoder->nids_exec[0][14] + " 428 426\n"
    "430 next 2 " + encoder->nids_accu[0] + " 429 accu_0\n"
    "\n"
    "431 init 2 " + encoder->nids_accu[1] + " " + encoder->nids_const[0] + "\n"
    "432 ite 2 " + encoder->nids_exec[1][0] + " 414 " + encoder->nids_accu[1] + "\n"
    "433 add 2 " + encoder->nids_accu[1] + " 414\n"
    "434 ite 2 " + encoder->nids_exec[1][2] + " 433 432\n"
    "435 add 2 " + encoder->nids_accu[1] + " " + encoder->nids_const[1] + "\n"
    "436 ite 2 " + encoder->nids_exec[1][3] + " 435 434\n"
    "437 sub 2 " + encoder->nids_accu[1] + " 414\n"
    "438 ite 2 " + encoder->nids_exec[1][4] + " 437 436\n"
    "439 sub 2 " + encoder->nids_accu[1] + " " + encoder->nids_const[1] + "\n"
    "440 ite 2 " + encoder->nids_exec[1][5] + " 439 438\n"
    "441 sub 2 " + encoder->nids_accu[1] + " 414\n"
    "442 ite 2 " + encoder->nids_exec[1][6] + " 441 440\n"
    "443 ite 2 " + encoder->nids_exec[1][13] + " 414 442\n"
    "444 eq 1 " + encoder->nids_mem[1] + " 414\n"
    "445 ite 2 444 " + encoder->nids_const[1] + " " + encoder->nids_const[0] + "\n"
    "446 ite 2 " + encoder->nids_exec[1][14] + " 445 443\n"
    "447 next 2 " + encoder->nids_accu[1] + " 446 accu_1\n"
    "\n"
    "448 init 2 " + encoder->nids_accu[2] + " " + encoder->nids_const[0] + "\n"
    "449 ite 2 " + encoder->nids_exec[2][0] + " 414 " + encoder->nids_accu[2] + "\n"
    "450 add 2 " + encoder->nids_accu[2] + " 414\n"
    "451 ite 2 " + encoder->nids_exec[2][2] + " 450 449\n"
    "452 add 2 " + encoder->nids_accu[2] + " " + encoder->nids_const[1] + "\n"
    "453 ite 2 " + encoder->nids_exec[2][3] + " 452 451\n"
    "454 sub 2 " + encoder->nids_accu[2] + " 414\n"
    "455 ite 2 " + encoder->nids_exec[2][4] + " 454 453\n"
    "456 sub 2 " + encoder->nids_accu[2] + " " + encoder->nids_const[1] + "\n"
    "457 ite 2 " + encoder->nids_exec[2][5] + " 456 455\n"
    "458 sub 2 " + encoder->nids_accu[2] + " 414\n"
    "459 ite 2 " + encoder->nids_exec[2][6] + " 458 457\n"
    "460 ite 2 " + encoder->nids_exec[2][13] + " 414 459\n"
    "461 eq 1 " + encoder->nids_mem[2] + " 414\n"
    "462 ite 2 461 " + encoder->nids_const[1] + " " + encoder->nids_const[0] + "\n"
    "463 ite 2 " + encoder->nids_exec[2][14] + " 462 460\n"
    "464 next 2 " + encoder->nids_accu[2] + " 463 accu_2\n"
    "\n"
    "465 init 2 " + encoder->nids_mem[0] + " " + encoder->nids_const[0] + "\n"
    "466 ite 2 " + encoder->nids_exec[0][13] + " 414 " + encoder->nids_mem[0] + "\n"
    "467 next 2 " + encoder->nids_mem[0] + " 466 mem_0\n"
    "\n"
    "468 init 2 " + encoder->nids_mem[1] + " " + encoder->nids_const[0] + "\n"
    "469 ite 2 " + encoder->nids_exec[1][13] + " 414 " + encoder->nids_mem[1] + "\n"
    "470 next 2 " + encoder->nids_mem[1] + " 469 mem_1\n"
    "\n"
    "471 init 2 " + encoder->nids_mem[2] + " " + encoder->nids_const[0] + "\n"
    "472 ite 2 " + encoder->nids_exec[2][13] + " 414 " + encoder->nids_mem[2] + "\n"
    "473 next 2 " + encoder->nids_mem[2] + " 472 mem_2\n"
    "\n",
    encoder->str());
}

// void Btor2_Encoder::add_heap_definition ()
TEST_F(Btor2_Encoder_Test, add_heap_definition)
{
  add_instruction_set(3);
  reset_encoder();

  init_heap_definition(true);

  encoder->add_heap_definition();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; heap state definition\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "474 write 3 " + encoder->nid_heap + " " + encoder->nids_const[1] + " " + encoder->nids_accu[0] + "\n"
    "475 ite 3 " + encoder->nids_exec[0][1] + " 474 " + encoder->nid_heap + " 0:1:STORE:1\n"
    "476 eq 1 " + encoder->nids_mem[0] + " 414\n"
    "477 ite 3 476 474 " + encoder->nid_heap + "\n"
    "478 ite 3 " + encoder->nids_exec[0][14] + " 477 475 0:14:CAS:1\n"
    "479 write 3 " + encoder->nid_heap + " " + encoder->nids_const[1] + " " + encoder->nids_accu[1] + "\n"
    "480 ite 3 " + encoder->nids_exec[1][1] + " 479 478 1:1:STORE:1\n"
    "481 eq 1 " + encoder->nids_mem[1] + " 414\n"
    "482 ite 3 481 479 " + encoder->nid_heap + "\n"
    "483 ite 3 " + encoder->nids_exec[1][14] + " 482 480 1:14:CAS:1\n"
    "484 write 3 " + encoder->nid_heap + " " + encoder->nids_const[1] + " " + encoder->nids_accu[2] + "\n"
    "485 ite 3 " + encoder->nids_exec[2][1] + " 484 483 2:1:STORE:1\n"
    "486 eq 1 " + encoder->nids_mem[2] + " 414\n"
    "487 ite 3 486 484 " + encoder->nid_heap + "\n"
    "488 ite 3 " + encoder->nids_exec[2][14] + " 487 485 2:14:CAS:1\n"
    "489 next 3 " + encoder->nid_heap + " 488 heap\n"
    "\n",
    encoder->str());

  /* verbosity */
  reset_encoder();

  init_heap_definition(true);

  verbose = false;
  encoder->add_heap_definition();
  verbose = true;

  ASSERT_EQ(
    "474 write 3 " + encoder->nid_heap + " " + encoder->nids_const[1] + " " + encoder->nids_accu[0] + "\n"
    "475 ite 3 " + encoder->nids_exec[0][1] + " 474 " + encoder->nid_heap + "\n"
    "476 eq 1 " + encoder->nids_mem[0] + " 414\n"
    "477 ite 3 476 474 " + encoder->nid_heap + "\n"
    "478 ite 3 " + encoder->nids_exec[0][14] + " 477 475\n"
    "479 write 3 " + encoder->nid_heap + " " + encoder->nids_const[1] + " " + encoder->nids_accu[1] + "\n"
    "480 ite 3 " + encoder->nids_exec[1][1] + " 479 478\n"
    "481 eq 1 " + encoder->nids_mem[1] + " 414\n"
    "482 ite 3 481 479 " + encoder->nid_heap + "\n"
    "483 ite 3 " + encoder->nids_exec[1][14] + " 482 480\n"
    "484 write 3 " + encoder->nid_heap + " " + encoder->nids_const[1] + " " + encoder->nids_accu[2] + "\n"
    "485 ite 3 " + encoder->nids_exec[2][1] + " 484 483\n"
    "486 eq 1 " + encoder->nids_mem[2] + " 414\n"
    "487 ite 3 486 484 " + encoder->nid_heap + "\n"
    "488 ite 3 " + encoder->nids_exec[2][14] + " 487 485\n"
    "489 next 3 " + encoder->nid_heap + " 488 heap\n"
    "\n",
    encoder->str());
}

// void Btor2_Encoder::add_exit_definitions ()
TEST_F(Btor2_Encoder_Test, add_exit_definitions)
{
  add_instruction_set(3);
  reset_encoder();

  init_exit_definitions(true);

  encoder->add_exit_definitions();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit state definitions\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; exit flag\n"
    "490 init 1 " + encoder->nid_exit_flag + " " + encoder->nid_false + "\n"
    "491 or 1 " + encoder->nid_exit_flag + " " + encoder->nids_exec[2][16] + "\n"
    "492 or 1 " + encoder->nids_exec[0][16] + " 491\n"
    "493 or 1 " + encoder->nids_exec[1][16] + " 492\n"
    "494 next 1 " + encoder->nid_exit_flag + " 493 exit\n"
    "\n"
    "; exit code\n"
    "495 state 2 exit-code\n"
    "496 init 2 " + encoder->nid_exit_code + " " + encoder->nids_const[0] + "\n"
    "497 ite 2 " + encoder->nids_exec[0][16] + " " + encoder->nids_const[1] + " " + encoder->nid_exit_code + " 0:16:EXIT:1\n"
    "498 ite 2 " + encoder->nids_exec[1][16] + " " + encoder->nids_const[1] + " 497 1:16:EXIT:1\n"
    "499 ite 2 " + encoder->nids_exec[2][16] + " " + encoder->nids_const[1] + " 498 2:16:EXIT:1\n"
    "500 next 2 " + encoder->nid_exit_code + " 499 exit-code\n"
    "\n",
    encoder->str());

  /* verbosity */
  reset_encoder();

  init_exit_definitions(true);

  verbose = false;
  encoder->add_exit_definitions();
  verbose = true;

  ASSERT_EQ(
    "490 init 1 " + encoder->nid_exit_flag + " " + encoder->nid_false + "\n"
    "491 or 1 " + encoder->nid_exit_flag + " " + encoder->nids_exec[2][16] + "\n"
    "492 or 1 " + encoder->nids_exec[0][16] + " 491\n"
    "493 or 1 " + encoder->nids_exec[1][16] + " 492\n"
    "494 next 1 " + encoder->nid_exit_flag + " 493 exit\n"
    "\n"
    "495 state 2 exit-code\n"
    "496 init 2 " + encoder->nid_exit_code + " " + encoder->nids_const[0] + "\n"
    "497 ite 2 " + encoder->nids_exec[0][16] + " " + encoder->nids_const[1] + " " + encoder->nid_exit_code + "\n"
    "498 ite 2 " + encoder->nids_exec[1][16] + " " + encoder->nids_const[1] + " 497\n"
    "499 ite 2 " + encoder->nids_exec[2][16] + " " + encoder->nids_const[1] + " 498\n"
    "500 next 2 " + encoder->nid_exit_code + " 499 exit-code\n"
    "\n",
    encoder->str());
}

TEST_F(Btor2_Encoder_Test, add_exit_definitions_no_exit)
{
  add_dummy_programs(1);
  reset_encoder();

  init_exit_definitions(true);

  encoder->add_exit_definitions();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit state definitions\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; exit flag\n"
    "29 init 1 " + encoder->nid_exit_flag + " " + encoder->nid_false + "\n"
    "30 next 1 " + encoder->nid_exit_flag + " " + encoder->nid_exit_flag + " exit\n"
    "\n"
    "; exit code\n"
    "31 state 2 exit-code\n"
    "32 init 2 " + encoder->nid_exit_code + " " + encoder->nids_const[0] + "\n"
    "33 next 2 " + encoder->nid_exit_code + " " + encoder->nid_exit_code + " exit-code\n"
    "\n",
    encoder->str());
}

// void Btor2_Encoder::add_checkpoint_constraints ()
TEST_F(Btor2_Encoder_Test, add_checkpoint_constraints)
{
  for (size_t thread = 0; thread < 3; thread++)
    {
      Program_ptr program = make_shared<Program>();

      programs.push_back(program);

      for (size_t id = 1; id < 3; id++)
        program->push_back(Instruction::Set::create("CHECK", id));
    }

  reset_encoder();

  init_checkpoint_constraints(true);

  encoder->add_checkpoint_constraints();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; checkpoint constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread blocking flags - block_<id>_<thread>\n"
    "87 state 1 block_1_0\n"
    "88 state 1 block_1_1\n"
    "89 state 1 block_1_2\n"
    "\n"
    "90 state 1 block_2_0\n"
    "91 state 1 block_2_1\n"
    "92 state 1 block_2_2\n"
    "\n"
    "; checkpoint flags - check_<id>\n"
    "93 and 1 " + encoder->nids_block[1][0] + " " + encoder->nids_block[1][1] + "\n"
    "94 and 1 " + encoder->nids_block[1][2] + " 93 check_1\n"
    "95 and 1 " + encoder->nids_block[2][0] + " " + encoder->nids_block[2][1] + "\n"
    "96 and 1 " + encoder->nids_block[2][2] + " 95 check_2\n"
    "\n"
    "; thread blocking flag definitions\n"
    "97 init 1 " + encoder->nids_block[1][0] + " 4\n"
    "98 or 1 " + encoder->nids_exec[0][0] + " " + encoder->nids_block[1][0] + "\n"
    "99 ite 1 " + encoder->nids_check[1] + " 4 98\n"
    "100 next 1 " + encoder->nids_block[1][0] + " 99 block_1_0\n"
    "\n"
    "101 init 1 " + encoder->nids_block[1][1] + " 4\n"
    "102 or 1 " + encoder->nids_exec[1][0] + " " + encoder->nids_block[1][1] + "\n"
    "103 ite 1 " + encoder->nids_check[1] + " 4 102\n"
    "104 next 1 " + encoder->nids_block[1][1] + " 103 block_1_1\n"
    "\n"
    "105 init 1 " + encoder->nids_block[1][2] + " 4\n"
    "106 or 1 " + encoder->nids_exec[2][0] + " " + encoder->nids_block[1][2] + "\n"
    "107 ite 1 " + encoder->nids_check[1] + " 4 106\n"
    "108 next 1 " + encoder->nids_block[1][2] + " 107 block_1_2\n"
    "\n"
    "109 init 1 " + encoder->nids_block[2][0] + " 4\n"
    "110 or 1 " + encoder->nids_exec[0][1] + " " + encoder->nids_block[2][0] + "\n"
    "111 ite 1 " + encoder->nids_check[2] + " 4 110\n"
    "112 next 1 " + encoder->nids_block[2][0] + " 111 block_2_0\n"
    "\n"
    "113 init 1 " + encoder->nids_block[2][1] + " 4\n"
    "114 or 1 " + encoder->nids_exec[1][1] + " " + encoder->nids_block[2][1] + "\n"
    "115 ite 1 " + encoder->nids_check[2] + " 4 114\n"
    "116 next 1 " + encoder->nids_block[2][1] + " 115 block_2_1\n"
    "\n"
    "117 init 1 " + encoder->nids_block[2][2] + " 4\n"
    "118 or 1 " + encoder->nids_exec[2][1] + " " + encoder->nids_block[2][2] + "\n"
    "119 ite 1 " + encoder->nids_check[2] + " 4 118\n"
    "120 next 1 " + encoder->nids_block[2][2] + " 119 block_2_2\n"
    "\n"
    "; prevent scheduling of blocked threads\n"
    "121 and 1 " + encoder->nids_block[1][0] + " -" + encoder->nids_check[1] + "\n"
    "122 implies 1 121 -" + encoder->nids_thread[0] + "\n"
    "123 constraint 122 block_1_0\n"
    "\n"
    "124 and 1 " + encoder->nids_block[1][1] + " -" + encoder->nids_check[1] + "\n"
    "125 implies 1 124 -" + encoder->nids_thread[1] + "\n"
    "126 constraint 125 block_1_1\n"
    "\n"
    "127 and 1 " + encoder->nids_block[1][2] + " -" + encoder->nids_check[1] + "\n"
    "128 implies 1 127 -" + encoder->nids_thread[2] + "\n"
    "129 constraint 128 block_1_2\n"
    "\n"
    "130 and 1 " + encoder->nids_block[2][0] + " -" + encoder->nids_check[2] + "\n"
    "131 implies 1 130 -" + encoder->nids_thread[0] + "\n"
    "132 constraint 131 block_2_0\n"
    "\n"
    "133 and 1 " + encoder->nids_block[2][1] + " -" + encoder->nids_check[2] + "\n"
    "134 implies 1 133 -" + encoder->nids_thread[1] + "\n"
    "135 constraint 134 block_2_1\n"
    "\n"
    "136 and 1 " + encoder->nids_block[2][2] + " -" + encoder->nids_check[2] + "\n"
    "137 implies 1 136 -" + encoder->nids_thread[2] + "\n"
    "138 constraint 137 block_2_2\n"
    "\n",
    encoder->str());

  /* multiple calls to the same checkpoint */
  for (const auto & program : programs)
    for (size_t pc = 0; pc < 4; pc++)
      program->push_back(Instruction::Set::create("CHECK", pc % 2 + 1));

  reset_encoder();

  init_checkpoint_constraints(true);

  encoder->add_checkpoint_constraints();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; checkpoint constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread blocking flags - block_<id>_<thread>\n"
    "159 state 1 block_1_0\n"
    "160 state 1 block_1_1\n"
    "161 state 1 block_1_2\n"
    "\n"
    "162 state 1 block_2_0\n"
    "163 state 1 block_2_1\n"
    "164 state 1 block_2_2\n"
    "\n"
    "; checkpoint flags - check_<id>\n"
    "165 and 1 " + encoder->nids_block[1][0] + " " + encoder->nids_block[1][1] + "\n"
    "166 and 1 " + encoder->nids_block[1][2] + " 165 check_1\n"
    "167 and 1 " + encoder->nids_block[2][0] + " " + encoder->nids_block[2][1] + "\n"
    "168 and 1 " + encoder->nids_block[2][2] + " 167 check_2\n"
    "\n"
    "; thread blocking flag definitions\n"
    "169 init 1 " + encoder->nids_block[1][0] + " 4\n"
    "170 or 1 " + encoder->nids_exec[0][0] + " " + encoder->nids_exec[0][2] + "\n"
    "171 or 1 " + encoder->nids_exec[0][4] + " 170\n"
    "172 or 1 " + encoder->nids_block[1][0] + " 171\n"
    "173 ite 1 " + encoder->nids_check[1] + " 4 172\n"
    "174 next 1 " + encoder->nids_block[1][0] + " 173 block_1_0\n"
    "\n"
    "175 init 1 " + encoder->nids_block[1][1] + " 4\n"
    "176 or 1 " + encoder->nids_exec[1][0] + " " + encoder->nids_exec[1][2] + "\n"
    "177 or 1 " + encoder->nids_exec[1][4] + " 176\n"
    "178 or 1 " + encoder->nids_block[1][1] + " 177\n"
    "179 ite 1 " + encoder->nids_check[1] + " 4 178\n"
    "180 next 1 " + encoder->nids_block[1][1] + " 179 block_1_1\n"
    "\n"
    "181 init 1 " + encoder->nids_block[1][2] + " 4\n"
    "182 or 1 " + encoder->nids_exec[2][0] + " " + encoder->nids_exec[2][2] + "\n"
    "183 or 1 " + encoder->nids_exec[2][4] + " 182\n"
    "184 or 1 " + encoder->nids_block[1][2] + " 183\n"
    "185 ite 1 " + encoder->nids_check[1] + " 4 184\n"
    "186 next 1 " + encoder->nids_block[1][2] + " 185 block_1_2\n"
    "\n"
    "187 init 1 " + encoder->nids_block[2][0] + " 4\n"
    "188 or 1 " + encoder->nids_exec[0][1] + " " + encoder->nids_exec[0][3] + "\n"
    "189 or 1 " + encoder->nids_exec[0][5] + " 188\n"
    "190 or 1 " + encoder->nids_block[2][0] + " 189\n"
    "191 ite 1 " + encoder->nids_check[2] + " 4 190\n"
    "192 next 1 " + encoder->nids_block[2][0] + " 191 block_2_0\n"
    "\n"
    "193 init 1 " + encoder->nids_block[2][1] + " 4\n"
    "194 or 1 " + encoder->nids_exec[1][1] + " " + encoder->nids_exec[1][3] + "\n"
    "195 or 1 " + encoder->nids_exec[1][5] + " 194\n"
    "196 or 1 " + encoder->nids_block[2][1] + " 195\n"
    "197 ite 1 " + encoder->nids_check[2] + " 4 196\n"
    "198 next 1 " + encoder->nids_block[2][1] + " 197 block_2_1\n"
    "\n"
    "199 init 1 " + encoder->nids_block[2][2] + " 4\n"
    "200 or 1 " + encoder->nids_exec[2][1] + " " + encoder->nids_exec[2][3] + "\n"
    "201 or 1 " + encoder->nids_exec[2][5] + " 200\n"
    "202 or 1 " + encoder->nids_block[2][2] + " 201\n"
    "203 ite 1 " + encoder->nids_check[2] + " 4 202\n"
    "204 next 1 " + encoder->nids_block[2][2] + " 203 block_2_2\n"
    "\n"
    "; prevent scheduling of blocked threads\n"
    "205 and 1 " + encoder->nids_block[1][0] + " -" + encoder->nids_check[1] + "\n"
    "206 implies 1 205 -" + encoder->nids_thread[0] + "\n"
    "207 constraint 206 block_1_0\n"
    "\n"
    "208 and 1 " + encoder->nids_block[1][1] + " -" + encoder->nids_check[1] + "\n"
    "209 implies 1 208 -" + encoder->nids_thread[1] + "\n"
    "210 constraint 209 block_1_1\n"
    "\n"
    "211 and 1 " + encoder->nids_block[1][2] + " -" + encoder->nids_check[1] + "\n"
    "212 implies 1 211 -" + encoder->nids_thread[2] + "\n"
    "213 constraint 212 block_1_2\n"
    "\n"
    "214 and 1 " + encoder->nids_block[2][0] + " -" + encoder->nids_check[2] + "\n"
    "215 implies 1 214 -" + encoder->nids_thread[0] + "\n"
    "216 constraint 215 block_2_0\n"
    "\n"
    "217 and 1 " + encoder->nids_block[2][1] + " -" + encoder->nids_check[2] + "\n"
    "218 implies 1 217 -" + encoder->nids_thread[1] + "\n"
    "219 constraint 218 block_2_1\n"
    "\n"
    "220 and 1 " + encoder->nids_block[2][2] + " -" + encoder->nids_check[2] + "\n"
    "221 implies 1 220 -" + encoder->nids_thread[2] + "\n"
    "222 constraint 221 block_2_2\n"
    "\n",
    encoder->str());

  /* checkpoint only for a subset of threads */
  for (size_t i = 0; i < programs.size() - 1; i++)
    programs[i]->push_back(Instruction::Set::create("CHECK", 3));

  reset_encoder();

  init_checkpoint_constraints(true);

  encoder->add_checkpoint_constraints();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; checkpoint constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread blocking flags - block_<id>_<thread>\n"
    "172 state 1 block_1_0\n"
    "173 state 1 block_1_1\n"
    "174 state 1 block_1_2\n"
    "\n"
    "175 state 1 block_2_0\n"
    "176 state 1 block_2_1\n"
    "177 state 1 block_2_2\n"
    "\n"
    "178 state 1 block_3_0\n"
    "179 state 1 block_3_1\n"
    "\n"
    "; checkpoint flags - check_<id>\n"
    "180 and 1 " + encoder->nids_block[1][0] + " " + encoder->nids_block[1][1] + "\n"
    "181 and 1 " + encoder->nids_block[1][2] + " 180 check_1\n"
    "182 and 1 " + encoder->nids_block[2][0] + " " + encoder->nids_block[2][1] + "\n"
    "183 and 1 " + encoder->nids_block[2][2] + " 182 check_2\n"
    "184 and 1 " + encoder->nids_block[3][0] + " " + encoder->nids_block[3][1] + " check_3\n"
    "\n"
    "; thread blocking flag definitions\n"
    "185 init 1 " + encoder->nids_block[1][0] + " 4\n"
    "186 or 1 " + encoder->nids_exec[0][0] + " " + encoder->nids_exec[0][2] + "\n"
    "187 or 1 " + encoder->nids_exec[0][4] + " 186\n"
    "188 or 1 " + encoder->nids_block[1][0] + " 187\n"
    "189 ite 1 " + encoder->nids_check[1] + " 4 188\n"
    "190 next 1 " + encoder->nids_block[1][0] + " 189 block_1_0\n"
    "\n"
    "191 init 1 " + encoder->nids_block[1][1] + " 4\n"
    "192 or 1 " + encoder->nids_exec[1][0] + " " + encoder->nids_exec[1][2] + "\n"
    "193 or 1 " + encoder->nids_exec[1][4] + " 192\n"
    "194 or 1 " + encoder->nids_block[1][1] + " 193\n"
    "195 ite 1 " + encoder->nids_check[1] + " 4 194\n"
    "196 next 1 " + encoder->nids_block[1][1] + " 195 block_1_1\n"
    "\n"
    "197 init 1 " + encoder->nids_block[1][2] + " 4\n"
    "198 or 1 " + encoder->nids_exec[2][0] + " " + encoder->nids_exec[2][2] + "\n"
    "199 or 1 " + encoder->nids_exec[2][4] + " 198\n"
    "200 or 1 " + encoder->nids_block[1][2] + " 199\n"
    "201 ite 1 " + encoder->nids_check[1] + " 4 200\n"
    "202 next 1 " + encoder->nids_block[1][2] + " 201 block_1_2\n"
    "\n"
    "203 init 1 " + encoder->nids_block[2][0] + " 4\n"
    "204 or 1 " + encoder->nids_exec[0][1] + " " + encoder->nids_exec[0][3] + "\n"
    "205 or 1 " + encoder->nids_exec[0][5] + " 204\n"
    "206 or 1 " + encoder->nids_block[2][0] + " 205\n"
    "207 ite 1 " + encoder->nids_check[2] + " 4 206\n"
    "208 next 1 " + encoder->nids_block[2][0] + " 207 block_2_0\n"
    "\n"
    "209 init 1 " + encoder->nids_block[2][1] + " 4\n"
    "210 or 1 " + encoder->nids_exec[1][1] + " " + encoder->nids_exec[1][3] + "\n"
    "211 or 1 " + encoder->nids_exec[1][5] + " 210\n"
    "212 or 1 " + encoder->nids_block[2][1] + " 211\n"
    "213 ite 1 " + encoder->nids_check[2] + " 4 212\n"
    "214 next 1 " + encoder->nids_block[2][1] + " 213 block_2_1\n"
    "\n"
    "215 init 1 " + encoder->nids_block[2][2] + " 4\n"
    "216 or 1 " + encoder->nids_exec[2][1] + " " + encoder->nids_exec[2][3] + "\n"
    "217 or 1 " + encoder->nids_exec[2][5] + " 216\n"
    "218 or 1 " + encoder->nids_block[2][2] + " 217\n"
    "219 ite 1 " + encoder->nids_check[2] + " 4 218\n"
    "220 next 1 " + encoder->nids_block[2][2] + " 219 block_2_2\n"
    "\n"
    "221 init 1 " + encoder->nids_block[3][0] + " 4\n"
    "222 or 1 " + encoder->nids_exec[0][6] + " " + encoder->nids_block[3][0] + "\n"
    "223 ite 1 " + encoder->nids_check[3] + " 4 222\n"
    "224 next 1 " + encoder->nids_block[3][0] + " 223 block_3_0\n"
    "\n"
    "225 init 1 " + encoder->nids_block[3][1] + " 4\n"
    "226 or 1 " + encoder->nids_exec[1][6] + " " + encoder->nids_block[3][1] + "\n"
    "227 ite 1 " + encoder->nids_check[3] + " 4 226\n"
    "228 next 1 " + encoder->nids_block[3][1] + " 227 block_3_1\n"
    "\n"
    "; prevent scheduling of blocked threads\n"
    "229 and 1 " + encoder->nids_block[1][0] + " -" + encoder->nids_check[1] + "\n"
    "230 implies 1 229 -" + encoder->nids_thread[0] + "\n"
    "231 constraint 230 block_1_0\n"
    "\n"
    "232 and 1 " + encoder->nids_block[1][1] + " -" + encoder->nids_check[1] + "\n"
    "233 implies 1 232 -" + encoder->nids_thread[1] + "\n"
    "234 constraint 233 block_1_1\n"
    "\n"
    "235 and 1 " + encoder->nids_block[1][2] + " -" + encoder->nids_check[1] + "\n"
    "236 implies 1 235 -" + encoder->nids_thread[2] + "\n"
    "237 constraint 236 block_1_2\n"
    "\n"
    "238 and 1 " + encoder->nids_block[2][0] + " -" + encoder->nids_check[2] + "\n"
    "239 implies 1 238 -" + encoder->nids_thread[0] + "\n"
    "240 constraint 239 block_2_0\n"
    "\n"
    "241 and 1 " + encoder->nids_block[2][1] + " -" + encoder->nids_check[2] + "\n"
    "242 implies 1 241 -" + encoder->nids_thread[1] + "\n"
    "243 constraint 242 block_2_1\n"
    "\n"
    "244 and 1 " + encoder->nids_block[2][2] + " -" + encoder->nids_check[2] + "\n"
    "245 implies 1 244 -" + encoder->nids_thread[2] + "\n"
    "246 constraint 245 block_2_2\n"
    "\n"
    "247 and 1 " + encoder->nids_block[3][0] + " -" + encoder->nids_check[3] + "\n"
    "248 implies 1 247 -" + encoder->nids_thread[0] + "\n"
    "249 constraint 248 block_3_0\n"
    "\n"
    "250 and 1 " + encoder->nids_block[3][1] + " -" + encoder->nids_check[3] + "\n"
    "251 implies 1 250 -" + encoder->nids_thread[1] + "\n"
    "252 constraint 251 block_3_1\n"
    "\n",
    encoder->str());

  /* verbosity */
  reset_encoder();

  init_checkpoint_constraints(true);

  verbose = false;
  encoder->add_checkpoint_constraints();
  verbose = true;

  ASSERT_EQ(
    "172 state 1 block_1_0\n"
    "173 state 1 block_1_1\n"
    "174 state 1 block_1_2\n"
    "\n"
    "175 state 1 block_2_0\n"
    "176 state 1 block_2_1\n"
    "177 state 1 block_2_2\n"
    "\n"
    "178 state 1 block_3_0\n"
    "179 state 1 block_3_1\n"
    "\n"
    "180 and 1 " + encoder->nids_block[1][0] + " " + encoder->nids_block[1][1] + "\n"
    "181 and 1 " + encoder->nids_block[1][2] + " 180 check_1\n"
    "182 and 1 " + encoder->nids_block[2][0] + " " + encoder->nids_block[2][1] + "\n"
    "183 and 1 " + encoder->nids_block[2][2] + " 182 check_2\n"
    "184 and 1 " + encoder->nids_block[3][0] + " " + encoder->nids_block[3][1] + " check_3\n"
    "\n"
    "185 init 1 " + encoder->nids_block[1][0] + " 4\n"
    "186 or 1 " + encoder->nids_exec[0][0] + " " + encoder->nids_exec[0][2] + "\n"
    "187 or 1 " + encoder->nids_exec[0][4] + " 186\n"
    "188 or 1 " + encoder->nids_block[1][0] + " 187\n"
    "189 ite 1 " + encoder->nids_check[1] + " 4 188\n"
    "190 next 1 " + encoder->nids_block[1][0] + " 189 block_1_0\n"
    "\n"
    "191 init 1 " + encoder->nids_block[1][1] + " 4\n"
    "192 or 1 " + encoder->nids_exec[1][0] + " " + encoder->nids_exec[1][2] + "\n"
    "193 or 1 " + encoder->nids_exec[1][4] + " 192\n"
    "194 or 1 " + encoder->nids_block[1][1] + " 193\n"
    "195 ite 1 " + encoder->nids_check[1] + " 4 194\n"
    "196 next 1 " + encoder->nids_block[1][1] + " 195 block_1_1\n"
    "\n"
    "197 init 1 " + encoder->nids_block[1][2] + " 4\n"
    "198 or 1 " + encoder->nids_exec[2][0] + " " + encoder->nids_exec[2][2] + "\n"
    "199 or 1 " + encoder->nids_exec[2][4] + " 198\n"
    "200 or 1 " + encoder->nids_block[1][2] + " 199\n"
    "201 ite 1 " + encoder->nids_check[1] + " 4 200\n"
    "202 next 1 " + encoder->nids_block[1][2] + " 201 block_1_2\n"
    "\n"
    "203 init 1 " + encoder->nids_block[2][0] + " 4\n"
    "204 or 1 " + encoder->nids_exec[0][1] + " " + encoder->nids_exec[0][3] + "\n"
    "205 or 1 " + encoder->nids_exec[0][5] + " 204\n"
    "206 or 1 " + encoder->nids_block[2][0] + " 205\n"
    "207 ite 1 " + encoder->nids_check[2] + " 4 206\n"
    "208 next 1 " + encoder->nids_block[2][0] + " 207 block_2_0\n"
    "\n"
    "209 init 1 " + encoder->nids_block[2][1] + " 4\n"
    "210 or 1 " + encoder->nids_exec[1][1] + " " + encoder->nids_exec[1][3] + "\n"
    "211 or 1 " + encoder->nids_exec[1][5] + " 210\n"
    "212 or 1 " + encoder->nids_block[2][1] + " 211\n"
    "213 ite 1 " + encoder->nids_check[2] + " 4 212\n"
    "214 next 1 " + encoder->nids_block[2][1] + " 213 block_2_1\n"
    "\n"
    "215 init 1 " + encoder->nids_block[2][2] + " 4\n"
    "216 or 1 " + encoder->nids_exec[2][1] + " " + encoder->nids_exec[2][3] + "\n"
    "217 or 1 " + encoder->nids_exec[2][5] + " 216\n"
    "218 or 1 " + encoder->nids_block[2][2] + " 217\n"
    "219 ite 1 " + encoder->nids_check[2] + " 4 218\n"
    "220 next 1 " + encoder->nids_block[2][2] + " 219 block_2_2\n"
    "\n"
    "221 init 1 " + encoder->nids_block[3][0] + " 4\n"
    "222 or 1 " + encoder->nids_exec[0][6] + " " + encoder->nids_block[3][0] + "\n"
    "223 ite 1 " + encoder->nids_check[3] + " 4 222\n"
    "224 next 1 " + encoder->nids_block[3][0] + " 223 block_3_0\n"
    "\n"
    "225 init 1 " + encoder->nids_block[3][1] + " 4\n"
    "226 or 1 " + encoder->nids_exec[1][6] + " " + encoder->nids_block[3][1] + "\n"
    "227 ite 1 " + encoder->nids_check[3] + " 4 226\n"
    "228 next 1 " + encoder->nids_block[3][1] + " 227 block_3_1\n"
    "\n"
    "229 and 1 " + encoder->nids_block[1][0] + " -" + encoder->nids_check[1] + "\n"
    "230 implies 1 229 -" + encoder->nids_thread[0] + "\n"
    "231 constraint 230 block_1_0\n"
    "\n"
    "232 and 1 " + encoder->nids_block[1][1] + " -" + encoder->nids_check[1] + "\n"
    "233 implies 1 232 -" + encoder->nids_thread[1] + "\n"
    "234 constraint 233 block_1_1\n"
    "\n"
    "235 and 1 " + encoder->nids_block[1][2] + " -" + encoder->nids_check[1] + "\n"
    "236 implies 1 235 -" + encoder->nids_thread[2] + "\n"
    "237 constraint 236 block_1_2\n"
    "\n"
    "238 and 1 " + encoder->nids_block[2][0] + " -" + encoder->nids_check[2] + "\n"
    "239 implies 1 238 -" + encoder->nids_thread[0] + "\n"
    "240 constraint 239 block_2_0\n"
    "\n"
    "241 and 1 " + encoder->nids_block[2][1] + " -" + encoder->nids_check[2] + "\n"
    "242 implies 1 241 -" + encoder->nids_thread[1] + "\n"
    "243 constraint 242 block_2_1\n"
    "\n"
    "244 and 1 " + encoder->nids_block[2][2] + " -" + encoder->nids_check[2] + "\n"
    "245 implies 1 244 -" + encoder->nids_thread[2] + "\n"
    "246 constraint 245 block_2_2\n"
    "\n"
    "247 and 1 " + encoder->nids_block[3][0] + " -" + encoder->nids_check[3] + "\n"
    "248 implies 1 247 -" + encoder->nids_thread[0] + "\n"
    "249 constraint 248 block_3_0\n"
    "\n"
    "250 and 1 " + encoder->nids_block[3][1] + " -" + encoder->nids_check[3] + "\n"
    "251 implies 1 250 -" + encoder->nids_thread[1] + "\n"
    "252 constraint 251 block_3_1\n"
    "\n",
    encoder->str());
}

TEST_F(Btor2_Encoder_Test, add_checkpoint_constraints_single_thread)
{
  programs.push_back(create_program("CHECK 1\n"));
  reset_encoder();

  init_checkpoint_constraints(true);

  encoder->add_checkpoint_constraints();

  // TODO: ignore single-threaded checkpoints -> see gitlab issue #65
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; checkpoint constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread blocking flags - block_<id>_<thread>\n"
    "; checkpoint flags - check_<id>\n"
    "\n"
    "; thread blocking flag definitions\n"
    "; prevent scheduling of blocked threads\n",
    encoder->str());
}

TEST_F(Btor2_Encoder_Test, add_checkpoint_constraints_no_check)
{
  add_dummy_programs(3, 3);
  reset_encoder();

  init_checkpoint_constraints(true);

  encoder->add_checkpoint_constraints();

  ASSERT_EQ("", encoder->str());
}

// void Btor2_Encoder::add_bound ()
TEST_F(Btor2_Encoder_Test, add_bound)
{
  init_machine_state_declarations(true);

  encoder->add_bound();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; bound\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; step counter\n"
    "8 state 2 k\n"
    "9 init 2 8 " + encoder->nids_const[0] + "\n"
    "10 add 2 " + encoder->nids_const[1] + " 8\n"
    "11 next 2 8 10\n"
    "\n"
    "; bound (1)\n"
    "12 eq 1 " + encoder->nids_const[encoder->bound] + " 8\n"
    "13 bad 12\n",
    encoder->str());

  /* verbosity */
  reset_encoder(1);

  init_machine_state_declarations(true);

  verbose = false;
  encoder->add_bound();
  verbose = true;

  ASSERT_EQ(
    "8 state 2 k\n"
    "9 init 2 8 " + encoder->nids_const[0] + "\n"
    "10 add 2 " + encoder->nids_const[1] + " 8\n"
    "11 next 2 8 10\n"
    "\n"
    "12 eq 1 " + encoder->nids_const[encoder->bound] + " 8\n"
    "13 bad 12\n",
    encoder->str());
}

// std::string Btor2_Encoder::load(Load & l)
TEST_F(Btor2_Encoder_Test, load)
{
  add_dummy_programs(1);
  reset_encoder();

  init_register_definitions(true);

  Load l(1);

  encoder->load(l);
  ASSERT_EQ(
    encoder->nids_load[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n",
    encoder->str());

  /* another load from the same memory address */
  encoder->formula.str("");

  encoder->load(l);
  ASSERT_EQ("", encoder->str());
}

TEST_F(Btor2_Encoder_Test, load_indirect)
{
  add_dummy_programs(1);
  reset_encoder();

  init_register_definitions(true);

  Load l(1, true);

  encoder->load(l);
  ASSERT_EQ(
    encoder->nids_load[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n" +
    encoder->nids_load_indirect[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_load[1] + "\n",
    encoder->str());

  /* another load from the same memory address */
  encoder->formula.str("");

  encoder->load(l);
  ASSERT_EQ("", encoder->str());
}

// std::string Btor2_Encoder::store(Store & s)
TEST_F(Btor2_Encoder_Test, store)
{
  add_dummy_programs(2);
  reset_encoder();

  init_register_definitions(true);

  Store s(1);

  encoder->thread = 0;
  encoder->store(s);
  ASSERT_EQ(
    encoder->nids_store[0][1] + " write 3 " + encoder->nid_heap + " " + encoder->nids_const[1] + " " + encoder->nids_accu[0] + "\n",
    encoder->str());

  encoder->formula.str("");

  encoder->thread = 1;
  encoder->store(s);
  ASSERT_EQ(
    encoder->nids_store[1][1] + " write 3 " + encoder->nid_heap + " " + encoder->nids_const[1] + " " + encoder->nids_accu[1] + "\n",
    encoder->str());

  /* another store to the same memory address */
  encoder->formula.str("");

  encoder->thread = 0;
  encoder->store(s);
  ASSERT_EQ("", encoder->str());

  encoder->thread = 1;
  encoder->store(s);
  ASSERT_EQ("", encoder->str());
}

TEST_F(Btor2_Encoder_Test, store_indirect)
{
  add_dummy_programs(2);
  reset_encoder();

  init_register_definitions(true);

  Store s(1, true);

  encoder->thread = 0;
  encoder->store(s);
  ASSERT_EQ(
    encoder->nids_load[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n" +
    encoder->nids_store_indirect[0][1] + " write 3 " + encoder->nid_heap + " " + encoder->nids_load[1] + " " + encoder->nids_accu[0] + "\n",
    encoder->str());

  encoder->formula.str("");

  encoder->thread = 1;
  encoder->store(s);
  ASSERT_EQ(
    encoder->nids_store_indirect[1][1] + " write 3 " + encoder->nid_heap + " " + encoder->nids_load[1] + " " + encoder->nids_accu[1] + "\n",
    encoder->str());

  /* another store to the same memory address */
  encoder->formula.str("");

  encoder->thread = 0;
  encoder->store(s);
  ASSERT_EQ("", encoder->str());

  encoder->thread = 1;
  encoder->store(s);
  ASSERT_EQ("", encoder->str());
}

// virtual void Btor2_Encoder::encode ()
TEST_F(Btor2_Encoder_Test, encode_check)
{
  /* concurrent increment using CHECK */
  encode(
    {"increment.check.thread.0.asm", "increment.check.thread.n.asm"},
    "increment.check.t2.k16.btor2",
    16);
}

TEST_F(Btor2_Encoder_Test, encode_cas)
{
  /* concurrent increment using CAS */
  encode(
    {"increment.cas.asm", "increment.cas.asm"},
    "increment.cas.t2.k16.btor2",
    16);
}

// virtual std::string Btor2_Encoder::encode (Load & l)
TEST_F(Btor2_Encoder_Test, LOAD)
{
  Btor2_Encoder_Test_load_Test();
}

TEST_F(Btor2_Encoder_Test, LOAD_indirect)
{
  Btor2_Encoder_Test_load_indirect_Test();
}

// virtual std::string Btor2_Encoder::encode (Store & s)
TEST_F(Btor2_Encoder_Test, STORE)
{
  Btor2_Encoder_Test_store_Test();
}

TEST_F(Btor2_Encoder_Test, STORE_indirect)
{
  Btor2_Encoder_Test_store_indirect_Test();
}

// virtual std::string Btor2_Encoder::encode (Add & a)
TEST_F(Btor2_Encoder_Test, ADD)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Add a(1);

  encoder->thread = 0;
  nid = encoder->encode(a);
  ASSERT_EQ(
    encoder->nids_load[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n"
    + nid + " add 2 " + encoder->nids_accu[0] + " " + encoder->nids_load[1] + "\n",
    encoder->str());

  /* another ADD from a different thread, but same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(a);
  ASSERT_EQ(
    nid + " add 2 " + encoder->nids_accu[1] + " " + encoder->nids_load[1] + "\n",
    encoder->str());
}

TEST_F(Btor2_Encoder_Test, ADD_indirect)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Add a(1, true);

  encoder->thread = 0;
  nid = encoder->encode(a);
  ASSERT_EQ(
    encoder->nids_load[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n"
    + encoder->nids_load_indirect[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_load[1] + "\n"
    + nid + " add 2 " + encoder->nids_accu[0] + " " + encoder->nids_load_indirect[1] + "\n",
    encoder->str());

  /* another ADD from a different thread, but same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(a);
  ASSERT_EQ(
    nid + " add 2 " + encoder->nids_accu[1] + " " + encoder->nids_load_indirect[1] + "\n",
    encoder->str());
}

// virtual std::string Btor2_Encoder::encode (Addi & a)
TEST_F(Btor2_Encoder_Test, ADDI)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Addi a(1);

  encoder->thread = 0;
  nid = encoder->encode(a);
  ASSERT_EQ(
    nid + " add 2 " + encoder->nids_accu[0] + " " + encoder->nids_const[1] + "\n",
    encoder->str());

  /* another ADDI from a different thread */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(a);
  ASSERT_EQ(
    nid + " add 2 " + encoder->nids_accu[1] + " " + encoder->nids_const[1] + "\n",
    encoder->str());
}

// virtual std::string Btor2_Encoder::encode (Sub & s)
TEST_F(Btor2_Encoder_Test, SUB)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Sub s(1);

  encoder->thread = 0;
  nid = encoder->encode(s);
  ASSERT_EQ(
    encoder->nids_load[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n"
    + nid + " sub 2 " + encoder->nids_accu[0] + " " + encoder->nids_load[1] + "\n",
    encoder->str());

  /* another SUB from a different thread, but same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(s);
  ASSERT_EQ(
    nid + " sub 2 " + encoder->nids_accu[1] + " " + encoder->nids_load[1] + "\n",
    encoder->str());
}

TEST_F(Btor2_Encoder_Test, SUB_indirect)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Sub s(1, true);

  encoder->thread = 0;
  nid = encoder->encode(s);
  ASSERT_EQ(
    encoder->nids_load[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n"
    + encoder->nids_load_indirect[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_load[1] + "\n"
    + nid + " sub 2 " + encoder->nids_accu[0] + " " + encoder->nids_load_indirect[1] + "\n",
    encoder->str());

  /* another SUB from a different thread, but same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(s);
  ASSERT_EQ(
    nid + " sub 2 " + encoder->nids_accu[1] + " " + encoder->nids_load_indirect[1] + "\n",
    encoder->str());
}

// virtual std::string Btor2_Encoder::encode (Subi & s)
TEST_F(Btor2_Encoder_Test, SUBI)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Subi s(1);

  encoder->thread = 0;
  nid = encoder->encode(s);
  ASSERT_EQ(
    nid + " sub 2 " + encoder->nids_accu[0] + " " + encoder->nids_const[1] + "\n",
    encoder->str());

  /* another SUBI from a different thread */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(s);
  ASSERT_EQ(
    nid + " sub 2 " + encoder->nids_accu[1] + " " + encoder->nids_const[1] + "\n",
    encoder->str());
}

// virtual std::string Btor2_Encoder::encode (Cmp & c)
TEST_F(Btor2_Encoder_Test, CMP)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Cmp c(1);

  encoder->thread = 0;
  nid = encoder->encode(c);
  ASSERT_EQ(
    encoder->nids_load[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n"
    + nid + " sub 2 " + encoder->nids_accu[0] + " " + encoder->nids_load[1] + "\n",
    encoder->str());

  /* another CMP from a different thread, but same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(c);
  ASSERT_EQ(
    nid + " sub 2 " + encoder->nids_accu[1] + " " + encoder->nids_load[1] + "\n",
    encoder->str());
}

TEST_F(Btor2_Encoder_Test, CMP_indirect)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Cmp c(1, true);

  encoder->thread = 0;
  nid = encoder->encode(c);
  ASSERT_EQ(
    encoder->nids_load[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n"
    + encoder->nids_load_indirect[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_load[1] + "\n"
    + nid + " sub 2 " + encoder->nids_accu[0] + " " + encoder->nids_load_indirect[1] + "\n",
    encoder->str());

  /* another CMP from a different thread, but same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(c);
  ASSERT_EQ(
    nid + " sub 2 " + encoder->nids_accu[1] + " " + encoder->nids_load_indirect[1] + "\n",
    encoder->str());
}

// virtual std::string Btor2_Encoder::encode (Jmp & j)
TEST_F(Btor2_Encoder_Test, JMP)
{
  Jmp j(1);

  ASSERT_EQ("", encoder->encode(j));
  ASSERT_EQ("", encoder->str());
}

// virtual std::string Btor2_Encoder::encode (Jz & j)
TEST_F(Btor2_Encoder_Test, JZ)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Jz j(1);

  encoder->thread = 0;
  nid = encoder->encode(j);
  ASSERT_EQ(
    nid + " eq 1 " + encoder->nids_accu[0] + " " + encoder->nids_const[0] + "\n",
    encoder->str());

  /* another JZ from a different thread */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(j);
  ASSERT_EQ(
    nid + " eq 1 " + encoder->nids_accu[1] + " " + encoder->nids_const[0] + "\n",
    encoder->str());
}

// virtual std::string Btor2_Encoder::encode (Jnz & j)
TEST_F(Btor2_Encoder_Test, JNZ)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Jnz j(1);

  encoder->thread = 0;
  nid = encoder->encode(j);
  ASSERT_EQ(
    nid + " ne 1 " + encoder->nids_accu[0] + " " + encoder->nids_const[0] + "\n",
    encoder->str());

  /* another JNZ from a different thread */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(j);
  ASSERT_EQ(
    nid + " ne 1 " + encoder->nids_accu[1] + " " + encoder->nids_const[0] + "\n",
    encoder->str());
}

// virtual std::string Btor2_Encoder::encode (Js & j)
TEST_F(Btor2_Encoder_Test, JS)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Js j(1);

  encoder->thread = 0;
  nid = encoder->encode(j);
  ASSERT_EQ(
    nid + " slice 1 " + encoder->nids_accu[0] + " " + encoder->msb + " " + encoder->msb + "\n",
    encoder->str());

  /* another JS from a different thread */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(j);
  ASSERT_EQ(
    nid + " slice 1 " + encoder->nids_accu[1] + " " + encoder->msb + " " + encoder->msb + "\n",
    encoder->str());
}

// virtual std::string Btor2_Encoder::encode (Jns & j)
TEST_F(Btor2_Encoder_Test, JNS)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Jns j(1);

  encoder->thread = 0;
  nid = encoder->encode(j);
  ASSERT_EQ(
    encoder->nid(-2) + " slice 1 " + encoder->nids_accu[0] + " " + encoder->msb + " " + encoder->msb + "\n"
    + nid + " not 1 " + encoder->nid(-2) + "\n",
    encoder->str());

  /* another JNS from a different thread */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(j);
  ASSERT_EQ(
    encoder->nid(-2) + " slice 1 " + encoder->nids_accu[1] + " " + encoder->msb + " " + encoder->msb + "\n"
    + nid + " not 1 " + encoder->nid(-2) + "\n",
    encoder->str());
}

// virtual std::string Btor2_Encoder::encode (Jnzns & j)
TEST_F(Btor2_Encoder_Test, JNZNS)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Jnzns j(1);

  encoder->thread = 0;
  nid = encoder->encode(j);
  ASSERT_EQ(
    encoder->nid(-4) + " ne 1 " + encoder->nids_accu[0] + " " + encoder->nids_const[0] + "\n"
    + encoder->nid(-3) + " slice 1 " + encoder->nids_accu[0] + " " + encoder->msb + " " + encoder->msb + "\n"
    + encoder->nid(-2) + " not 1 " + encoder->nid(-3) + "\n"
    + nid + " and 1 " + encoder->nid(-4) + " " + encoder->nid(-2) + "\n",
    encoder->str());

  /* another JNZNS from a different thread */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(j);
  ASSERT_EQ(
    encoder->nid(-4) + " ne 1 " + encoder->nids_accu[1] + " " + encoder->nids_const[0] + "\n"
    + encoder->nid(-3) + " slice 1 " + encoder->nids_accu[1] + " " + encoder->msb + " " + encoder->msb + "\n"
    + encoder->nid(-2) + " not 1 " + encoder->nid(-3) + "\n"
    + nid + " and 1 " + encoder->nid(-4) + " " + encoder->nid(-2) + "\n",
    encoder->str());
}

// virtual std::string Btor2_Encoder::encode (Mem & m)
TEST_F(Btor2_Encoder_Test, MEM)
{
  Btor2_Encoder_Test_LOAD_Test();
}

TEST_F(Btor2_Encoder_Test, MEM_indirect)
{
  Btor2_Encoder_Test_LOAD_indirect_Test();
}

// virtual std::string Btor2_Encoder::encode (Cas & c)
TEST_F(Btor2_Encoder_Test, CAS_accu)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Cas c(1);

  encoder->update_accu = true;

  encoder->thread = 0;
  nid = encoder->encode(c);
  ASSERT_EQ(
    encoder->nids_load[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n"
    + encoder->nid(-2) + " eq 1 " + encoder->nids_mem[0] + " " + encoder->nids_load[1] + "\n"
    + nid + " ite 2 " + encoder->nid(-2) + " " + encoder->nids_const[1] + " " + encoder->nids_const[0] + "\n",
    encoder->str());

  /* another CAS from a different thread, but same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(c);
  ASSERT_EQ(
    encoder->nid(-2) + " eq 1 " + encoder->nids_mem[1] + " " + encoder->nids_load[1] + "\n"
    + nid + " ite 2 " + encoder->nid(-2) + " " + encoder->nids_const[1] + " " + encoder->nids_const[0] + "\n",
    encoder->str());
}

TEST_F(Btor2_Encoder_Test, CAS_accu_indirect)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Cas c(1, true);

  encoder->update_accu = true;

  encoder->thread = 0;
  nid = encoder->encode(c);
  ASSERT_EQ(
    encoder->nids_load[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n"
    + encoder->nids_load_indirect[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_load[1] + "\n"
    + encoder->nid(-2) + " eq 1 " + encoder->nids_mem[0] + " " + encoder->nids_load_indirect[1] + "\n"
    + nid + " ite 2 " + encoder->nid(-2) + " " + encoder->nids_const[1] + " " + encoder->nids_const[0] + "\n",
    encoder->str());

  /* another CAS from a different thread, but same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(c);
  ASSERT_EQ(
    encoder->nid(-2) + " eq 1 " + encoder->nids_mem[1] + " " + encoder->nids_load_indirect[1] + "\n"
    + nid + " ite 2 " + encoder->nid(-2) + " " + encoder->nids_const[1] + " " + encoder->nids_const[0] + "\n",
    encoder->str());
}

TEST_F(Btor2_Encoder_Test, CAS_heap)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Cas c(1);

  encoder->update_accu = false;

  encoder->thread = 0;
  nid = encoder->encode(c);
  ASSERT_EQ(
    encoder->nids_load[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n"
    + encoder->nid(-3) + " eq 1 " + encoder->nids_mem[0] + " " + encoder->nids_load[1] + "\n"
    + encoder->nid(-2) + " write 3 " + encoder->nid_heap + " " + encoder->nids_const[1] + " " + encoder->nids_accu[0] + "\n"
    + nid + " ite 3 " + encoder->nid(-3) + " " + encoder->nid(-2) + " " + encoder->nid_heap + "\n",
    encoder->str());

  /* another CAS from a different thread, but same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(c);
  ASSERT_EQ(
    encoder->nid(-3) + " eq 1 " + encoder->nids_mem[1] + " " + encoder->nids_load[1] + "\n"
    + encoder->nid(-2) + " write 3 " + encoder->nid_heap + " " + encoder->nids_const[1] + " " + encoder->nids_accu[1] + "\n"
    + nid + " ite 3 " + encoder->nid(-3) + " " + encoder->nid(-2) + " " + encoder->nid_heap + "\n",
    encoder->str());
}

TEST_F(Btor2_Encoder_Test, CAS_heap_indirect)
{
  add_dummy_programs(2);

  init_register_definitions(true);

  Cas c(1, true);

  encoder->update_accu = false;

  encoder->thread = 0;
  nid = encoder->encode(c);
  ASSERT_EQ(
    encoder->nids_load[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n"
    + encoder->nids_load_indirect[1] + " read 2 " + encoder->nid_heap + " " + encoder->nids_load[1] + "\n"
    + encoder->nid(-3) + " eq 1 " + encoder->nids_mem[0] + " " + encoder->nids_load_indirect[1] + "\n"
    + encoder->nid(-2) + " write 3 " + encoder->nid_heap + " " + encoder->nids_load[1] + " " + encoder->nids_accu[0] + "\n"
    + nid + " ite 3 " + encoder->nid(-3) + " " + encoder->nid(-2) + " " + encoder->nid_heap + "\n",
    encoder->str());

  /* another CAS from a different thread, but same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  nid = encoder->encode(c);
  ASSERT_EQ(
    encoder->nid(-3) + " eq 1 " + encoder->nids_mem[1] + " " + encoder->nids_load_indirect[1] + "\n"
    + encoder->nid(-2) + " write 3 " + encoder->nid_heap + " " + encoder->nids_load[1] + " " + encoder->nids_accu[1] + "\n"
    + nid + " ite 3 " + encoder->nid(-3) + " " + encoder->nid(-2) + " " + encoder->nid_heap + "\n",
    encoder->str());
}

// virtual std::string Btor2_Encoder::encode (Check & c)
TEST_F(Btor2_Encoder_Test, CHECK)
{
  Check c(1);

  ASSERT_EQ("", encoder->encode(c));
  ASSERT_EQ("", encoder->str());
}

// virtual std::string Btor2_Encoder::encode (Exit & e)
TEST_F(Btor2_Encoder_Test, EXIT)
{
  Exit e(1);

  ASSERT_EQ(encoder->nids_const[1], encoder->encode(e));
  ASSERT_EQ("", encoder->str());
}
