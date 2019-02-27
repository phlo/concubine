#include <gtest/gtest.h>

#include "encoder.hh"

using namespace std;

typedef map<word, string> NIDMap;

// TODO remove - debug only
#include "btor2.hh"
#include "btormc.hh"
void evaluate (string & formula)
{
  BtorMC btormc;
  cout << "running btormc..." << eol;
  btormc.sat(formula);
}

struct Btor2EncoderTest : public ::testing::Test
{
  string            expected;
  ProgramList       programs;
  Btor2EncoderPtr   encoder = create_encoder(1);

  Btor2EncoderPtr create_encoder (const word bound)
    {
      return make_shared<Btor2Encoder>(
        make_shared<ProgramList>(programs),
        bound,
        false);
    }

  void reset_encoder (const word bound)
    {
      encoder = create_encoder(bound);
    }

  void add_dummy_programs (unsigned num, unsigned size)
    {
      for (size_t i = 0; i < num; i++)
        {
          InstructionPtr op = Instruction::Set::create("ADDI", i + 1);
          programs.push_back(shared_ptr<Program>(new Program()));
          for (size_t j = 0; j < size; j++)
            programs[i]->add(op);
        }

      encoder = create_encoder(1);
    }

  void add_instruction_set (unsigned num)
    {
      for (size_t i = 0; i < num; i++)
        {
          programs.push_back(shared_ptr<Program>(new Program()));

          programs[i]->add(Instruction::Set::create("LOAD", 1));  // 0
          programs[i]->add(Instruction::Set::create("STORE", 1)); // 1
          programs[i]->add(Instruction::Set::create("ADD", 1));   // 2
          programs[i]->add(Instruction::Set::create("ADDI", 1));  // 3
          programs[i]->add(Instruction::Set::create("SUB", 1));   // 4
          programs[i]->add(Instruction::Set::create("SUBI", 1));  // 5
          programs[i]->add(Instruction::Set::create("CMP", 1));   // 6
          programs[i]->add(Instruction::Set::create("JMP", 1));   // 7
          programs[i]->add(Instruction::Set::create("JZ", 1));    // 8
          programs[i]->add(Instruction::Set::create("JNZ", 1));   // 9
          programs[i]->add(Instruction::Set::create("JS", 1));    // 10
          programs[i]->add(Instruction::Set::create("JNS", 1));   // 11
          programs[i]->add(Instruction::Set::create("JNZNS", 1)); // 12
          programs[i]->add(Instruction::Set::create("MEM", 1));   // 13
          programs[i]->add(Instruction::Set::create("CAS", 1));   // 14
          programs[i]->add(Instruction::Set::create("SYNC", 1));  // 15
          programs[i]->add(Instruction::Set::create("EXIT", 1));  // 16
        }

      reset_encoder(1);
    }

  void add_declerations (bool clear_formula)
    {
      encoder->declare_sorts();
      encoder->declare_constants();

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_states (bool clear_formula)
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->add_bound();
      encoder->declare_states();

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_thread_scheduling (bool clear_formula)
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->add_bound();
      encoder->declare_states();
      encoder->add_thread_scheduling();

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_synchronization_constraints (bool clear_formula)
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->add_bound();
      encoder->declare_states();
      encoder->add_thread_scheduling();
      encoder->add_synchronization_constraints();

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_statement_execution (bool clear_formula)
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->add_bound();
      encoder->declare_states();
      encoder->add_thread_scheduling();
      encoder->add_synchronization_constraints();
      encoder->add_statement_execution();

      if (clear_formula)
        encoder->formula.str("");
    }

  void init_statement_activation (bool clear_formula)
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->add_bound();
      encoder->declare_states();
      encoder->add_thread_scheduling();
      encoder->add_synchronization_constraints();
      encoder->add_statement_execution();
      encoder->add_statement_activation();

      if (clear_formula)
        encoder->formula.str("");
    }

  string nid (int offset)
    {
      int nid = encoder->node;
      return to_string(nid + offset);
    }
};

// Btor2Encoder::Btor2Encoder (const ProgramListPtr, unsigned long, bool);
TEST_F(Btor2EncoderTest, constructor)
{
  add_dummy_programs(3, 3);

  ASSERT_EQ(
    NIDMap({{0, ""}, {1, ""}, {2, ""}, {3, ""}}),
    encoder->nids_const);
}

// void Btor2Encoder::declare_sorts ();
TEST_F(Btor2EncoderTest, declare_sorts)
{
  encoder->declare_sorts();

  ASSERT_EQ("1", encoder->sid_bool);
  ASSERT_EQ("2", encoder->sid_bv);
  ASSERT_EQ("3", encoder->sid_heap);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; sorts\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "1 sort bitvec 1\n"
    "2 sort bitvec 16\n"
    "3 sort array 2 2\n\n",
    encoder->str());

  /* verbosity */
  reset_encoder(1);

  verbose = false;
  encoder->declare_sorts();
  verbose = true;

  ASSERT_EQ(
    "1 sort bitvec 1\n"
    "2 sort bitvec 16\n"
    "3 sort array 2 2\n\n",
    encoder->str());
}

// void Btor2Encoder::declare_constants ();
TEST_F(Btor2EncoderTest, declare_constants)
{
  for (size_t t = 0; t < 3; t++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      for (size_t pc = 0; pc < 3; pc++)
        programs.back()->add(
          Instruction::Set::create("ADDI", t + pc + 1));
    }

  reset_encoder(1);

  encoder->declare_sorts();
  encoder->declare_constants();

  ASSERT_EQ("4", encoder->nid_false);
  ASSERT_EQ("5", encoder->nid_true);
  ASSERT_EQ(
    NIDMap({{0, "6"}, {1, "7"}, {2, "8"}, {3, "9"}, {4, "10"}, {5, "11"}}),
    encoder->nids_const);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; sorts\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "1 sort bitvec 1\n"
    "2 sort bitvec 16\n"
    "3 sort array 2 2\n"
    "\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; constants\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "4 zero 1\n"
    "5 one 1\n"
    "6 zero 2\n"
    "7 one 2\n"
    "8 constd 2 2\n"
    "9 constd 2 3\n"
    "10 constd 2 4\n"
    "11 constd 2 5\n\n",
    encoder->str());

  /* verbosity */
  reset_encoder(1);

  verbose = false;
  encoder->declare_sorts();
  encoder->declare_constants();
  verbose = true;

  ASSERT_EQ(
    "1 sort bitvec 1\n"
    "2 sort bitvec 16\n"
    "3 sort array 2 2\n"
    "\n"
    "4 zero 1\n"
    "5 one 1\n"
    "6 zero 2\n"
    "7 one 2\n"
    "8 constd 2 2\n"
    "9 constd 2 3\n"
    "10 constd 2 4\n"
    "11 constd 2 5\n\n",
    encoder->str());
}

// void add_bound ();
TEST_F(Btor2EncoderTest, add_bound)
{
  add_declerations(true);

  encoder->add_bound();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; bound\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; step counter\n"
    "8 state 2 k\n"
    "9 init 2 8 6\n"
    "10 add 2 7 8\n"
    "11 next 2 8 10\n"
    "\n"
    "; bound (1)\n"
    "12 eq 1 7 8\n"
    "13 bad 12\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  add_declerations(true);

  verbose = false;
  encoder->add_bound();
  verbose = true;

  ASSERT_EQ(
    "8 state 2 k\n"
    "9 init 2 8 6\n"
    "10 add 2 7 8\n"
    "11 next 2 8 10\n"
    "\n"
    "12 eq 1 7 8\n"
    "13 bad 12\n\n",
    encoder->formula.str());
}

// void declare_states ();
TEST_F(Btor2EncoderTest, declare_states)
{
  add_dummy_programs(3, 3);

  add_declerations(true);

  encoder->declare_states();

  ASSERT_EQ("10", encoder->nid_heap);
  ASSERT_EQ(NIDMap({{1, "11"}, {2, "13"}, {3, "15"}}), encoder->nids_accu);
  ASSERT_EQ(NIDMap({{1, "17"}, {2, "19"}, {3, "21"}}), encoder->nids_mem);
  ASSERT_EQ(vector<string>({"23", "25", "27"}), encoder->nids_stmt[1]);
  ASSERT_EQ(vector<string>({"29", "31", "33"}), encoder->nids_stmt[2]);
  ASSERT_EQ(vector<string>({"35", "37", "39"}), encoder->nids_stmt[3]);
  ASSERT_EQ("41", encoder->nid_exit);
  ASSERT_EQ("43", encoder->nid_exit_code);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; states\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; heap\n"
    "10 state 3 heap\n"
    "\n"
    "; accumulator\n"
    "11 state 2 accu_1\n"
    "12 init 2 11 6\n"
    "13 state 2 accu_2\n"
    "14 init 2 13 6\n"
    "15 state 2 accu_3\n"
    "16 init 2 15 6\n"
    "\n"
    "; CAS memory register\n"
    "17 state 2 mem_1\n"
    "18 init 2 17 6\n"
    "19 state 2 mem_2\n"
    "20 init 2 19 6\n"
    "21 state 2 mem_3\n"
    "22 init 2 21 6\n"
    "\n"
    "; statement activation\n"
    "23 state 1 stmt_1_0\n"
    "24 init 1 23 5\n"
    "25 state 1 stmt_1_1\n"
    "26 init 1 25 4\n"
    "27 state 1 stmt_1_2\n"
    "28 init 1 27 4\n"
    "\n"
    "29 state 1 stmt_2_0\n"
    "30 init 1 29 5\n"
    "31 state 1 stmt_2_1\n"
    "32 init 1 31 4\n"
    "33 state 1 stmt_2_2\n"
    "34 init 1 33 4\n"
    "\n"
    "35 state 1 stmt_3_0\n"
    "36 init 1 35 5\n"
    "37 state 1 stmt_3_1\n"
    "38 init 1 37 4\n"
    "39 state 1 stmt_3_2\n"
    "40 init 1 39 4\n"
    "\n"
    "; exit flag\n"
    "41 state 1 exit\n"
    "42 init 1 41 4\n"
    "\n"
    "; exit code\n"
    "43 state 2 exit_code\n"
    "44 init 2 43 6\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  add_declerations(true);

  verbose = false;
  encoder->declare_states();
  verbose = true;

  ASSERT_EQ(
    "10 state 3 heap\n"
    "\n"
    "11 state 2 accu_1\n"
    "12 init 2 11 6\n"
    "13 state 2 accu_2\n"
    "14 init 2 13 6\n"
    "15 state 2 accu_3\n"
    "16 init 2 15 6\n"
    "\n"
    "17 state 2 mem_1\n"
    "18 init 2 17 6\n"
    "19 state 2 mem_2\n"
    "20 init 2 19 6\n"
    "21 state 2 mem_3\n"
    "22 init 2 21 6\n"
    "\n"
    "23 state 1 stmt_1_0\n"
    "24 init 1 23 5\n"
    "25 state 1 stmt_1_1\n"
    "26 init 1 25 4\n"
    "27 state 1 stmt_1_2\n"
    "28 init 1 27 4\n"
    "\n"
    "29 state 1 stmt_2_0\n"
    "30 init 1 29 5\n"
    "31 state 1 stmt_2_1\n"
    "32 init 1 31 4\n"
    "33 state 1 stmt_2_2\n"
    "34 init 1 33 4\n"
    "\n"
    "35 state 1 stmt_3_0\n"
    "36 init 1 35 5\n"
    "37 state 1 stmt_3_1\n"
    "38 init 1 37 4\n"
    "39 state 1 stmt_3_2\n"
    "40 init 1 39 4\n"
    "\n"
    "41 state 1 exit\n"
    "42 init 1 41 4\n"
    "\n"
    "43 state 2 exit_code\n"
    "44 init 2 43 6\n\n",
    encoder->formula.str());
}

// void add_thread_scheduling ();
TEST_F(Btor2EncoderTest, add_thread_scheduling)
{
  add_dummy_programs(3, 3);

  init_states(true);

  encoder->add_thread_scheduling();

  ASSERT_EQ(NIDMap({{1, "51"}, {2, "52"}, {3, "53"}}), encoder->nids_thread);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; thread scheduling\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "51 input 1 thread_1\n"
    "52 input 1 thread_2\n"
    "53 input 1 thread_3\n"
    "\n"
    "; cardinality constraint\n"
    "54 or 1 51 52\n"
    "55 or 1 53 54\n"
    "56 or 1 47 55\n"
    "57 constraint 56\n"
    "58 nand 1 51 52\n"
    "59 nand 1 51 53\n"
    "60 nand 1 51 47\n"
    "61 nand 1 52 53\n"
    "62 nand 1 52 47\n"
    "63 nand 1 53 47\n"
    "64 and 1 58 59\n"
    "65 and 1 60 64\n"
    "66 and 1 61 65\n"
    "67 and 1 62 66\n"
    "68 and 1 63 67\n"
    "69 constraint 68\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  init_states(true);

  verbose = false;
  encoder->add_thread_scheduling();
  verbose = true;

  ASSERT_EQ(
    "51 input 1 thread_1\n"
    "52 input 1 thread_2\n"
    "53 input 1 thread_3\n"
    "\n"
    "54 or 1 51 52\n"
    "55 or 1 53 54\n"
    "56 or 1 47 55\n"
    "57 constraint 56\n"
    "58 nand 1 51 52\n"
    "59 nand 1 51 53\n"
    "60 nand 1 51 47\n"
    "61 nand 1 52 53\n"
    "62 nand 1 52 47\n"
    "63 nand 1 53 47\n"
    "64 and 1 58 59\n"
    "65 and 1 60 64\n"
    "66 and 1 61 65\n"
    "67 and 1 62 66\n"
    "68 and 1 63 67\n"
    "69 constraint 68\n\n",
    encoder->formula.str());
}

// void add_synchronization_constraints ();
TEST_F(Btor2EncoderTest, add_synchronization_constraints)
{
  for (size_t t = 0; t < 3; t++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      for (size_t pc = 0; pc < 2; pc++)
        programs.back()->add(Instruction::Set::create("SYNC", pc + 1));
    }

  reset_encoder(1);

  init_thread_scheduling(true);

  encoder->add_synchronization_constraints();

  ASSERT_EQ(NIDMap({{1, "67"}, {2, "79"}}), encoder->nids_sync);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; synchronization constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; negated thread activation variables\n"
    "63 not 1 44 not_thread_1\n"
    "64 not 1 45 not_thread_2\n"
    "65 not 1 46 not_thread_3\n"
    "\n"
    "; synchronization condition sync_1\n"
    "66 and 1 28 32\n"
    "67 and 1 36 66 sync_1\n"
    "68 not 1 67 not_sync_1\n"
    "\n"
    "; disable threads waiting for barrier 1\n"
    "69 and 1 28 68\n"
    "70 implies 1 69 63\n"
    "71 constraint 70 sync_1_block_1\n"
    "\n"
    "72 and 1 32 68\n"
    "73 implies 1 72 64\n"
    "74 constraint 73 sync_1_block_2\n"
    "\n"
    "75 and 1 36 68\n"
    "76 implies 1 75 65\n"
    "77 constraint 76 sync_1_block_3\n"
    "\n"
    "; synchronization condition sync_2\n"
    "78 and 1 30 34\n"
    "79 and 1 38 78 sync_2\n"
    "80 not 1 79 not_sync_2\n"
    "\n"
    "; disable threads waiting for barrier 2\n"
    "81 and 1 30 80\n"
    "82 implies 1 81 63\n"
    "83 constraint 82 sync_2_block_1\n"
    "\n"
    "84 and 1 34 80\n"
    "85 implies 1 84 64\n"
    "86 constraint 85 sync_2_block_2\n"
    "\n"
    "87 and 1 38 80\n"
    "88 implies 1 87 65\n"
    "89 constraint 88 sync_2_block_3\n\n",
    encoder->formula.str());

  /* multiple calls to the same barrier */
  for (const auto & program : programs)
    for (size_t pc = 0; pc < 4; pc++)
      program->add(Instruction::Set::create("SYNC", pc % 2 + 1));

  reset_encoder(1);

  init_thread_scheduling(true);

  encoder->add_synchronization_constraints();

  ASSERT_EQ(
    vector<string>({"28", "30", "32", "34", "36", "38"}),
    encoder->nids_stmt[1]);
  ASSERT_EQ(
    vector<string>({"40", "42", "44", "46", "48", "50"}),
    encoder->nids_stmt[2]);
  ASSERT_EQ(
    vector<string>({"52", "54", "56", "58", "60", "62"}),
    encoder->nids_stmt[3]);
  ASSERT_EQ(NIDMap({{1, "97"}, {2, "115"}}), encoder->nids_sync);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; synchronization constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; negated thread activation variables\n"
    "87 not 1 68 not_thread_1\n"
    "88 not 1 69 not_thread_2\n"
    "89 not 1 70 not_thread_3\n"
    "\n"
    "; synchronization condition sync_1\n"
    "90 or 1 28 32\n"
    "91 or 1 36 90 thread_1@sync_1\n"
    "92 or 1 40 44\n"
    "93 or 1 48 92 thread_2@sync_1\n"
    "94 or 1 52 56\n"
    "95 or 1 60 94 thread_3@sync_1\n"
    "96 and 1 91 93\n"
    "97 and 1 95 96 sync_1\n"
    "98 not 1 97 not_sync_1\n"
    "\n"
    "; disable threads waiting for barrier 1\n"
    "99 and 1 91 98\n"
    "100 implies 1 99 87\n"
    "101 constraint 100 sync_1_block_1\n"
    "\n"
    "102 and 1 93 98\n"
    "103 implies 1 102 88\n"
    "104 constraint 103 sync_1_block_2\n"
    "\n"
    "105 and 1 95 98\n"
    "106 implies 1 105 89\n"
    "107 constraint 106 sync_1_block_3\n"
    "\n"
    "; synchronization condition sync_2\n"
    "108 or 1 30 34\n"
    "109 or 1 38 108 thread_1@sync_2\n"
    "110 or 1 42 46\n"
    "111 or 1 50 110 thread_2@sync_2\n"
    "112 or 1 54 58\n"
    "113 or 1 62 112 thread_3@sync_2\n"
    "114 and 1 109 111\n"
    "115 and 1 113 114 sync_2\n"
    "116 not 1 115 not_sync_2\n"
    "\n"
    "; disable threads waiting for barrier 2\n"
    "117 and 1 109 116\n"
    "118 implies 1 117 87\n"
    "119 constraint 118 sync_2_block_1\n"
    "\n"
    "120 and 1 111 116\n"
    "121 implies 1 120 88\n"
    "122 constraint 121 sync_2_block_2\n"
    "\n"
    "123 and 1 113 116\n"
    "124 implies 1 123 89\n"
    "125 constraint 124 sync_2_block_3\n\n",
    encoder->formula.str());

  /* barrier only for a subset of threads */
  for (size_t i = 0; i < programs.size() - 1; i++)
    programs[i]->add(Instruction::Set::create("SYNC", 3));

  reset_encoder(1);

  init_thread_scheduling(true);

  encoder->add_synchronization_constraints();

  ASSERT_EQ(
    vector<string>({"29", "31", "33", "35", "37", "39", "41"}),
    encoder->nids_stmt[1]);
  ASSERT_EQ(
    vector<string>({"43", "45", "47", "49", "51", "53", "55"}),
    encoder->nids_stmt[2]);
  ASSERT_EQ(
    vector<string>({"57", "59", "61", "63", "65", "67"}),
    encoder->nids_stmt[3]);
  ASSERT_EQ(NIDMap({{1, "102"}, {2, "120"}, {3, "133"}}), encoder->nids_sync);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; synchronization constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; negated thread activation variables\n"
    "92 not 1 73 not_thread_1\n"
    "93 not 1 74 not_thread_2\n"
    "94 not 1 75 not_thread_3\n"
    "\n"
    "; synchronization condition sync_1\n"
    "95 or 1 29 33\n"
    "96 or 1 37 95 thread_1@sync_1\n"
    "97 or 1 43 47\n"
    "98 or 1 51 97 thread_2@sync_1\n"
    "99 or 1 57 61\n"
    "100 or 1 65 99 thread_3@sync_1\n"
    "101 and 1 96 98\n"
    "102 and 1 100 101 sync_1\n"
    "103 not 1 102 not_sync_1\n"
    "\n"
    "; disable threads waiting for barrier 1\n"
    "104 and 1 96 103\n"
    "105 implies 1 104 92\n"
    "106 constraint 105 sync_1_block_1\n"
    "\n"
    "107 and 1 98 103\n"
    "108 implies 1 107 93\n"
    "109 constraint 108 sync_1_block_2\n"
    "\n"
    "110 and 1 100 103\n"
    "111 implies 1 110 94\n"
    "112 constraint 111 sync_1_block_3\n"
    "\n"
    "; synchronization condition sync_2\n"
    "113 or 1 31 35\n"
    "114 or 1 39 113 thread_1@sync_2\n"
    "115 or 1 45 49\n"
    "116 or 1 53 115 thread_2@sync_2\n"
    "117 or 1 59 63\n"
    "118 or 1 67 117 thread_3@sync_2\n"
    "119 and 1 114 116\n"
    "120 and 1 118 119 sync_2\n"
    "121 not 1 120 not_sync_2\n"
    "\n"
    "; disable threads waiting for barrier 2\n"
    "122 and 1 114 121\n"
    "123 implies 1 122 92\n"
    "124 constraint 123 sync_2_block_1\n"
    "\n"
    "125 and 1 116 121\n"
    "126 implies 1 125 93\n"
    "127 constraint 126 sync_2_block_2\n"
    "\n"
    "128 and 1 118 121\n"
    "129 implies 1 128 94\n"
    "130 constraint 129 sync_2_block_3\n"
    "\n"
    "; synchronization condition sync_3\n"
    "131 or 1 73 74\n"
    "132 and 1 41 55\n"
    "133 and 1 131 132 sync_3\n"
    "134 not 1 133 not_sync_3\n"
    "\n"
    "; disable threads waiting for barrier 3\n"
    "135 and 1 41 134\n"
    "136 implies 1 135 92\n"
    "137 constraint 136 sync_3_block_1\n"
    "\n"
    "138 and 1 55 134\n"
    "139 implies 1 138 93\n"
    "140 constraint 139 sync_3_block_2\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  init_thread_scheduling(true);

  verbose = false;
  encoder->add_synchronization_constraints();
  verbose = true;

  ASSERT_EQ(
    "92 not 1 73 not_thread_1\n"
    "93 not 1 74 not_thread_2\n"
    "94 not 1 75 not_thread_3\n"
    "\n"
    "95 or 1 29 33\n"
    "96 or 1 37 95 thread_1@sync_1\n"
    "97 or 1 43 47\n"
    "98 or 1 51 97 thread_2@sync_1\n"
    "99 or 1 57 61\n"
    "100 or 1 65 99 thread_3@sync_1\n"
    "101 and 1 96 98\n"
    "102 and 1 100 101 sync_1\n"
    "103 not 1 102 not_sync_1\n"
    "\n"
    "104 and 1 96 103\n"
    "105 implies 1 104 92\n"
    "106 constraint 105 sync_1_block_1\n"
    "\n"
    "107 and 1 98 103\n"
    "108 implies 1 107 93\n"
    "109 constraint 108 sync_1_block_2\n"
    "\n"
    "110 and 1 100 103\n"
    "111 implies 1 110 94\n"
    "112 constraint 111 sync_1_block_3\n"
    "\n"
    "113 or 1 31 35\n"
    "114 or 1 39 113 thread_1@sync_2\n"
    "115 or 1 45 49\n"
    "116 or 1 53 115 thread_2@sync_2\n"
    "117 or 1 59 63\n"
    "118 or 1 67 117 thread_3@sync_2\n"
    "119 and 1 114 116\n"
    "120 and 1 118 119 sync_2\n"
    "121 not 1 120 not_sync_2\n"
    "\n"
    "122 and 1 114 121\n"
    "123 implies 1 122 92\n"
    "124 constraint 123 sync_2_block_1\n"
    "\n"
    "125 and 1 116 121\n"
    "126 implies 1 125 93\n"
    "127 constraint 126 sync_2_block_2\n"
    "\n"
    "128 and 1 118 121\n"
    "129 implies 1 128 94\n"
    "130 constraint 129 sync_2_block_3\n"
    "\n"
    "131 or 1 73 74\n"
    "132 and 1 41 55\n"
    "133 and 1 131 132 sync_3\n"
    "134 not 1 133 not_sync_3\n"
    "\n"
    "135 and 1 41 134\n"
    "136 implies 1 135 92\n"
    "137 constraint 136 sync_3_block_1\n"
    "\n"
    "138 and 1 55 134\n"
    "139 implies 1 138 93\n"
    "140 constraint 139 sync_3_block_2\n\n",
    encoder->formula.str());
}

// void add_statement_execution ();
TEST_F(Btor2EncoderTest, add_statement_execution)
{
  add_dummy_programs(3, 2);

  for (const auto & program : programs)
    program->add(Instruction::Set::create("SYNC", 1));

  reset_encoder(1);

  init_synchronization_constraints(true);

  encoder->add_statement_execution();

  ASSERT_EQ(vector<string>({"85", "86", "87"}), encoder->nids_exec[1]);
  ASSERT_EQ(vector<string>({"88", "89", "90"}), encoder->nids_exec[2]);
  ASSERT_EQ(vector<string>({"91", "92", "93"}), encoder->nids_exec[3]);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; statement execution - shorthand for statement & thread activation\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "85 and 1 29 51 exec_1_0\n"
    "86 and 1 31 51 exec_1_1\n"
    "87 and 1 33 74 exec_1_2\n"
    "\n"
    "88 and 1 35 52 exec_2_0\n"
    "89 and 1 37 52 exec_2_1\n"
    "90 and 1 39 74 exec_2_2\n"
    "\n"
    "91 and 1 41 53 exec_3_0\n"
    "92 and 1 43 53 exec_3_1\n"
    "93 and 1 45 74 exec_3_2\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  init_synchronization_constraints(true);

  verbose = false;
  encoder->add_statement_execution();
  verbose = true;

  ASSERT_EQ(
    "85 and 1 29 51 exec_1_0\n"
    "86 and 1 31 51 exec_1_1\n"
    "87 and 1 33 74 exec_1_2\n"
    "\n"
    "88 and 1 35 52 exec_2_0\n"
    "89 and 1 37 52 exec_2_1\n"
    "90 and 1 39 74 exec_2_2\n"
    "\n"
    "91 and 1 41 53 exec_3_0\n"
    "92 and 1 43 53 exec_3_1\n"
    "93 and 1 45 74 exec_3_2\n\n",
    encoder->formula.str());
}

// void add_statement_state_update ();
TEST_F(Btor2EncoderTest, add_statement_activation_basic)
{
  add_dummy_programs(3, 2);

  init_statement_execution(true);

  encoder->add_statement_activation();

  ASSERT_EQ(
    "; update statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_1_0\n"
    "73 not 1 67\n"
    "74 and 1 29 73\n"
    "75 next 1 29 74\n"
    "\n"
    "; stmt_1_1\n"
    "76 not 1 68\n"
    "77 and 1 31 76\n"
    "78 ite 1 29 67 77\n"
    "79 next 1 31 78\n"
    "\n"
    "; stmt_2_0\n"
    "80 not 1 69\n"
    "81 and 1 33 80\n"
    "82 next 1 33 81\n"
    "\n"
    "; stmt_2_1\n"
    "83 not 1 70\n"
    "84 and 1 35 83\n"
    "85 ite 1 33 69 84\n"
    "86 next 1 35 85\n"
    "\n"
    "; stmt_3_0\n"
    "87 not 1 71\n"
    "88 and 1 37 87\n"
    "89 next 1 37 88\n"
    "\n"
    "; stmt_3_1\n"
    "90 not 1 72\n"
    "91 and 1 39 90\n"
    "92 ite 1 37 71 91\n"
    "93 next 1 39 92\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  init_statement_execution(true);

  verbose = false;
  encoder->add_statement_activation();
  verbose = true;

  ASSERT_EQ(
    "73 not 1 67\n"
    "74 and 1 29 73\n"
    "75 next 1 29 74\n"
    "\n"
    "76 not 1 68\n"
    "77 and 1 31 76\n"
    "78 ite 1 29 67 77\n"
    "79 next 1 31 78\n"
    "\n"
    "80 not 1 69\n"
    "81 and 1 33 80\n"
    "82 next 1 33 81\n"
    "\n"
    "83 not 1 70\n"
    "84 and 1 35 83\n"
    "85 ite 1 33 69 84\n"
    "86 next 1 35 85\n"
    "\n"
    "87 not 1 71\n"
    "88 and 1 37 87\n"
    "89 next 1 37 88\n"
    "\n"
    "90 not 1 72\n"
    "91 and 1 39 90\n"
    "92 ite 1 37 71 91\n"
    "93 next 1 39 92\n\n",
    encoder->formula.str());
}

TEST_F(Btor2EncoderTest, add_statement_activation_jmp)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->add(Instruction::Set::create("ADDI", 1));
      programs[i]->add(Instruction::Set::create("STORE", 1));
      programs[i]->add(Instruction::Set::create("JMP", 1));
      programs[i]->add(Instruction::Set::create("EXIT", 1));
    }

  reset_encoder(1);

  init_statement_execution(true);

  encoder->add_statement_activation();

  ASSERT_EQ(
    "; update statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_1_0\n"
    "89 not 1 77\n"
    "90 and 1 27 89\n"
    "91 next 1 27 90\n"
    "\n"
    "; stmt_1_1\n"
    "92 not 1 78\n"
    "93 and 1 29 92\n"
    "94 ite 1 27 77 93\n"
    "95 ite 1 31 79 94\n"
    "96 next 1 29 95\n"
    "\n"
    "; stmt_1_2\n"
    "97 not 1 79\n"
    "98 and 1 31 97\n"
    "99 ite 1 29 78 98\n"
    "100 next 1 31 99\n"
    "\n"
    "; stmt_1_3\n"
    "101 not 1 80\n"
    "102 and 1 33 101\n"
    "103 next 1 33 102\n"
    "\n"
    "; stmt_2_0\n"
    "104 not 1 81\n"
    "105 and 1 35 104\n"
    "106 next 1 35 105\n"
    "\n"
    "; stmt_2_1\n"
    "107 not 1 82\n"
    "108 and 1 37 107\n"
    "109 ite 1 35 81 108\n"
    "110 ite 1 39 83 109\n"
    "111 next 1 37 110\n"
    "\n"
    "; stmt_2_2\n"
    "112 not 1 83\n"
    "113 and 1 39 112\n"
    "114 ite 1 37 82 113\n"
    "115 next 1 39 114\n"
    "\n"
    "; stmt_2_3\n"
    "116 not 1 84\n"
    "117 and 1 41 116\n"
    "118 next 1 41 117\n"
    "\n"
    "; stmt_3_0\n"
    "119 not 1 85\n"
    "120 and 1 43 119\n"
    "121 next 1 43 120\n"
    "\n"
    "; stmt_3_1\n"
    "122 not 1 86\n"
    "123 and 1 45 122\n"
    "124 ite 1 43 85 123\n"
    "125 ite 1 47 87 124\n"
    "126 next 1 45 125\n"
    "\n"
    "; stmt_3_2\n"
    "127 not 1 87\n"
    "128 and 1 47 127\n"
    "129 ite 1 45 86 128\n"
    "130 next 1 47 129\n"
    "\n"
    "; stmt_3_3\n"
    "131 not 1 88\n"
    "132 and 1 49 131\n"
    "133 next 1 49 132\n\n",
    encoder->formula.str());
}

TEST_F(Btor2EncoderTest, add_statement_activation_jmp_conditional)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->add(Instruction::Set::create("ADDI", 1));
      programs[i]->add(Instruction::Set::create("STORE", 1));
      programs[i]->add(Instruction::Set::create("JNZ", 1));
      programs[i]->add(Instruction::Set::create("EXIT", 1));
    }

  reset_encoder(3);

  init_statement_execution(true);

  encoder->add_statement_activation();

  ASSERT_EQ(vector<string>({"28", "30", "32", "34"}), encoder->nids_stmt[1]);
  ASSERT_EQ(vector<string>({"36", "38", "40", "42"}), encoder->nids_stmt[2]);
  ASSERT_EQ(vector<string>({"44", "46", "48", "50"}), encoder->nids_stmt[3]);

  ASSERT_EQ(vector<string>({"78", "79", "80", "81"}), encoder->nids_exec[1]);
  ASSERT_EQ(vector<string>({"82", "83", "84", "85"}), encoder->nids_exec[2]);
  ASSERT_EQ(vector<string>({"86", "87", "88", "89"}), encoder->nids_exec[3]);

  ASSERT_EQ(
    "; update statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_1_0\n"
    "90 not 1 78\n"
    "91 and 1 28 90\n"
    "92 next 1 28 91\n"
    "\n"
    "; stmt_1_1\n"
    "93 not 1 79\n"
    "94 and 1 30 93\n"
    "95 ite 1 28 78 94\n"
    "96 ne 1 16 6\n"
    "97 and 1 80 96\n"
    "98 ite 1 32 97 95\n"
    "99 next 1 30 98\n"
    "\n"
    "; stmt_1_2\n"
    "100 not 1 80\n"
    "101 and 1 32 100\n"
    "102 ite 1 30 79 101\n"
    "103 next 1 32 102\n"
    "\n"
    "; stmt_1_3\n"
    "104 not 1 81\n"
    "105 and 1 34 104\n"
    "106 not 1 96\n"
    "107 and 1 80 106\n"
    "108 ite 1 32 107 105\n"
    "109 next 1 34 108\n"
    "\n"
    "; stmt_2_0\n"
    "110 not 1 82\n"
    "111 and 1 36 110\n"
    "112 next 1 36 111\n"
    "\n"
    "; stmt_2_1\n"
    "113 not 1 83\n"
    "114 and 1 38 113\n"
    "115 ite 1 36 82 114\n"
    "116 ne 1 18 6\n"
    "117 and 1 84 116\n"
    "118 ite 1 40 117 115\n"
    "119 next 1 38 118\n"
    "\n"
    "; stmt_2_2\n"
    "120 not 1 84\n"
    "121 and 1 40 120\n"
    "122 ite 1 38 83 121\n"
    "123 next 1 40 122\n"
    "\n"
    "; stmt_2_3\n"
    "124 not 1 85\n"
    "125 and 1 42 124\n"
    "126 not 1 116\n"
    "127 and 1 84 126\n"
    "128 ite 1 40 127 125\n"
    "129 next 1 42 128\n"
    "\n"
    "; stmt_3_0\n"
    "130 not 1 86\n"
    "131 and 1 44 130\n"
    "132 next 1 44 131\n"
    "\n"
    "; stmt_3_1\n"
    "133 not 1 87\n"
    "134 and 1 46 133\n"
    "135 ite 1 44 86 134\n"
    "136 ne 1 20 6\n"
    "137 and 1 88 136\n"
    "138 ite 1 48 137 135\n"
    "139 next 1 46 138\n"
    "\n"
    "; stmt_3_2\n"
    "140 not 1 88\n"
    "141 and 1 48 140\n"
    "142 ite 1 46 87 141\n"
    "143 next 1 48 142\n"
    "\n"
    "; stmt_3_3\n"
    "144 not 1 89\n"
    "145 and 1 50 144\n"
    "146 not 1 136\n"
    "147 and 1 88 146\n"
    "148 ite 1 48 147 145\n"
    "149 next 1 50 148\n\n",
    encoder->formula.str());

  /* TODO remove
  reset_encoder(4);

  encoder->declare_sorts();
  encoder->declare_constants();
  encoder->add_bound();
  encoder->declare_states();
  encoder->add_thread_scheduling();
  encoder->add_synchronization_constraints();
  encoder->add_statement_execution();
  encoder->add_statement_activation();

  string formula = encoder->formula.str() + eol;

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

TEST_F(Btor2EncoderTest, add_statement_activation_jmp_start)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->add(Instruction::Set::create("ADDI", 1));
      programs[i]->add(Instruction::Set::create("STORE", 1));
      programs[i]->add(Instruction::Set::create("JNZ", 0));
      programs[i]->add(Instruction::Set::create("EXIT", 1));
    }

  reset_encoder(3);

  init_statement_execution(true);

  encoder->add_statement_activation();

  ASSERT_EQ(vector<string>({"28", "30", "32", "34"}), encoder->nids_stmt[1]);
  ASSERT_EQ(vector<string>({"36", "38", "40", "42"}), encoder->nids_stmt[2]);
  ASSERT_EQ(vector<string>({"44", "46", "48", "50"}), encoder->nids_stmt[3]);

  ASSERT_EQ(vector<string>({"78", "79", "80", "81"}), encoder->nids_exec[1]);
  ASSERT_EQ(vector<string>({"82", "83", "84", "85"}), encoder->nids_exec[2]);
  ASSERT_EQ(vector<string>({"86", "87", "88", "89"}), encoder->nids_exec[3]);

  ASSERT_EQ(
    "; update statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_1_0\n"
    "90 not 1 78\n"
    "91 and 1 28 90\n"
    "92 ne 1 16 6\n"
    "93 and 1 80 92\n"
    "94 ite 1 32 93 91\n"
    "95 next 1 28 94\n"
    "\n"
    "; stmt_1_1\n"
    "96 not 1 79\n"
    "97 and 1 30 96\n"
    "98 ite 1 28 78 97\n"
    "99 next 1 30 98\n"
    "\n"
    "; stmt_1_2\n"
    "100 not 1 80\n"
    "101 and 1 32 100\n"
    "102 ite 1 30 79 101\n"
    "103 next 1 32 102\n"
    "\n"
    "; stmt_1_3\n"
    "104 not 1 81\n"
    "105 and 1 34 104\n"
    "106 not 1 92\n"
    "107 and 1 80 106\n"
    "108 ite 1 32 107 105\n"
    "109 next 1 34 108\n"
    "\n"
    "; stmt_2_0\n"
    "110 not 1 82\n"
    "111 and 1 36 110\n"
    "112 ne 1 18 6\n"
    "113 and 1 84 112\n"
    "114 ite 1 40 113 111\n"
    "115 next 1 36 114\n"
    "\n"
    "; stmt_2_1\n"
    "116 not 1 83\n"
    "117 and 1 38 116\n"
    "118 ite 1 36 82 117\n"
    "119 next 1 38 118\n"
    "\n"
    "; stmt_2_2\n"
    "120 not 1 84\n"
    "121 and 1 40 120\n"
    "122 ite 1 38 83 121\n"
    "123 next 1 40 122\n"
    "\n"
    "; stmt_2_3\n"
    "124 not 1 85\n"
    "125 and 1 42 124\n"
    "126 not 1 112\n"
    "127 and 1 84 126\n"
    "128 ite 1 40 127 125\n"
    "129 next 1 42 128\n"
    "\n"
    "; stmt_3_0\n"
    "130 not 1 86\n"
    "131 and 1 44 130\n"
    "132 ne 1 20 6\n"
    "133 and 1 88 132\n"
    "134 ite 1 48 133 131\n"
    "135 next 1 44 134\n"
    "\n"
    "; stmt_3_1\n"
    "136 not 1 87\n"
    "137 and 1 46 136\n"
    "138 ite 1 44 86 137\n"
    "139 next 1 46 138\n"
    "\n"
    "; stmt_3_2\n"
    "140 not 1 88\n"
    "141 and 1 48 140\n"
    "142 ite 1 46 87 141\n"
    "143 next 1 48 142\n"
    "\n"
    "; stmt_3_3\n"
    "144 not 1 89\n"
    "145 and 1 50 144\n"
    "146 not 1 132\n"
    "147 and 1 88 146\n"
    "148 ite 1 48 147 145\n"
    "149 next 1 50 148\n\n",
    encoder->formula.str());

  /* TODO remove
  reset_encoder(4);

  encoder->declare_sorts();
  encoder->declare_constants();
  encoder->add_bound();
  encoder->declare_states();
  encoder->add_thread_scheduling();
  encoder->add_synchronization_constraints();
  encoder->add_statement_execution();
  encoder->add_statement_activation();

  string formula = encoder->formula.str() + eol;

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

TEST_F(Btor2EncoderTest, add_statement_activation_jmp_twice)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->add(Instruction::Set::create("ADDI", 1));
      programs[i]->add(Instruction::Set::create("STORE", 1));
      programs[i]->add(Instruction::Set::create("JZ", 1));
      programs[i]->add(Instruction::Set::create("JNZ", 1));
      programs[i]->add(Instruction::Set::create("EXIT", 1));
    }

  reset_encoder(3);

  init_statement_execution(true);

  encoder->add_statement_activation();

  ASSERT_EQ(vector<string>({"28", "30", "32", "34", "36"}), encoder->nids_stmt[1]);
  ASSERT_EQ(vector<string>({"38", "40", "42", "44", "46"}), encoder->nids_stmt[2]);
  ASSERT_EQ(vector<string>({"48", "50", "52", "54", "56"}), encoder->nids_stmt[3]);

  ASSERT_EQ(vector<string>({"84", "85", "86", "87", "88"}), encoder->nids_exec[1]);
  ASSERT_EQ(vector<string>({"89", "90", "91", "92", "93"}), encoder->nids_exec[2]);
  ASSERT_EQ(vector<string>({"94", "95", "96", "97", "98"}), encoder->nids_exec[3]);

  ASSERT_EQ(
    "; update statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_1_0\n"
    "99 not 1 84\n"
    "100 and 1 28 99\n"
    "101 next 1 28 100\n"
    "\n"
    "; stmt_1_1\n"
    "102 not 1 85\n"
    "103 and 1 30 102\n"
    "104 ite 1 28 84 103\n"
    "105 eq 1 16 6\n"
    "106 and 1 86 105\n"
    "107 ite 1 32 106 104\n"
    "108 ne 1 16 6\n"
    "109 and 1 87 108\n"
    "110 ite 1 34 109 107\n"
    "111 next 1 30 110\n"
    "\n"
    "; stmt_1_2\n"
    "112 not 1 86\n"
    "113 and 1 32 112\n"
    "114 ite 1 30 85 113\n"
    "115 next 1 32 114\n"
    "\n"
    "; stmt_1_3\n"
    "116 not 1 87\n"
    "117 and 1 34 116\n"
    "118 not 1 105\n"
    "119 and 1 86 118\n"
    "120 ite 1 32 119 117\n"
    "121 next 1 34 120\n"
    "\n"
    "; stmt_1_4\n"
    "122 not 1 88\n"
    "123 and 1 36 122\n"
    "124 not 1 108\n"
    "125 and 1 87 124\n"
    "126 ite 1 34 125 123\n"
    "127 next 1 36 126\n"
    "\n"
    "; stmt_2_0\n"
    "128 not 1 89\n"
    "129 and 1 38 128\n"
    "130 next 1 38 129\n"
    "\n"
    "; stmt_2_1\n"
    "131 not 1 90\n"
    "132 and 1 40 131\n"
    "133 ite 1 38 89 132\n"
    "134 eq 1 18 6\n"
    "135 and 1 91 134\n"
    "136 ite 1 42 135 133\n"
    "137 ne 1 18 6\n"
    "138 and 1 92 137\n"
    "139 ite 1 44 138 136\n"
    "140 next 1 40 139\n"
    "\n"
    "; stmt_2_2\n"
    "141 not 1 91\n"
    "142 and 1 42 141\n"
    "143 ite 1 40 90 142\n"
    "144 next 1 42 143\n"
    "\n"
    "; stmt_2_3\n"
    "145 not 1 92\n"
    "146 and 1 44 145\n"
    "147 not 1 134\n"
    "148 and 1 91 147\n"
    "149 ite 1 42 148 146\n"
    "150 next 1 44 149\n"
    "\n"
    "; stmt_2_4\n"
    "151 not 1 93\n"
    "152 and 1 46 151\n"
    "153 not 1 137\n"
    "154 and 1 92 153\n"
    "155 ite 1 44 154 152\n"
    "156 next 1 46 155\n"
    "\n"
    "; stmt_3_0\n"
    "157 not 1 94\n"
    "158 and 1 48 157\n"
    "159 next 1 48 158\n"
    "\n"
    "; stmt_3_1\n"
    "160 not 1 95\n"
    "161 and 1 50 160\n"
    "162 ite 1 48 94 161\n"
    "163 eq 1 20 6\n"
    "164 and 1 96 163\n"
    "165 ite 1 52 164 162\n"
    "166 ne 1 20 6\n"
    "167 and 1 97 166\n"
    "168 ite 1 54 167 165\n"
    "169 next 1 50 168\n"
    "\n"
    "; stmt_3_2\n"
    "170 not 1 96\n"
    "171 and 1 52 170\n"
    "172 ite 1 50 95 171\n"
    "173 next 1 52 172\n"
    "\n"
    "; stmt_3_3\n"
    "174 not 1 97\n"
    "175 and 1 54 174\n"
    "176 not 1 163\n"
    "177 and 1 96 176\n"
    "178 ite 1 52 177 175\n"
    "179 next 1 54 178\n"
    "\n"
    "; stmt_3_4\n"
    "180 not 1 98\n"
    "181 and 1 56 180\n"
    "182 not 1 166\n"
    "183 and 1 97 182\n"
    "184 ite 1 54 183 181\n"
    "185 next 1 56 184\n\n",
    encoder->formula.str());

  /* TODO remove
  reset_encoder(10);

  encoder->declare_sorts();
  encoder->declare_constants();
  encoder->add_bound();
  encoder->declare_states();
  encoder->add_thread_scheduling();
  encoder->add_synchronization_constraints();
  encoder->add_statement_execution();
  encoder->add_statement_activation();

  string formula = encoder->formula.str() + eol;

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

// void add_state_update (string, string, unordered_map<word, vector<word>> &);
TEST_F(Btor2EncoderTest, add_state_update_helper)
{
  add_dummy_programs(3, 3);

  init_statement_activation(true);

  string state = "0";
  string sym = "state";
  unordered_map<word, vector<word>> alters_state({
    {1, {0, 1, 2}},
    {2, {0, 1, 2}},
    {3, {0, 1, 2}}
  });

  /* thread states */
  for (encoder->thread = 1; encoder->thread <= 3; encoder->thread++)
    {
      encoder->add_state_update(state, sym, alters_state);

      vector<string> & exec = encoder->nids_exec[encoder->thread];

      string thread = to_string(encoder->thread);
      string accu = encoder->nids_accu[encoder->thread];
      string arg = encoder->nids_const[encoder->thread];

      string nid_0_addi = nid(-7);
      string nid_0_ite  = nid(-6);
      string nid_1_addi = nid(-5);
      string nid_1_ite  = nid(-4);
      string nid_2_addi = nid(-3);
      string nid_2_ite  = nid(-2);
      string nid_next   = nid(-1);

      ASSERT_EQ(
        "; " + sym + "\n"
        + nid_0_addi + " add 2 " + accu + " " + arg + "\n"
        + nid_0_ite  + " ite 1 " + exec[0] + " " + nid_0_addi + " " + state + " " + thread + ":0:ADDI:" + thread + "\n"
        + nid_1_addi + " add 2 " + accu + " " + arg + "\n"
        + nid_1_ite  + " ite 1 " + exec[1] + " " + nid_1_addi + " " + nid_0_ite + " " + thread + ":1:ADDI:" + thread + "\n"
        + nid_2_addi + " add 2 " + accu + " " + arg + "\n"
        + nid_2_ite  + " ite 1 " + exec[2] + " " + nid_2_addi + " " + nid_1_ite + " " + thread + ":2:ADDI:" + thread + "\n"
        + nid_next   + " next 2 " + state + " " + nid_2_ite + "\n\n",
        encoder->formula.str());

      encoder->formula.str("");
    }

  /* global state */
  reset_encoder(1);

  init_statement_activation(true);

  encoder->thread = 0;

  encoder->add_state_update(state, sym, alters_state);

  string nid_1_0_addi = nid(-19);
  string nid_1_0_ite  = nid(-18);
  string nid_1_1_addi = nid(-17);
  string nid_1_1_ite  = nid(-16);
  string nid_1_2_addi = nid(-15);
  string nid_1_2_ite  = nid(-14);

  string nid_2_0_addi = nid(-13);
  string nid_2_0_ite  = nid(-12);
  string nid_2_1_addi = nid(-11);
  string nid_2_1_ite  = nid(-10);
  string nid_2_2_addi = nid(-9);
  string nid_2_2_ite  = nid(-8);

  string nid_3_0_addi = nid(-7);
  string nid_3_0_ite  = nid(-6);
  string nid_3_1_addi = nid(-5);
  string nid_3_1_ite  = nid(-4);
  string nid_3_2_addi = nid(-3);
  string nid_3_2_ite  = nid(-2);

  string nid_next     = nid(-1);

  ASSERT_EQ(
      nid_1_0_addi + " add 2 " + encoder->nids_accu[1] + " 7\n"
    + nid_1_0_ite  + " ite 1 " + encoder->nids_exec[1][0] + " " + nid_1_0_addi + " " + state + " 1:0:ADDI:1\n"
    + nid_1_1_addi + " add 2 " + encoder->nids_accu[1] + " 7\n"
    + nid_1_1_ite  + " ite 1 " + encoder->nids_exec[1][1] + " " + nid_1_1_addi + " " + nid_1_0_ite + " 1:1:ADDI:1\n"
    + nid_1_2_addi + " add 2 " + encoder->nids_accu[1] + " 7\n"
    + nid_1_2_ite  + " ite 1 " + encoder->nids_exec[1][2] + " " + nid_1_2_addi + " " + nid_1_1_ite + " 1:2:ADDI:1\n"

    + nid_2_0_addi + " add 2 " + encoder->nids_accu[2] + " 8\n"
    + nid_2_0_ite  + " ite 1 " + encoder->nids_exec[2][0] + " " + nid_2_0_addi + " " + nid_1_2_ite + " 2:0:ADDI:2\n"
    + nid_2_1_addi + " add 2 " + encoder->nids_accu[2] + " 8\n"
    + nid_2_1_ite  + " ite 1 " + encoder->nids_exec[2][1] + " " + nid_2_1_addi + " " + nid_2_0_ite + " 2:1:ADDI:2\n"
    + nid_2_2_addi + " add 2 " + encoder->nids_accu[2] + " 8\n"
    + nid_2_2_ite  + " ite 1 " + encoder->nids_exec[2][2] + " " + nid_2_2_addi + " " + nid_2_1_ite + " 2:2:ADDI:2\n"

    + nid_3_0_addi + " add 2 " + encoder->nids_accu[3] + " 9\n"
    + nid_3_0_ite  + " ite 1 " + encoder->nids_exec[3][0] + " " + nid_3_0_addi + " " + nid_2_2_ite + " 3:0:ADDI:3\n"
    + nid_3_1_addi + " add 2 " + encoder->nids_accu[3] + " 9\n"
    + nid_3_1_ite  + " ite 1 " + encoder->nids_exec[3][1] + " " + nid_3_1_addi + " " + nid_3_0_ite + " 3:1:ADDI:3\n"
    + nid_3_2_addi + " add 2 " + encoder->nids_accu[3] + " 9\n"
    + nid_3_2_ite  + " ite 1 " + encoder->nids_exec[3][2] + " " + nid_3_2_addi + " " + nid_3_1_ite + " 3:2:ADDI:3\n"

    + nid_next + " next 2 " + state + " " + nid_3_2_ite + "\n\n",
    encoder->formula.str());
}

// void Btor2Encoder::add_accu_update ();
TEST_F(Btor2EncoderTest, add_accu_update)
{
  add_instruction_set(3);

  init_statement_activation(true);

  int offset = encoder->node + 1;

  encoder->add_accu_update();

  offset = static_cast<int>(encoder->node) - offset;

  expected = "; update accu ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n";

  for (encoder->thread = 1; encoder->thread <= 3; encoder->thread++)
    {
      vector<string> & exec = encoder->nids_exec[encoder->thread];

      string thread = to_string(encoder->thread);
      string accu = encoder->nids_accu[encoder->thread];

      string nid_0_ite  = nid(-offset--);
      string nid_2_add  = nid(-offset--);
      string nid_2_ite  = nid(-offset--);
      string nid_3_addi = nid(-offset--);
      string nid_3_ite  = nid(-offset--);
      string nid_4_sub  = nid(-offset--);
      string nid_4_ite  = nid(-offset--);
      string nid_5_subi = nid(-offset--);
      string nid_5_ite  = nid(-offset--);
      string nid_6_cmp  = nid(-offset--);
      string nid_6_ite  = nid(-offset--);
      string nid_13_mem = nid(-offset--);
      string nid_14_eq  = nid(-offset--);
      string nid_14_cas = nid(-offset--);
      string nid_14_ite = nid(-offset--);
      string nid_next   = nid(-offset--);

      expected +=
        "; accu_" + thread + "\n"
        + (encoder->thread > 1 ? "" : "509 read 2 14 7\n")
        + nid_0_ite  + " ite 1 " + exec[0] + " 509 " + accu + " " + thread + ":0:LOAD:1\n"
        + nid_2_add  + " add 2 " + accu + " 509\n"
        + nid_2_ite  + " ite 1 " + exec[2] + " " + nid_2_add + " " + nid_0_ite + " " + thread + ":2:ADD:1\n"
        + nid_3_addi + " add 2 " + accu + " 7\n"
        + nid_3_ite  + " ite 1 " + exec[3] + " " + nid_3_addi + " " + nid_2_ite + " " + thread + ":3:ADDI:1\n"
        + nid_4_sub  + " sub 2 " + accu + " 509\n"
        + nid_4_ite  + " ite 1 " + exec[4] + " " + nid_4_sub + " " + nid_3_ite + " " + thread + ":4:SUB:1\n"
        + nid_5_subi + " sub 2 " + accu + " 7\n"
        + nid_5_ite  + " ite 1 " + exec[5] + " " + nid_5_subi + " " + nid_4_ite + " " + thread + ":5:SUBI:1\n"
        + nid_6_cmp  + " sub 2 " + accu + " 509\n"
        + nid_6_ite  + " ite 1 " + exec[6] + " " + nid_6_cmp + " " + nid_5_ite + " " + thread + ":6:CMP:1\n"
        + nid_13_mem + " ite 1 " + exec[13] + " 509 " + nid_6_ite + " " + thread + ":13:MEM:1\n"
        + nid_14_eq  + " eq 1 "  + encoder->nids_mem[encoder->thread] + " 509\n"
        + nid_14_cas + " ite 1 " + nid_14_eq + " 7 6\n"
        + nid_14_ite + " ite 1 " + exec[14] + " " + nid_14_cas + " " + nid_13_mem + " " + thread + ":14:CAS:1\n"
        + nid_next   + " next 2 " + accu + " " + nid_14_ite + "\n\n";
    }

  ASSERT_EQ(expected, encoder->formula.str());
}

// void Btor2Encoder::add_mem_update ();
TEST_F(Btor2EncoderTest, add_mem_update)
{
  add_instruction_set(3);

  init_statement_activation(true);

  int offset = encoder->node + 1;

  encoder->add_mem_update();

  offset = static_cast<int>(encoder->node) - offset;

  expected = "; update CAS memory register ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n";

  for (encoder->thread = 1; encoder->thread <= 3; encoder->thread++)
    {
      vector<string> & exec = encoder->nids_exec[encoder->thread];

      string thread = to_string(encoder->thread);
      string mem = encoder->nids_mem[encoder->thread];

      string nid_13_ite = nid(-offset--);
      string nid_next = nid(-offset--);

      expected +=
        "; mem_" + thread + "\n"
        + (encoder->thread > 1 ? "" : "509 read 2 14 7\n")
        + nid_13_ite + " ite 1 " + exec[13] + " 509 " + mem + " " + thread + ":13:MEM:1\n"
        + nid_next + " next 2 " + mem + " " + nid_13_ite + "\n\n";
    }

  ASSERT_EQ(expected, encoder->formula.str());
}

// void Btor2Encoder::add_heap_update ();
TEST_F(Btor2EncoderTest, add_heap_update)
{
  add_instruction_set(3);

  init_statement_activation(true);

  encoder->thread = 0;

  encoder->update_accu = false;

  encoder->add_heap_update();

  string nid_1_1_ite  = nid(-14);
  string nid_1_14_eq  = nid(-12);
  string nid_1_14_cas = nid(-11);
  string nid_1_14_ite = nid(-10);

  string nid_2_1_ite  = nid(-9);
  string nid_2_14_eq  = nid(-8);
  string nid_2_14_cas = nid(-7);
  string nid_2_14_ite = nid(-6);

  string nid_3_1_ite  = nid(-5);
  string nid_3_14_eq  = nid(-4);
  string nid_3_14_cas = nid(-3);
  string nid_3_14_ite = nid(-2);

  string nid_next     = nid(-1);

  ASSERT_EQ(
    "; update heap ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n"
    "509 write 3 14 7 15\n"

    + nid_1_1_ite  + " ite 1 " + encoder->nids_exec[1][1] + " 509 14 1:1:STORE:1\n"
    "511 read 2 14 7\n"
    + nid_1_14_eq  + " eq 1 "  + encoder->nids_mem[1] + " 511\n"
    + nid_1_14_cas + " ite 1 " + nid_1_14_eq + " 509 14\n"
    + nid_1_14_ite + " ite 1 " + encoder->nids_exec[1][14] + " " + nid_1_14_cas + " " + nid_1_1_ite + " 1:14:CAS:1\n"

    + nid_2_1_ite  + " ite 1 " + encoder->nids_exec[2][1] + " 509 " + nid_1_14_ite + " 2:1:STORE:1\n"
    + nid_2_14_eq  + " eq 1 "  + encoder->nids_mem[2] + " 511\n"
    + nid_2_14_cas + " ite 1 " + nid_2_14_eq + " 509 14\n"
    + nid_2_14_ite + " ite 1 " + encoder->nids_exec[2][14] + " " + nid_2_14_cas + " " + nid_2_1_ite + " 2:14:CAS:1\n"

    + nid_3_1_ite  + " ite 1 " + encoder->nids_exec[3][1] + " 509 " + nid_2_14_ite + " 3:1:STORE:1\n"
    + nid_3_14_eq  + " eq 1 "  + encoder->nids_mem[3] + " 511\n"
    + nid_3_14_cas + " ite 1 " + nid_3_14_eq + " 509 14\n"
    + nid_3_14_ite + " ite 1 " + encoder->nids_exec[3][14] + " " + nid_3_14_cas + " " + nid_3_1_ite + " 3:14:CAS:1\n"

    + nid_next     + " next 2 14 " + nid_3_14_ite + "\n\n",
    encoder->formula.str());
}

// void Btor2Encoder::add_exit_flag_update ();
TEST_F(Btor2EncoderTest, add_exit_flag_update)
{
  add_instruction_set(3);

  init_statement_activation(true);

  encoder->add_exit_flag_update();

  string nid_or_1 = nid(-4);
  string nid_or_2 = nid(-3);
  string nid_or_3 = nid(-2);
  string nid_next = nid(-1);

  ASSERT_EQ(
    "; update exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    + nid_or_1 + " or 1 " + encoder->nid_exit + " " + encoder->nids_exec[3][16] + "\n"
    + nid_or_2 + " or 1 " + encoder->nids_exec[1][16] + " " + nid_or_1 + "\n"
    + nid_or_3 + " or 1 " + encoder->nids_exec[2][16] + " " + nid_or_2 + "\n"
    + nid_next + " next 1 " + encoder->nid_exit + " " + nid_or_3 + "\n"
    "\n",
    encoder->formula.str());
}

// void Btor2Encoder::add_exit_code_update ();
TEST_F(Btor2EncoderTest, add_exit_code_update)
{
  add_instruction_set(3);

  init_statement_activation(true);

  encoder->add_exit_code_update();

  string nid_one = encoder->nids_const[1];
  string nid_ite_1 = nid(-4);
  string nid_ite_2 = nid(-3);
  string nid_ite_3 = nid(-2);
  string nid_next = nid(-1);

  ASSERT_EQ(
    "; update exit code ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    + nid_ite_1 + " ite 1 " + encoder->nids_exec[1][16] + " " + nid_one + " " + encoder->nid_exit_code + " 1:16:EXIT:1\n"
    + nid_ite_2 + " ite 1 " + encoder->nids_exec[2][16] + " " + nid_one + " " + nid_ite_1 + " 2:16:EXIT:1\n"
    + nid_ite_3 + " ite 1 " + encoder->nids_exec[3][16] + " " + nid_one + " " + nid_ite_2 + " 3:16:EXIT:1\n"
    + nid_next + " next 2 " + encoder->nid_exit_code + " " + nid_ite_3 + "\n"
    "\n",
    encoder->formula.str());
}

// void add_state_update ();
TEST_F(Btor2EncoderTest, add_state_update)
{
  add_instruction_set(3);

  init_statement_activation(true);

  encoder->add_state_update();

  ASSERT_EQ(
    "; update accu ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu_1\n"
    "509 read 2 14 7\n"
    "510 ite 1 167 509 15 1:0:LOAD:1\n"
    "511 add 2 15 509\n"
    "512 ite 1 169 511 510 1:2:ADD:1\n"
    "513 add 2 15 7\n"
    "514 ite 1 170 513 512 1:3:ADDI:1\n"
    "515 sub 2 15 509\n"
    "516 ite 1 171 515 514 1:4:SUB:1\n"
    "517 sub 2 15 7\n"
    "518 ite 1 172 517 516 1:5:SUBI:1\n"
    "519 sub 2 15 509\n"
    "520 ite 1 173 519 518 1:6:CMP:1\n"
    "521 ite 1 180 509 520 1:13:MEM:1\n"
    "522 eq 1 21 509\n"
    "523 ite 1 522 7 6\n"
    "524 ite 1 181 523 521 1:14:CAS:1\n"
    "525 next 2 15 524\n"
    "\n"
    "; accu_2\n"
    "526 ite 1 184 509 17 2:0:LOAD:1\n"
    "527 add 2 17 509\n"
    "528 ite 1 186 527 526 2:2:ADD:1\n"
    "529 add 2 17 7\n"
    "530 ite 1 187 529 528 2:3:ADDI:1\n"
    "531 sub 2 17 509\n"
    "532 ite 1 188 531 530 2:4:SUB:1\n"
    "533 sub 2 17 7\n"
    "534 ite 1 189 533 532 2:5:SUBI:1\n"
    "535 sub 2 17 509\n"
    "536 ite 1 190 535 534 2:6:CMP:1\n"
    "537 ite 1 197 509 536 2:13:MEM:1\n"
    "538 eq 1 23 509\n"
    "539 ite 1 538 7 6\n"
    "540 ite 1 198 539 537 2:14:CAS:1\n"
    "541 next 2 17 540\n"
    "\n"
    "; accu_3\n"
    "542 ite 1 201 509 19 3:0:LOAD:1\n"
    "543 add 2 19 509\n"
    "544 ite 1 203 543 542 3:2:ADD:1\n"
    "545 add 2 19 7\n"
    "546 ite 1 204 545 544 3:3:ADDI:1\n"
    "547 sub 2 19 509\n"
    "548 ite 1 205 547 546 3:4:SUB:1\n"
    "549 sub 2 19 7\n"
    "550 ite 1 206 549 548 3:5:SUBI:1\n"
    "551 sub 2 19 509\n"
    "552 ite 1 207 551 550 3:6:CMP:1\n"
    "553 ite 1 214 509 552 3:13:MEM:1\n"
    "554 eq 1 25 509\n"
    "555 ite 1 554 7 6\n"
    "556 ite 1 215 555 553 3:14:CAS:1\n"
    "557 next 2 19 556\n"
    "\n"
    "; update CAS memory register ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; mem_1\n"
    "558 ite 1 180 509 21 1:13:MEM:1\n"
    "559 next 2 21 558\n"
    "\n"
    "; mem_2\n"
    "560 ite 1 197 509 23 2:13:MEM:1\n"
    "561 next 2 23 560\n"
    "\n"
    "; mem_3\n"
    "562 ite 1 214 509 25 3:13:MEM:1\n"
    "563 next 2 25 562\n"
    "\n"
    "; update heap ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "564 write 3 14 7 15\n"
    "565 ite 1 168 564 14 1:1:STORE:1\n"
    "566 eq 1 21 509\n"
    "567 ite 1 566 564 14\n"
    "568 ite 1 181 567 565 1:14:CAS:1\n"
    "569 ite 1 185 564 568 2:1:STORE:1\n"
    "570 eq 1 23 509\n"
    "571 ite 1 570 564 14\n"
    "572 ite 1 198 571 569 2:14:CAS:1\n"
    "573 ite 1 202 564 572 3:1:STORE:1\n"
    "574 eq 1 25 509\n"
    "575 ite 1 574 564 14\n"
    "576 ite 1 215 575 573 3:14:CAS:1\n"
    "577 next 2 14 576\n"
    "\n"
    "; update exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "578 or 1 129 217\n"
    "579 or 1 183 578\n"
    "580 or 1 200 579\n"
    "581 next 1 129 580\n"
    "\n"
    "; update exit code ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "582 ite 1 183 7 131 1:16:EXIT:1\n"
    "583 ite 1 200 7 582 2:16:EXIT:1\n"
    "584 ite 1 217 7 583 3:16:EXIT:1\n"
    "585 next 2 131 584\n"
    "\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  init_statement_activation(true);

  verbose = false;
  encoder->add_state_update();
  verbose = true;

  ASSERT_EQ(
    "509 read 2 14 7\n"
    "510 ite 1 167 509 15\n"
    "511 add 2 15 509\n"
    "512 ite 1 169 511 510\n"
    "513 add 2 15 7\n"
    "514 ite 1 170 513 512\n"
    "515 sub 2 15 509\n"
    "516 ite 1 171 515 514\n"
    "517 sub 2 15 7\n"
    "518 ite 1 172 517 516\n"
    "519 sub 2 15 509\n"
    "520 ite 1 173 519 518\n"
    "521 ite 1 180 509 520\n"
    "522 eq 1 21 509\n"
    "523 ite 1 522 7 6\n"
    "524 ite 1 181 523 521\n"
    "525 next 2 15 524\n"
    "\n"
    "526 ite 1 184 509 17\n"
    "527 add 2 17 509\n"
    "528 ite 1 186 527 526\n"
    "529 add 2 17 7\n"
    "530 ite 1 187 529 528\n"
    "531 sub 2 17 509\n"
    "532 ite 1 188 531 530\n"
    "533 sub 2 17 7\n"
    "534 ite 1 189 533 532\n"
    "535 sub 2 17 509\n"
    "536 ite 1 190 535 534\n"
    "537 ite 1 197 509 536\n"
    "538 eq 1 23 509\n"
    "539 ite 1 538 7 6\n"
    "540 ite 1 198 539 537\n"
    "541 next 2 17 540\n"
    "\n"
    "542 ite 1 201 509 19\n"
    "543 add 2 19 509\n"
    "544 ite 1 203 543 542\n"
    "545 add 2 19 7\n"
    "546 ite 1 204 545 544\n"
    "547 sub 2 19 509\n"
    "548 ite 1 205 547 546\n"
    "549 sub 2 19 7\n"
    "550 ite 1 206 549 548\n"
    "551 sub 2 19 509\n"
    "552 ite 1 207 551 550\n"
    "553 ite 1 214 509 552\n"
    "554 eq 1 25 509\n"
    "555 ite 1 554 7 6\n"
    "556 ite 1 215 555 553\n"
    "557 next 2 19 556\n"
    "\n"
    "558 ite 1 180 509 21\n"
    "559 next 2 21 558\n"
    "\n"
    "560 ite 1 197 509 23\n"
    "561 next 2 23 560\n"
    "\n"
    "562 ite 1 214 509 25\n"
    "563 next 2 25 562\n"
    "\n"
    "564 write 3 14 7 15\n"
    "565 ite 1 168 564 14\n"
    "566 eq 1 21 509\n"
    "567 ite 1 566 564 14\n"
    "568 ite 1 181 567 565\n"
    "569 ite 1 185 564 568\n"
    "570 eq 1 23 509\n"
    "571 ite 1 570 564 14\n"
    "572 ite 1 198 571 569\n"
    "573 ite 1 202 564 572\n"
    "574 eq 1 25 509\n"
    "575 ite 1 574 564 14\n"
    "576 ite 1 215 575 573\n"
    "577 next 2 14 576\n"
    "\n"
    "578 or 1 129 217\n"
    "579 or 1 183 578\n"
    "580 or 1 200 579\n"
    "581 next 1 129 580\n"
    "\n"
    "582 ite 1 183 7 131\n"
    "583 ite 1 200 7 582\n"
    "584 ite 1 217 7 583\n"
    "585 next 2 131 584\n"
    "\n",
    encoder->formula.str());
}

// std::string load(Load &);
TEST_F(Btor2EncoderTest, load)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  Load l(1);

  ASSERT_EQ("35", encoder->load(l));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ("35 read 2 14 7\n", encoder->formula.str());

  /* another load from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("35", encoder->load(l));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ("", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  l.indirect = true;

  ASSERT_EQ("36", encoder->load(l));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "36"}}), encoder->nids_load_indirect);
  ASSERT_EQ("36 read 2 14 35\n", encoder->formula.str());

  /* another load from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("36", encoder->load(l));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "36"}}), encoder->nids_load_indirect);
  ASSERT_EQ("", encoder->formula.str());
}

// std::string store(Store &);
TEST_F(Btor2EncoderTest, store)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  Store s(1);

  encoder->thread = 1;

  ASSERT_EQ("35", encoder->store(s));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_store);
  ASSERT_EQ("35 write 3 14 7 15\n", encoder->formula.str());

  /* another store to the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("35", encoder->store(s));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_store);
  ASSERT_EQ("", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  s.indirect = true;

  ASSERT_EQ("37", encoder->store(s));
  ASSERT_EQ(NIDMap({{1, "36"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "37"}}), encoder->nids_store_indirect);
  ASSERT_EQ(
    "36 read 2 14 7\n"
    "37 write 3 14 36 15\n",
    encoder->formula.str());

  /* another store to the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("37", encoder->store(s));
  ASSERT_EQ(NIDMap({{1, "36"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "37"}}), encoder->nids_store_indirect);
  ASSERT_EQ("", encoder->formula.str());
}

// virtual void encode (void);
TEST_F(Btor2EncoderTest, encode)
{
  // TODO
}

// virtual std::string encode (Load &);
TEST_F(Btor2EncoderTest, LOAD)
{
  Btor2EncoderTest_load_Test();
}

// virtual std::string encode (Store &);
TEST_F(Btor2EncoderTest, STORE)
{
  Btor2EncoderTest_store_Test();
}

// virtual std::string encode (Add &);
TEST_F(Btor2EncoderTest, ADD)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Add a(1);

  ASSERT_EQ("36", encoder->encode(a));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(
    "35 read 2 14 7\n"
    "36 add 2 15 35\n",
    encoder->formula.str());

  /* another ADD from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("37", encoder->encode(a));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ("37 add 2 15 35\n", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  a.indirect = true;

  ASSERT_EQ("39", encoder->encode(a));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "38"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "38 read 2 14 35\n"
    "39 add 2 15 38\n",
    encoder->formula.str());

  /* another ADD from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("40", encoder->encode(a));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "38"}}), encoder->nids_load_indirect);
  ASSERT_EQ("40 add 2 15 38\n", encoder->formula.str());
}

// virtual std::string encode (Addi &);
TEST_F(Btor2EncoderTest, ADDI)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Addi a(1);

  ASSERT_EQ("35", encoder->encode(a));
  ASSERT_EQ("35 add 2 15 7\n", encoder->formula.str());

  /* another ADDI with the same constant */
  encoder->formula.str("");

  ASSERT_EQ("36", encoder->encode(a));
  ASSERT_EQ("36 add 2 15 7\n", encoder->formula.str());
}

// virtual std::string encode (Sub &);
TEST_F(Btor2EncoderTest, SUB)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Sub s(1);

  ASSERT_EQ("36", encoder->encode(s));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(
    "35 read 2 14 7\n"
    "36 sub 2 15 35\n",
    encoder->formula.str());

  /* another SUB from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("37", encoder->encode(s));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ("37 sub 2 15 35\n", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  s.indirect = true;

  ASSERT_EQ("39", encoder->encode(s));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "38"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "38 read 2 14 35\n"
    "39 sub 2 15 38\n",
    encoder->formula.str());

  /* another SUB from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("40", encoder->encode(s));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "38"}}), encoder->nids_load_indirect);
  ASSERT_EQ("40 sub 2 15 38\n", encoder->formula.str());
}

// virtual std::string encode (Subi &);
TEST_F(Btor2EncoderTest, SUBI)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Subi s(1);

  ASSERT_EQ("35", encoder->encode(s));
  ASSERT_EQ("35 sub 2 15 7\n", encoder->formula.str());

  /* another SUBI with the same constant */
  encoder->formula.str("");

  ASSERT_EQ("36", encoder->encode(s));
  ASSERT_EQ("36 sub 2 15 7\n", encoder->formula.str());
}

// virtual std::string encode (Cmp &);
TEST_F(Btor2EncoderTest, CMP)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Cmp c(1);

  ASSERT_EQ("36", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(
    "35 read 2 14 7\n"
    "36 sub 2 15 35\n",
    encoder->formula.str());

  /* another CMP from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("37", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ("37 sub 2 15 35\n", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  c.indirect = true;

  ASSERT_EQ("39", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "38"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "38 read 2 14 35\n"
    "39 sub 2 15 38\n",
    encoder->formula.str());

  /* another CMP from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("40", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "38"}}), encoder->nids_load_indirect);
  ASSERT_EQ("40 sub 2 15 38\n", encoder->formula.str());
}

// virtual std::string encode (Jmp &);
TEST_F(Btor2EncoderTest, JMP)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Jmp j(1);

  ASSERT_EQ("", encoder->encode(j));
  ASSERT_EQ("", encoder->formula.str());
}

// virtual std::string encode (Jz &);
TEST_F(Btor2EncoderTest, JZ)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Jz j(1);

  ASSERT_EQ("35", encoder->encode(j));
  ASSERT_EQ("35 eq 1 15 6\n", encoder->formula.str());
}

// virtual std::string encode (Jnz &);
TEST_F(Btor2EncoderTest, JNZ)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Jnz j(1);

  ASSERT_EQ("35", encoder->encode(j));
  ASSERT_EQ("35 ne 1 15 6\n", encoder->formula.str());
}

// virtual std::string encode (Js &);
TEST_F(Btor2EncoderTest, JS)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Js j(1);

  ASSERT_EQ("35", encoder->encode(j));
  ASSERT_EQ("35 slice 1 15 15 15\n", encoder->formula.str());
}

// virtual std::string encode (Jns &);
TEST_F(Btor2EncoderTest, JNS)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Jns j(1);

  ASSERT_EQ("36", encoder->encode(j));
  ASSERT_EQ(
    "35 slice 1 15 15 15\n"
    "36 not 1 35\n",
    encoder->formula.str());
}

// virtual std::string encode (Jnzns &);
TEST_F(Btor2EncoderTest, JNZNS)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Jnzns j(1);

  ASSERT_EQ("39", encoder->encode(j));
  ASSERT_EQ(
    "36 ne 1 15 6\n"
    "37 slice 1 15 15 15\n"
    "38 not 1 37\n"
    "39 and 1 36 38\n",
    encoder->formula.str());
}

// virtual std::string encode (Mem &);
TEST_F(Btor2EncoderTest, MEM)
{
  Btor2EncoderTest_LOAD_Test();
}

// virtual std::string encode (Cas &);
TEST_F(Btor2EncoderTest, CAS_accu)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  encoder->update_accu = true;

  Cas c(1);

  ASSERT_EQ("37", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(
    "35 read 2 14 7\n"
    "36 eq 1 17 35\n"
    "37 ite 1 36 7 6\n",
    encoder->formula.str());

  /* another CAS to the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("39", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(
    "38 eq 1 17 35\n"
    "39 ite 1 38 7 6\n",
    encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  c.indirect = true;

  ASSERT_EQ("42", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "40"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "40 read 2 14 35\n"
    "41 eq 1 17 40\n"
    "42 ite 1 41 7 6\n",
    encoder->formula.str());

  /* another CAS to the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("44", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "40"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "43 eq 1 17 40\n"
    "44 ite 1 43 7 6\n",
    encoder->formula.str());
}

TEST_F(Btor2EncoderTest, CAS_heap)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  encoder->update_accu = false;

  Cas c(1);

  ASSERT_EQ("38", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(
    "35 read 2 14 7\n"
    "36 eq 1 17 35\n"
    "37 write 3 14 7 15\n"
    "38 ite 1 36 37 14\n",
    encoder->formula.str());

  /* another CAS to the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("40", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(
    "39 eq 1 17 35\n"
    "40 ite 1 39 37 14\n",
    encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  c.indirect = true;

  ASSERT_EQ("44", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "41"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "41 read 2 14 35\n"
    "42 eq 1 17 41\n"
    "43 write 3 14 35 15\n"
    "44 ite 1 42 43 14\n",
    encoder->formula.str());

  /* another CAS to the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("46", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "41"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "45 eq 1 17 41\n"
    "46 ite 1 45 43 14\n",
    encoder->formula.str());
}

// virtual std::string encode (Sync &);
TEST_F(Btor2EncoderTest, SYNC)
{
  Sync s(1);

  ASSERT_EQ("", encoder->encode(s));
  ASSERT_EQ("", encoder->formula.str());
}

// virtual std::string encode (Exit &);
TEST_F(Btor2EncoderTest, EXIT)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  Exit e(1);

  ASSERT_EQ("7", encoder->encode(e));
  ASSERT_EQ("", encoder->formula.str());
}
