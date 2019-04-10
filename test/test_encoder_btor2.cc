#include <gtest/gtest.h>

#include "encoder.hh"
#include "parser.hh"

using namespace std;

typedef map<word, string> Word2NIDMap;
typedef map<word, map<word, string>> Word2Word2NIDMap;

// TODO remove - debug only
#include "btor2.hh"
#include "btormc.hh"
void evaluate (string & formula)
{
  BtorMC btormc(20);
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
            programs[i]->push_back(op);
        }

      encoder = create_encoder(1);
    }

  void add_instruction_set (unsigned num)
    {
      for (size_t i = 0; i < num; i++)
        {
          programs.push_back(shared_ptr<Program>(new Program()));

          programs[i]->push_back(Instruction::Set::create("LOAD", 1));  // 0
          programs[i]->push_back(Instruction::Set::create("STORE", 1)); // 1
          programs[i]->push_back(Instruction::Set::create("ADD", 1));   // 2
          programs[i]->push_back(Instruction::Set::create("ADDI", 1));  // 3
          programs[i]->push_back(Instruction::Set::create("SUB", 1));   // 4
          programs[i]->push_back(Instruction::Set::create("SUBI", 1));  // 5
          programs[i]->push_back(Instruction::Set::create("CMP", 1));   // 6
          programs[i]->push_back(Instruction::Set::create("JMP", 1));   // 7
          programs[i]->push_back(Instruction::Set::create("JZ", 1));    // 8
          programs[i]->push_back(Instruction::Set::create("JNZ", 1));   // 9
          programs[i]->push_back(Instruction::Set::create("JS", 1));    // 10
          programs[i]->push_back(Instruction::Set::create("JNS", 1));   // 11
          programs[i]->push_back(Instruction::Set::create("JNZNS", 1)); // 12
          programs[i]->push_back(Instruction::Set::create("MEM", 1));   // 13
          programs[i]->push_back(Instruction::Set::create("CAS", 1));   // 14
          programs[i]->push_back(Instruction::Set::create("SYNC", 1));  // 15
          programs[i]->push_back(Instruction::Set::create("EXIT", 1));  // 16
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
    Word2NIDMap({{0, ""}, {1, ""}, {2, ""}, {3, ""}}),
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
    "3 sort array 2 2\n"
    "\n",
    encoder->str());

  /* verbosity */
  reset_encoder(1);

  verbose = false;
  encoder->declare_sorts();
  verbose = true;

  ASSERT_EQ(
    "1 sort bitvec 1\n"
    "2 sort bitvec 16\n"
    "3 sort array 2 2\n"
    "\n",
    encoder->str());
}

// void Btor2Encoder::declare_constants ();
TEST_F(Btor2EncoderTest, declare_constants)
{
  for (size_t t = 0; t < 3; t++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      for (size_t pc = 0; pc < 3; pc++)
        programs.back()->push_back(
          Instruction::Set::create("ADDI", t + pc + 1));
    }

  reset_encoder(1);

  encoder->declare_sorts();
  encoder->declare_constants();

  ASSERT_EQ("4", encoder->nid_false);
  ASSERT_EQ("5", encoder->nid_true);
  ASSERT_EQ(
    Word2NIDMap({{0, "6"}, {1, "7"}, {2, "8"}, {3, "9"}, {4, "10"}, {5, "11"}}),
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
    "11 constd 2 5\n"
    "\n",
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
    "11 constd 2 5\n"
    "\n",
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
    "13 bad 12\n"
    "\n",
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
    "13 bad 12\n"
    "\n",
    encoder->formula.str());
}

// void declare_states ();
TEST_F(Btor2EncoderTest, declare_states)
{
  add_dummy_programs(3, 3);

  add_declerations(true);

  encoder->declare_states();

  ASSERT_EQ("10", encoder->nid_heap);
  ASSERT_EQ(Word2NIDMap({{1, "11"}, {2, "13"}, {3, "15"}}), encoder->nids_accu);
  ASSERT_EQ(Word2NIDMap({{1, "17"}, {2, "19"}, {3, "21"}}), encoder->nids_mem);
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
    "43 state 2 exit-code\n"
    "44 init 2 43 6\n"
    "\n",
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
    "43 state 2 exit-code\n"
    "44 init 2 43 6\n"
    "\n",
    encoder->formula.str());
}

// void add_thread_scheduling ();
TEST_F(Btor2EncoderTest, add_thread_scheduling)
{
  add_dummy_programs(3, 3);

  init_states(true);

  encoder->add_thread_scheduling();

  ASSERT_EQ(
    Word2NIDMap({{1, "51"}, {2, "52"}, {3, "53"}}),
    encoder->nids_thread);
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
    "69 constraint 68\n"
    "\n",
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
    "69 constraint 68\n"
    "\n",
    encoder->formula.str());
}

// void add_synchronization_constraints ();
TEST_F(Btor2EncoderTest, add_synchronization_constraints)
{
  for (size_t t = 0; t < 3; t++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      for (size_t pc = 0; pc < 2; pc++)
        programs.back()->push_back(Instruction::Set::create("SYNC", pc + 1));
    }

  reset_encoder(1);

  init_thread_scheduling(true);

  encoder->add_synchronization_constraints();

  ASSERT_EQ(Word2NIDMap({{1, "67"}, {2, "79"}}), encoder->nids_sync);
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
    "89 constraint 88 sync_2_block_3\n"
    "\n",
    encoder->formula.str());

  /* multiple calls to the same barrier */
  for (const auto & program : programs)
    for (size_t pc = 0; pc < 4; pc++)
      program->push_back(Instruction::Set::create("SYNC", pc % 2 + 1));

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
  ASSERT_EQ(Word2NIDMap({{1, "97"}, {2, "115"}}), encoder->nids_sync);
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
    "125 constraint 124 sync_2_block_3\n"
    "\n",
    encoder->formula.str());

  /* barrier only for a subset of threads */
  for (size_t i = 0; i < programs.size() - 1; i++)
    programs[i]->push_back(Instruction::Set::create("SYNC", 3));

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
  ASSERT_EQ(
    Word2NIDMap({{1, "102"}, {2, "120"}, {3, "133"}}),
    encoder->nids_sync);
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
    "140 constraint 139 sync_3_block_2\n"
    "\n",
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
    "140 constraint 139 sync_3_block_2\n"
    "\n",
    encoder->formula.str());
}

TEST_F(Btor2EncoderTest, add_synchronization_constraints_single_thread)
{
  programs.push_back(shared_ptr<Program>(new Program()));
  programs.back()->push_back(Instruction::Set::create("SYNC", 1));

  reset_encoder(1);

  init_thread_scheduling(true);

  encoder->add_synchronization_constraints();

  ASSERT_EQ(Word2NIDMap({{1, encoder->nids_stmt[1][0]}}), encoder->nids_sync);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; synchronization constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; negated thread activation variables\n"
    "30 not 1 25 not_thread_1\n"
    "\n"
    "; synchronization condition sync_1\n"
    "31 not 1 19 not_sync_1\n"
    "\n"
    "; disable threads waiting for barrier 1\n"
    "32 and 1 19 31\n"
    "33 implies 1 32 30\n"
    "34 constraint 33 sync_1_block_1\n"
    "\n",
    encoder->formula.str());
}

TEST_F(Btor2EncoderTest, add_synchronization_constraints_no_sync)
{
  add_dummy_programs(3, 1);

  init_thread_scheduling(true);

  encoder->add_synchronization_constraints();

  ASSERT_TRUE(encoder->nids_sync.empty());
  ASSERT_EQ("", encoder->formula.str());
}

// void add_statement_execution ();
TEST_F(Btor2EncoderTest, add_statement_execution)
{
  add_dummy_programs(3, 2);

  for (const auto & program : programs)
    program->push_back(Instruction::Set::create("SYNC", 1));

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
    "93 and 1 45 74 exec_3_2\n"
    "\n",
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
    "93 and 1 45 74 exec_3_2\n"
    "\n",
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
    "70 not 1 64\n"
    "71 and 1 29 70\n"
    "72 next 1 29 71 1:0:ADDI:1\n"
    "\n"
    "; stmt_1_1\n"
    "73 not 1 65\n"
    "74 and 1 31 73\n"
    "75 ite 1 29 64 74 1:0:ADDI:1\n"
    "76 next 1 31 75 1:1:ADDI:1\n"
    "\n"
    "; stmt_2_0\n"
    "77 not 1 66\n"
    "78 and 1 33 77\n"
    "79 next 1 33 78 2:0:ADDI:2\n"
    "\n"
    "; stmt_2_1\n"
    "80 not 1 67\n"
    "81 and 1 35 80\n"
    "82 ite 1 33 66 81 2:0:ADDI:2\n"
    "83 next 1 35 82 2:1:ADDI:2\n"
    "\n"
    "; stmt_3_0\n"
    "84 not 1 68\n"
    "85 and 1 37 84\n"
    "86 next 1 37 85 3:0:ADDI:3\n"
    "\n"
    "; stmt_3_1\n"
    "87 not 1 69\n"
    "88 and 1 39 87\n"
    "89 ite 1 37 68 88 3:0:ADDI:3\n"
    "90 next 1 39 89 3:1:ADDI:3\n"
    "\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  init_statement_execution(true);

  verbose = false;
  encoder->add_statement_activation();
  verbose = true;

  ASSERT_EQ(
    "70 not 1 64\n"
    "71 and 1 29 70\n"
    "72 next 1 29 71\n"
    "\n"
    "73 not 1 65\n"
    "74 and 1 31 73\n"
    "75 ite 1 29 64 74\n"
    "76 next 1 31 75\n"
    "\n"
    "77 not 1 66\n"
    "78 and 1 33 77\n"
    "79 next 1 33 78\n"
    "\n"
    "80 not 1 67\n"
    "81 and 1 35 80\n"
    "82 ite 1 33 66 81\n"
    "83 next 1 35 82\n"
    "\n"
    "84 not 1 68\n"
    "85 and 1 37 84\n"
    "86 next 1 37 85\n"
    "\n"
    "87 not 1 69\n"
    "88 and 1 39 87\n"
    "89 ite 1 37 68 88\n"
    "90 next 1 39 89\n"
    "\n",
    encoder->formula.str());
}

TEST_F(Btor2EncoderTest, add_statement_activation_jmp)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("STORE", 1));
      programs[i]->push_back(Instruction::Set::create("JMP", 1));
      programs[i]->push_back(Instruction::Set::create("EXIT", 1));
    }

  reset_encoder(1);

  init_statement_execution(true);

  encoder->add_statement_activation();

  ASSERT_EQ(
    "; update statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_1_0\n"
    "86 not 1 74\n"
    "87 and 1 27 86\n"
    "88 next 1 27 87 1:0:ADDI:1\n"
    "\n"
    "; stmt_1_1\n"
    "89 not 1 75\n"
    "90 and 1 29 89\n"
    "91 ite 1 27 74 90 1:0:ADDI:1\n"
    "92 ite 1 31 76 91 1:2:JMP:1\n"
    "93 next 1 29 92 1:1:STORE:1\n"
    "\n"
    "; stmt_1_2\n"
    "94 not 1 76\n"
    "95 and 1 31 94\n"
    "96 ite 1 29 75 95 1:1:STORE:1\n"
    "97 next 1 31 96 1:2:JMP:1\n"
    "\n"
    "; stmt_1_3\n"
    "98 not 1 77\n"
    "99 and 1 33 98\n"
    "100 next 1 33 99 1:3:EXIT:1\n"
    "\n"
    "; stmt_2_0\n"
    "101 not 1 78\n"
    "102 and 1 35 101\n"
    "103 next 1 35 102 2:0:ADDI:1\n"
    "\n"
    "; stmt_2_1\n"
    "104 not 1 79\n"
    "105 and 1 37 104\n"
    "106 ite 1 35 78 105 2:0:ADDI:1\n"
    "107 ite 1 39 80 106 2:2:JMP:1\n"
    "108 next 1 37 107 2:1:STORE:1\n"
    "\n"
    "; stmt_2_2\n"
    "109 not 1 80\n"
    "110 and 1 39 109\n"
    "111 ite 1 37 79 110 2:1:STORE:1\n"
    "112 next 1 39 111 2:2:JMP:1\n"
    "\n"
    "; stmt_2_3\n"
    "113 not 1 81\n"
    "114 and 1 41 113\n"
    "115 next 1 41 114 2:3:EXIT:1\n"
    "\n"
    "; stmt_3_0\n"
    "116 not 1 82\n"
    "117 and 1 43 116\n"
    "118 next 1 43 117 3:0:ADDI:1\n"
    "\n"
    "; stmt_3_1\n"
    "119 not 1 83\n"
    "120 and 1 45 119\n"
    "121 ite 1 43 82 120 3:0:ADDI:1\n"
    "122 ite 1 47 84 121 3:2:JMP:1\n"
    "123 next 1 45 122 3:1:STORE:1\n"
    "\n"
    "; stmt_3_2\n"
    "124 not 1 84\n"
    "125 and 1 47 124\n"
    "126 ite 1 45 83 125 3:1:STORE:1\n"
    "127 next 1 47 126 3:2:JMP:1\n"
    "\n"
    "; stmt_3_3\n"
    "128 not 1 85\n"
    "129 and 1 49 128\n"
    "130 next 1 49 129 3:3:EXIT:1\n"
    "\n",
    encoder->formula.str());
}

TEST_F(Btor2EncoderTest, add_statement_activation_jmp_conditional)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("STORE", 1));
      programs[i]->push_back(Instruction::Set::create("JNZ", 1));
      programs[i]->push_back(Instruction::Set::create("EXIT", 1));
    }

  reset_encoder(3);

  init_statement_execution(true);

  encoder->add_statement_activation();

  ASSERT_EQ(vector<string>({"28", "30", "32", "34"}), encoder->nids_stmt[1]);
  ASSERT_EQ(vector<string>({"36", "38", "40", "42"}), encoder->nids_stmt[2]);
  ASSERT_EQ(vector<string>({"44", "46", "48", "50"}), encoder->nids_stmt[3]);

  ASSERT_EQ(vector<string>({"75", "76", "77", "78"}), encoder->nids_exec[1]);
  ASSERT_EQ(vector<string>({"79", "80", "81", "82"}), encoder->nids_exec[2]);
  ASSERT_EQ(vector<string>({"83", "84", "85", "86"}), encoder->nids_exec[3]);

  ASSERT_EQ(
    "; update statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_1_0\n"
    "87 not 1 75\n"
    "88 and 1 28 87\n"
    "89 next 1 28 88 1:0:ADDI:1\n"
    "\n"
    "; stmt_1_1\n"
    "90 not 1 76\n"
    "91 and 1 30 90\n"
    "92 ite 1 28 75 91 1:0:ADDI:1\n"
    "93 ne 1 16 6\n"
    "94 and 1 77 93\n"
    "95 ite 1 32 94 92 1:2:JNZ:1\n"
    "96 next 1 30 95 1:1:STORE:1\n"
    "\n"
    "; stmt_1_2\n"
    "97 not 1 77\n"
    "98 and 1 32 97\n"
    "99 ite 1 30 76 98 1:1:STORE:1\n"
    "100 next 1 32 99 1:2:JNZ:1\n"
    "\n"
    "; stmt_1_3\n"
    "101 not 1 78\n"
    "102 and 1 34 101\n"
    "103 not 1 93\n"
    "104 and 1 77 103\n"
    "105 ite 1 32 104 102 1:2:JNZ:1\n"
    "106 next 1 34 105 1:3:EXIT:1\n"
    "\n"
    "; stmt_2_0\n"
    "107 not 1 79\n"
    "108 and 1 36 107\n"
    "109 next 1 36 108 2:0:ADDI:1\n"
    "\n"
    "; stmt_2_1\n"
    "110 not 1 80\n"
    "111 and 1 38 110\n"
    "112 ite 1 36 79 111 2:0:ADDI:1\n"
    "113 ne 1 18 6\n"
    "114 and 1 81 113\n"
    "115 ite 1 40 114 112 2:2:JNZ:1\n"
    "116 next 1 38 115 2:1:STORE:1\n"
    "\n"
    "; stmt_2_2\n"
    "117 not 1 81\n"
    "118 and 1 40 117\n"
    "119 ite 1 38 80 118 2:1:STORE:1\n"
    "120 next 1 40 119 2:2:JNZ:1\n"
    "\n"
    "; stmt_2_3\n"
    "121 not 1 82\n"
    "122 and 1 42 121\n"
    "123 not 1 113\n"
    "124 and 1 81 123\n"
    "125 ite 1 40 124 122 2:2:JNZ:1\n"
    "126 next 1 42 125 2:3:EXIT:1\n"
    "\n"
    "; stmt_3_0\n"
    "127 not 1 83\n"
    "128 and 1 44 127\n"
    "129 next 1 44 128 3:0:ADDI:1\n"
    "\n"
    "; stmt_3_1\n"
    "130 not 1 84\n"
    "131 and 1 46 130\n"
    "132 ite 1 44 83 131 3:0:ADDI:1\n"
    "133 ne 1 20 6\n"
    "134 and 1 85 133\n"
    "135 ite 1 48 134 132 3:2:JNZ:1\n"
    "136 next 1 46 135 3:1:STORE:1\n"
    "\n"
    "; stmt_3_2\n"
    "137 not 1 85\n"
    "138 and 1 48 137\n"
    "139 ite 1 46 84 138 3:1:STORE:1\n"
    "140 next 1 48 139 3:2:JNZ:1\n"
    "\n"
    "; stmt_3_3\n"
    "141 not 1 86\n"
    "142 and 1 50 141\n"
    "143 not 1 133\n"
    "144 and 1 85 143\n"
    "145 ite 1 48 144 142 3:2:JNZ:1\n"
    "146 next 1 50 145 3:3:EXIT:1\n"
    "\n",
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

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("STORE", 1));
      programs[i]->push_back(Instruction::Set::create("JNZ", 0));
      programs[i]->push_back(Instruction::Set::create("EXIT", 1));
    }

  reset_encoder(3);

  init_statement_execution(true);

  encoder->add_statement_activation();

  ASSERT_EQ(vector<string>({"28", "30", "32", "34"}), encoder->nids_stmt[1]);
  ASSERT_EQ(vector<string>({"36", "38", "40", "42"}), encoder->nids_stmt[2]);
  ASSERT_EQ(vector<string>({"44", "46", "48", "50"}), encoder->nids_stmt[3]);

  ASSERT_EQ(vector<string>({"75", "76", "77", "78"}), encoder->nids_exec[1]);
  ASSERT_EQ(vector<string>({"79", "80", "81", "82"}), encoder->nids_exec[2]);
  ASSERT_EQ(vector<string>({"83", "84", "85", "86"}), encoder->nids_exec[3]);

  ASSERT_EQ(
    "; update statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_1_0\n"
    "87 not 1 75\n"
    "88 and 1 28 87\n"
    "89 ne 1 16 6\n"
    "90 and 1 77 89\n"
    "91 ite 1 32 90 88 1:2:JNZ:0\n"
    "92 next 1 28 91 1:0:ADDI:1\n"
    "\n"
    "; stmt_1_1\n"
    "93 not 1 76\n"
    "94 and 1 30 93\n"
    "95 ite 1 28 75 94 1:0:ADDI:1\n"
    "96 next 1 30 95 1:1:STORE:1\n"
    "\n"
    "; stmt_1_2\n"
    "97 not 1 77\n"
    "98 and 1 32 97\n"
    "99 ite 1 30 76 98 1:1:STORE:1\n"
    "100 next 1 32 99 1:2:JNZ:0\n"
    "\n"
    "; stmt_1_3\n"
    "101 not 1 78\n"
    "102 and 1 34 101\n"
    "103 not 1 89\n"
    "104 and 1 77 103\n"
    "105 ite 1 32 104 102 1:2:JNZ:0\n"
    "106 next 1 34 105 1:3:EXIT:1\n"
    "\n"
    "; stmt_2_0\n"
    "107 not 1 79\n"
    "108 and 1 36 107\n"
    "109 ne 1 18 6\n"
    "110 and 1 81 109\n"
    "111 ite 1 40 110 108 2:2:JNZ:0\n"
    "112 next 1 36 111 2:0:ADDI:1\n"
    "\n"
    "; stmt_2_1\n"
    "113 not 1 80\n"
    "114 and 1 38 113\n"
    "115 ite 1 36 79 114 2:0:ADDI:1\n"
    "116 next 1 38 115 2:1:STORE:1\n"
    "\n"
    "; stmt_2_2\n"
    "117 not 1 81\n"
    "118 and 1 40 117\n"
    "119 ite 1 38 80 118 2:1:STORE:1\n"
    "120 next 1 40 119 2:2:JNZ:0\n"
    "\n"
    "; stmt_2_3\n"
    "121 not 1 82\n"
    "122 and 1 42 121\n"
    "123 not 1 109\n"
    "124 and 1 81 123\n"
    "125 ite 1 40 124 122 2:2:JNZ:0\n"
    "126 next 1 42 125 2:3:EXIT:1\n"
    "\n"
    "; stmt_3_0\n"
    "127 not 1 83\n"
    "128 and 1 44 127\n"
    "129 ne 1 20 6\n"
    "130 and 1 85 129\n"
    "131 ite 1 48 130 128 3:2:JNZ:0\n"
    "132 next 1 44 131 3:0:ADDI:1\n"
    "\n"
    "; stmt_3_1\n"
    "133 not 1 84\n"
    "134 and 1 46 133\n"
    "135 ite 1 44 83 134 3:0:ADDI:1\n"
    "136 next 1 46 135 3:1:STORE:1\n"
    "\n"
    "; stmt_3_2\n"
    "137 not 1 85\n"
    "138 and 1 48 137\n"
    "139 ite 1 46 84 138 3:1:STORE:1\n"
    "140 next 1 48 139 3:2:JNZ:0\n"
    "\n"
    "; stmt_3_3\n"
    "141 not 1 86\n"
    "142 and 1 50 141\n"
    "143 not 1 129\n"
    "144 and 1 85 143\n"
    "145 ite 1 48 144 142 3:2:JNZ:0\n"
    "146 next 1 50 145 3:3:EXIT:1\n"
    "\n",
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

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("STORE", 1));
      programs[i]->push_back(Instruction::Set::create("JZ", 1));
      programs[i]->push_back(Instruction::Set::create("JNZ", 1));
      programs[i]->push_back(Instruction::Set::create("EXIT", 1));
    }

  reset_encoder(3);

  init_statement_execution(true);

  encoder->add_statement_activation();

  ASSERT_EQ(vector<string>({"28", "30", "32", "34", "36"}), encoder->nids_stmt[1]);
  ASSERT_EQ(vector<string>({"38", "40", "42", "44", "46"}), encoder->nids_stmt[2]);
  ASSERT_EQ(vector<string>({"48", "50", "52", "54", "56"}), encoder->nids_stmt[3]);

  ASSERT_EQ(vector<string>({"81", "82", "83", "84", "85"}), encoder->nids_exec[1]);
  ASSERT_EQ(vector<string>({"86", "87", "88", "89", "90"}), encoder->nids_exec[2]);
  ASSERT_EQ(vector<string>({"91", "92", "93", "94", "95"}), encoder->nids_exec[3]);

  ASSERT_EQ(
    "; update statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_1_0\n"
    "96 not 1 81\n"
    "97 and 1 28 96\n"
    "98 next 1 28 97 1:0:ADDI:1\n"
    "\n"
    "; stmt_1_1\n"
    "99 not 1 82\n"
    "100 and 1 30 99\n"
    "101 ite 1 28 81 100 1:0:ADDI:1\n"
    "102 eq 1 16 6\n"
    "103 and 1 83 102\n"
    "104 ite 1 32 103 101 1:2:JZ:1\n"
    "105 ne 1 16 6\n"
    "106 and 1 84 105\n"
    "107 ite 1 34 106 104 1:3:JNZ:1\n"
    "108 next 1 30 107 1:1:STORE:1\n"
    "\n"
    "; stmt_1_2\n"
    "109 not 1 83\n"
    "110 and 1 32 109\n"
    "111 ite 1 30 82 110 1:1:STORE:1\n"
    "112 next 1 32 111 1:2:JZ:1\n"
    "\n"
    "; stmt_1_3\n"
    "113 not 1 84\n"
    "114 and 1 34 113\n"
    "115 not 1 102\n"
    "116 and 1 83 115\n"
    "117 ite 1 32 116 114 1:2:JZ:1\n"
    "118 next 1 34 117 1:3:JNZ:1\n"
    "\n"
    "; stmt_1_4\n"
    "119 not 1 85\n"
    "120 and 1 36 119\n"
    "121 not 1 105\n"
    "122 and 1 84 121\n"
    "123 ite 1 34 122 120 1:3:JNZ:1\n"
    "124 next 1 36 123 1:4:EXIT:1\n"
    "\n"
    "; stmt_2_0\n"
    "125 not 1 86\n"
    "126 and 1 38 125\n"
    "127 next 1 38 126 2:0:ADDI:1\n"
    "\n"
    "; stmt_2_1\n"
    "128 not 1 87\n"
    "129 and 1 40 128\n"
    "130 ite 1 38 86 129 2:0:ADDI:1\n"
    "131 eq 1 18 6\n"
    "132 and 1 88 131\n"
    "133 ite 1 42 132 130 2:2:JZ:1\n"
    "134 ne 1 18 6\n"
    "135 and 1 89 134\n"
    "136 ite 1 44 135 133 2:3:JNZ:1\n"
    "137 next 1 40 136 2:1:STORE:1\n"
    "\n"
    "; stmt_2_2\n"
    "138 not 1 88\n"
    "139 and 1 42 138\n"
    "140 ite 1 40 87 139 2:1:STORE:1\n"
    "141 next 1 42 140 2:2:JZ:1\n"
    "\n"
    "; stmt_2_3\n"
    "142 not 1 89\n"
    "143 and 1 44 142\n"
    "144 not 1 131\n"
    "145 and 1 88 144\n"
    "146 ite 1 42 145 143 2:2:JZ:1\n"
    "147 next 1 44 146 2:3:JNZ:1\n"
    "\n"
    "; stmt_2_4\n"
    "148 not 1 90\n"
    "149 and 1 46 148\n"
    "150 not 1 134\n"
    "151 and 1 89 150\n"
    "152 ite 1 44 151 149 2:3:JNZ:1\n"
    "153 next 1 46 152 2:4:EXIT:1\n"
    "\n"
    "; stmt_3_0\n"
    "154 not 1 91\n"
    "155 and 1 48 154\n"
    "156 next 1 48 155 3:0:ADDI:1\n"
    "\n"
    "; stmt_3_1\n"
    "157 not 1 92\n"
    "158 and 1 50 157\n"
    "159 ite 1 48 91 158 3:0:ADDI:1\n"
    "160 eq 1 20 6\n"
    "161 and 1 93 160\n"
    "162 ite 1 52 161 159 3:2:JZ:1\n"
    "163 ne 1 20 6\n"
    "164 and 1 94 163\n"
    "165 ite 1 54 164 162 3:3:JNZ:1\n"
    "166 next 1 50 165 3:1:STORE:1\n"
    "\n"
    "; stmt_3_2\n"
    "167 not 1 93\n"
    "168 and 1 52 167\n"
    "169 ite 1 50 92 168 3:1:STORE:1\n"
    "170 next 1 52 169 3:2:JZ:1\n"
    "\n"
    "; stmt_3_3\n"
    "171 not 1 94\n"
    "172 and 1 54 171\n"
    "173 not 1 160\n"
    "174 and 1 93 173\n"
    "175 ite 1 52 174 172 3:2:JZ:1\n"
    "176 next 1 54 175 3:3:JNZ:1\n"
    "\n"
    "; stmt_3_4\n"
    "177 not 1 95\n"
    "178 and 1 56 177\n"
    "179 not 1 163\n"
    "180 and 1 94 179\n"
    "181 ite 1 54 180 178 3:3:JNZ:1\n"
    "182 next 1 56 181 3:4:EXIT:1\n"
    "\n",
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
  string sid = encoder->sid_bv;
  string sym = "state";
  unordered_map<word, vector<word>> alters_state({
    {1, {0, 1, 2}},
    {2, {0, 1, 2}},
    {3, {0, 1, 2}}
  });

  /* thread states */
  for (encoder->thread = 1; encoder->thread <= 3; encoder->thread++)
    {
      encoder->add_state_update(state, sid, sym, alters_state);

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
        + nid_0_addi + " add " + sid + " " + accu + " " + arg + "\n"
        + nid_0_ite  + " ite " + sid + " " + exec[0] + " " + nid_0_addi + " " + state + " " + thread + ":0:ADDI:" + thread + "\n"
        + nid_1_addi + " add " + sid + " " + accu + " " + arg + "\n"
        + nid_1_ite  + " ite " + sid + " " + exec[1] + " " + nid_1_addi + " " + nid_0_ite + " " + thread + ":1:ADDI:" + thread + "\n"
        + nid_2_addi + " add " + sid + " " + accu + " " + arg + "\n"
        + nid_2_ite  + " ite " + sid + " " + exec[2] + " " + nid_2_addi + " " + nid_1_ite + " " + thread + ":2:ADDI:" + thread + "\n"
        + nid_next   + " next " + sid + " " + state + " " + nid_2_ite + "\n"
        "\n",
        encoder->formula.str());

      encoder->formula.str("");
    }

  /* global state */
  reset_encoder(1);

  init_statement_activation(true);

  encoder->thread = 0;

  encoder->add_state_update(state, sid, sym, alters_state);

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
      nid_1_0_addi + " add " + sid + " " + encoder->nids_accu[1] + " 7\n"
    + nid_1_0_ite  + " ite " + sid + " " + encoder->nids_exec[1][0] + " " + nid_1_0_addi + " " + state + " 1:0:ADDI:1\n"
    + nid_1_1_addi + " add " + sid + " " + encoder->nids_accu[1] + " 7\n"
    + nid_1_1_ite  + " ite " + sid + " " + encoder->nids_exec[1][1] + " " + nid_1_1_addi + " " + nid_1_0_ite + " 1:1:ADDI:1\n"
    + nid_1_2_addi + " add " + sid + " " + encoder->nids_accu[1] + " 7\n"
    + nid_1_2_ite  + " ite " + sid + " " + encoder->nids_exec[1][2] + " " + nid_1_2_addi + " " + nid_1_1_ite + " 1:2:ADDI:1\n"

    + nid_2_0_addi + " add " + sid + " " + encoder->nids_accu[2] + " 8\n"
    + nid_2_0_ite  + " ite " + sid + " " + encoder->nids_exec[2][0] + " " + nid_2_0_addi + " " + nid_1_2_ite + " 2:0:ADDI:2\n"
    + nid_2_1_addi + " add " + sid + " " + encoder->nids_accu[2] + " 8\n"
    + nid_2_1_ite  + " ite " + sid + " " + encoder->nids_exec[2][1] + " " + nid_2_1_addi + " " + nid_2_0_ite + " 2:1:ADDI:2\n"
    + nid_2_2_addi + " add " + sid + " " + encoder->nids_accu[2] + " 8\n"
    + nid_2_2_ite  + " ite " + sid + " " + encoder->nids_exec[2][2] + " " + nid_2_2_addi + " " + nid_2_1_ite + " 2:2:ADDI:2\n"

    + nid_3_0_addi + " add " + sid + " " + encoder->nids_accu[3] + " 9\n"
    + nid_3_0_ite  + " ite " + sid + " " + encoder->nids_exec[3][0] + " " + nid_3_0_addi + " " + nid_2_2_ite + " 3:0:ADDI:3\n"
    + nid_3_1_addi + " add " + sid + " " + encoder->nids_accu[3] + " 9\n"
    + nid_3_1_ite  + " ite " + sid + " " + encoder->nids_exec[3][1] + " " + nid_3_1_addi + " " + nid_3_0_ite + " 3:1:ADDI:3\n"
    + nid_3_2_addi + " add " + sid + " " + encoder->nids_accu[3] + " 9\n"
    + nid_3_2_ite  + " ite " + sid + " " + encoder->nids_exec[3][2] + " " + nid_3_2_addi + " " + nid_3_1_ite + " 3:2:ADDI:3\n"

    + nid_next + " next " + sid + " " + state + " " + nid_3_2_ite + "\n"
    "\n",
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
        + nid_0_ite  + " ite 2 " + exec[0] + " 509 " + accu + " " + thread + ":0:LOAD:1\n"
        + nid_2_add  + " add 2 " + accu + " 509\n"
        + nid_2_ite  + " ite 2 " + exec[2] + " " + nid_2_add + " " + nid_0_ite + " " + thread + ":2:ADD:1\n"
        + nid_3_addi + " add 2 " + accu + " 7\n"
        + nid_3_ite  + " ite 2 " + exec[3] + " " + nid_3_addi + " " + nid_2_ite + " " + thread + ":3:ADDI:1\n"
        + nid_4_sub  + " sub 2 " + accu + " 509\n"
        + nid_4_ite  + " ite 2 " + exec[4] + " " + nid_4_sub + " " + nid_3_ite + " " + thread + ":4:SUB:1\n"
        + nid_5_subi + " sub 2 " + accu + " 7\n"
        + nid_5_ite  + " ite 2 " + exec[5] + " " + nid_5_subi + " " + nid_4_ite + " " + thread + ":5:SUBI:1\n"
        + nid_6_cmp  + " sub 2 " + accu + " 509\n"
        + nid_6_ite  + " ite 2 " + exec[6] + " " + nid_6_cmp + " " + nid_5_ite + " " + thread + ":6:CMP:1\n"
        + nid_13_mem + " ite 2 " + exec[13] + " 509 " + nid_6_ite + " " + thread + ":13:MEM:1\n"
        + nid_14_eq  + " eq 1 "  + encoder->nids_mem[encoder->thread] + " 509\n"
        + nid_14_cas + " ite 2 " + nid_14_eq + " 7 6\n"
        + nid_14_ite + " ite 2 " + exec[14] + " " + nid_14_cas + " " + nid_13_mem + " " + thread + ":14:CAS:1\n"
        + nid_next   + " next 2 " + accu + " " + nid_14_ite + "\n"
        "\n";
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
        + nid_13_ite + " ite 2 " + exec[13] + " 509 " + mem + " " + thread + ":13:MEM:1\n"
        + nid_next + " next 2 " + mem + " " + nid_13_ite + "\n"
        "\n";
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

  string nid_1_write  = nid(-17);
  string nid_1_1_ite  = nid(-16);
  string nid_read     = nid(-15);
  string nid_1_14_eq  = nid(-14);
  string nid_1_14_cas = nid(-13);
  string nid_1_14_ite = nid(-12);

  string nid_2_write  = nid(-11);
  string nid_2_1_ite  = nid(-10);
  string nid_2_14_eq  = nid(-9);
  string nid_2_14_cas = nid(-8);
  string nid_2_14_ite = nid(-7);

  string nid_3_write  = nid(-6);
  string nid_3_1_ite  = nid(-5);
  string nid_3_14_eq  = nid(-4);
  string nid_3_14_cas = nid(-3);
  string nid_3_14_ite = nid(-2);

  string nid_next     = nid(-1);

  ASSERT_EQ(
    "; update heap ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n"

    + nid_1_write  + " write 3 " + encoder->nid_heap + " " + encoder->nids_const[1] + " " + encoder->nids_accu[1] + "\n"
    + nid_1_1_ite  + " ite 3 " + encoder->nids_exec[1][1] + " " + nid_1_write + " " + encoder->nid_heap + " 1:1:STORE:1\n"
    + nid_read     + " read 2 " + encoder->nid_heap + " " + encoder->nids_const[1] + "\n"
    + nid_1_14_eq  + " eq 1 "  + encoder->nids_mem[1] + " " + nid_read + "\n"
    + nid_1_14_cas + " ite 3 " + nid_1_14_eq + " " + nid_1_write + " " + encoder->nid_heap + "\n"
    + nid_1_14_ite + " ite 3 " + encoder->nids_exec[1][14] + " " + nid_1_14_cas + " " + nid_1_1_ite + " 1:14:CAS:1\n"

    + nid_2_write  + " write 3 " + encoder->nid_heap + " " + encoder->nids_const[1] + " " + encoder->nids_accu[2] + "\n"
    + nid_2_1_ite  + " ite 3 " + encoder->nids_exec[2][1] + " " + nid_2_write + " " + nid_1_14_ite + " 2:1:STORE:1\n"
    + nid_2_14_eq  + " eq 1 "  + encoder->nids_mem[2] + " " + nid_read + "\n"
    + nid_2_14_cas + " ite 3 " + nid_2_14_eq + " " + nid_2_write + " " + encoder->nid_heap + "\n"
    + nid_2_14_ite + " ite 3 " + encoder->nids_exec[2][14] + " " + nid_2_14_cas + " " + nid_2_1_ite + " 2:14:CAS:1\n"

    + nid_3_write  + " write 3 " + encoder->nid_heap + " " + encoder->nids_const[1] + " " + encoder->nids_accu[3] + "\n"
    + nid_3_1_ite  + " ite 3 " + encoder->nids_exec[3][1] + " " + nid_3_write + " " + nid_2_14_ite + " 3:1:STORE:1\n"
    + nid_3_14_eq  + " eq 1 "  + encoder->nids_mem[3] + " " + nid_read + "\n"
    + nid_3_14_cas + " ite 3 " + nid_3_14_eq + " " + nid_3_write + " " + encoder->nid_heap + "\n"
    + nid_3_14_ite + " ite 3 " + encoder->nids_exec[3][14] + " " + nid_3_14_cas + " " + nid_3_1_ite + " 3:14:CAS:1\n"

    + nid_next     + " next 3 14 " + nid_3_14_ite + "\n"
    "\n",
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

TEST_F(Btor2EncoderTest, add_exit_flag_update_no_exit)
{
  add_dummy_programs(3, 3);

  init_statement_activation(true);

  encoder->add_exit_flag_update();

  ASSERT_EQ(
    "; update exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    + nid(-1) + " next 1 " + encoder->nid_exit + " " + encoder->nid_exit + "\n"
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
    + nid_ite_1 + " ite 2 " + encoder->nids_exec[1][16] + " " + nid_one + " " + encoder->nid_exit_code + " 1:16:EXIT:1\n"
    + nid_ite_2 + " ite 2 " + encoder->nids_exec[2][16] + " " + nid_one + " " + nid_ite_1 + " 2:16:EXIT:1\n"
    + nid_ite_3 + " ite 2 " + encoder->nids_exec[3][16] + " " + nid_one + " " + nid_ite_2 + " 3:16:EXIT:1\n"
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
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; state updates\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; update statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_1_0\n"
    "509 not 1 167\n"
    "510 and 1 27 509\n"
    "511 next 1 27 510 1:0:LOAD:1\n"
    "\n"
    "; stmt_1_1\n"
    "512 not 1 168\n"
    "513 and 1 29 512\n"
    "514 ite 1 27 167 513 1:0:LOAD:1\n"
    "515 ite 1 41 174 514 1:7:JMP:1\n"
    "516 eq 1 15 6\n"
    "517 and 1 175 516\n"
    "518 ite 1 43 517 515 1:8:JZ:1\n"
    "519 ne 1 15 6\n"
    "520 and 1 176 519\n"
    "521 ite 1 45 520 518 1:9:JNZ:1\n"
    "522 slice 1 15 15 15\n"
    "523 and 1 177 522\n"
    "524 ite 1 47 523 521 1:10:JS:1\n"
    "525 slice 1 15 15 15\n"
    "526 not 1 525\n"
    "527 and 1 178 526\n"
    "528 ite 1 49 527 524 1:11:JNS:1\n"
    "530 ne 1 15 6\n"
    "531 slice 1 15 15 15\n"
    "532 not 1 531\n"
    "533 and 1 530 532\n"
    "534 and 1 179 533\n"
    "535 ite 1 51 534 528 1:12:JNZNS:1\n"
    "536 next 1 29 535 1:1:STORE:1\n"
    "\n"
    "; stmt_1_2\n"
    "537 not 1 169\n"
    "538 and 1 31 537\n"
    "539 ite 1 29 168 538 1:1:STORE:1\n"
    "540 next 1 31 539 1:2:ADD:1\n"
    "\n"
    "; stmt_1_3\n"
    "541 not 1 170\n"
    "542 and 1 33 541\n"
    "543 ite 1 31 169 542 1:2:ADD:1\n"
    "544 next 1 33 543 1:3:ADDI:1\n"
    "\n"
    "; stmt_1_4\n"
    "545 not 1 171\n"
    "546 and 1 35 545\n"
    "547 ite 1 33 170 546 1:3:ADDI:1\n"
    "548 next 1 35 547 1:4:SUB:1\n"
    "\n"
    "; stmt_1_5\n"
    "549 not 1 172\n"
    "550 and 1 37 549\n"
    "551 ite 1 35 171 550 1:4:SUB:1\n"
    "552 next 1 37 551 1:5:SUBI:1\n"
    "\n"
    "; stmt_1_6\n"
    "553 not 1 173\n"
    "554 and 1 39 553\n"
    "555 ite 1 37 172 554 1:5:SUBI:1\n"
    "556 next 1 39 555 1:6:CMP:1\n"
    "\n"
    "; stmt_1_7\n"
    "557 not 1 174\n"
    "558 and 1 41 557\n"
    "559 ite 1 39 173 558 1:6:CMP:1\n"
    "560 next 1 41 559 1:7:JMP:1\n"
    "\n"
    "; stmt_1_8\n"
    "561 not 1 175\n"
    "562 and 1 43 561\n"
    "563 next 1 43 562 1:8:JZ:1\n"
    "\n"
    "; stmt_1_9\n"
    "564 not 1 176\n"
    "565 and 1 45 564\n"
    "566 not 1 516\n"
    "567 and 1 175 566\n"
    "568 ite 1 43 567 565 1:8:JZ:1\n"
    "569 next 1 45 568 1:9:JNZ:1\n"
    "\n"
    "; stmt_1_10\n"
    "570 not 1 177\n"
    "571 and 1 47 570\n"
    "572 not 1 519\n"
    "573 and 1 176 572\n"
    "574 ite 1 45 573 571 1:9:JNZ:1\n"
    "575 next 1 47 574 1:10:JS:1\n"
    "\n"
    "; stmt_1_11\n"
    "576 not 1 178\n"
    "577 and 1 49 576\n"
    "578 not 1 522\n"
    "579 and 1 177 578\n"
    "580 ite 1 47 579 577 1:10:JS:1\n"
    "581 next 1 49 580 1:11:JNS:1\n"
    "\n"
    "; stmt_1_12\n"
    "582 not 1 179\n"
    "583 and 1 51 582\n"
    "584 not 1 526\n"
    "585 and 1 178 584\n"
    "586 ite 1 49 585 583 1:11:JNS:1\n"
    "587 next 1 51 586 1:12:JNZNS:1\n"
    "\n"
    "; stmt_1_13\n"
    "588 not 1 180\n"
    "589 and 1 53 588\n"
    "590 not 1 533\n"
    "591 and 1 179 590\n"
    "592 ite 1 51 591 589 1:12:JNZNS:1\n"
    "593 next 1 53 592 1:13:MEM:1\n"
    "\n"
    "; stmt_1_14\n"
    "594 not 1 181\n"
    "595 and 1 55 594\n"
    "596 ite 1 53 180 595 1:13:MEM:1\n"
    "597 next 1 55 596 1:14:CAS:1\n"
    "\n"
    "; stmt_1_15\n"
    "598 not 1 182\n"
    "599 and 1 57 598\n"
    "600 ite 1 55 181 599 1:14:CAS:1\n"
    "601 next 1 57 600 1:15:SYNC:1\n"
    "\n"
    "; stmt_1_16\n"
    "602 not 1 183\n"
    "603 and 1 59 602\n"
    "604 ite 1 57 182 603 1:15:SYNC:1\n"
    "605 next 1 59 604 1:16:EXIT:1\n"
    "\n"
    "; stmt_2_0\n"
    "606 not 1 184\n"
    "607 and 1 61 606\n"
    "608 next 1 61 607 2:0:LOAD:1\n"
    "\n"
    "; stmt_2_1\n"
    "609 not 1 185\n"
    "610 and 1 63 609\n"
    "611 ite 1 61 184 610 2:0:LOAD:1\n"
    "612 ite 1 75 191 611 2:7:JMP:1\n"
    "613 eq 1 17 6\n"
    "614 and 1 192 613\n"
    "615 ite 1 77 614 612 2:8:JZ:1\n"
    "616 ne 1 17 6\n"
    "617 and 1 193 616\n"
    "618 ite 1 79 617 615 2:9:JNZ:1\n"
    "619 slice 1 17 15 15\n"
    "620 and 1 194 619\n"
    "621 ite 1 81 620 618 2:10:JS:1\n"
    "622 slice 1 17 15 15\n"
    "623 not 1 622\n"
    "624 and 1 195 623\n"
    "625 ite 1 83 624 621 2:11:JNS:1\n"
    "627 ne 1 17 6\n"
    "628 slice 1 17 15 15\n"
    "629 not 1 628\n"
    "630 and 1 627 629\n"
    "631 and 1 196 630\n"
    "632 ite 1 85 631 625 2:12:JNZNS:1\n"
    "633 next 1 63 632 2:1:STORE:1\n"
    "\n"
    "; stmt_2_2\n"
    "634 not 1 186\n"
    "635 and 1 65 634\n"
    "636 ite 1 63 185 635 2:1:STORE:1\n"
    "637 next 1 65 636 2:2:ADD:1\n"
    "\n"
    "; stmt_2_3\n"
    "638 not 1 187\n"
    "639 and 1 67 638\n"
    "640 ite 1 65 186 639 2:2:ADD:1\n"
    "641 next 1 67 640 2:3:ADDI:1\n"
    "\n"
    "; stmt_2_4\n"
    "642 not 1 188\n"
    "643 and 1 69 642\n"
    "644 ite 1 67 187 643 2:3:ADDI:1\n"
    "645 next 1 69 644 2:4:SUB:1\n"
    "\n"
    "; stmt_2_5\n"
    "646 not 1 189\n"
    "647 and 1 71 646\n"
    "648 ite 1 69 188 647 2:4:SUB:1\n"
    "649 next 1 71 648 2:5:SUBI:1\n"
    "\n"
    "; stmt_2_6\n"
    "650 not 1 190\n"
    "651 and 1 73 650\n"
    "652 ite 1 71 189 651 2:5:SUBI:1\n"
    "653 next 1 73 652 2:6:CMP:1\n"
    "\n"
    "; stmt_2_7\n"
    "654 not 1 191\n"
    "655 and 1 75 654\n"
    "656 ite 1 73 190 655 2:6:CMP:1\n"
    "657 next 1 75 656 2:7:JMP:1\n"
    "\n"
    "; stmt_2_8\n"
    "658 not 1 192\n"
    "659 and 1 77 658\n"
    "660 next 1 77 659 2:8:JZ:1\n"
    "\n"
    "; stmt_2_9\n"
    "661 not 1 193\n"
    "662 and 1 79 661\n"
    "663 not 1 613\n"
    "664 and 1 192 663\n"
    "665 ite 1 77 664 662 2:8:JZ:1\n"
    "666 next 1 79 665 2:9:JNZ:1\n"
    "\n"
    "; stmt_2_10\n"
    "667 not 1 194\n"
    "668 and 1 81 667\n"
    "669 not 1 616\n"
    "670 and 1 193 669\n"
    "671 ite 1 79 670 668 2:9:JNZ:1\n"
    "672 next 1 81 671 2:10:JS:1\n"
    "\n"
    "; stmt_2_11\n"
    "673 not 1 195\n"
    "674 and 1 83 673\n"
    "675 not 1 619\n"
    "676 and 1 194 675\n"
    "677 ite 1 81 676 674 2:10:JS:1\n"
    "678 next 1 83 677 2:11:JNS:1\n"
    "\n"
    "; stmt_2_12\n"
    "679 not 1 196\n"
    "680 and 1 85 679\n"
    "681 not 1 623\n"
    "682 and 1 195 681\n"
    "683 ite 1 83 682 680 2:11:JNS:1\n"
    "684 next 1 85 683 2:12:JNZNS:1\n"
    "\n"
    "; stmt_2_13\n"
    "685 not 1 197\n"
    "686 and 1 87 685\n"
    "687 not 1 630\n"
    "688 and 1 196 687\n"
    "689 ite 1 85 688 686 2:12:JNZNS:1\n"
    "690 next 1 87 689 2:13:MEM:1\n"
    "\n"
    "; stmt_2_14\n"
    "691 not 1 198\n"
    "692 and 1 89 691\n"
    "693 ite 1 87 197 692 2:13:MEM:1\n"
    "694 next 1 89 693 2:14:CAS:1\n"
    "\n"
    "; stmt_2_15\n"
    "695 not 1 199\n"
    "696 and 1 91 695\n"
    "697 ite 1 89 198 696 2:14:CAS:1\n"
    "698 next 1 91 697 2:15:SYNC:1\n"
    "\n"
    "; stmt_2_16\n"
    "699 not 1 200\n"
    "700 and 1 93 699\n"
    "701 ite 1 91 199 700 2:15:SYNC:1\n"
    "702 next 1 93 701 2:16:EXIT:1\n"
    "\n"
    "; stmt_3_0\n"
    "703 not 1 201\n"
    "704 and 1 95 703\n"
    "705 next 1 95 704 3:0:LOAD:1\n"
    "\n"
    "; stmt_3_1\n"
    "706 not 1 202\n"
    "707 and 1 97 706\n"
    "708 ite 1 95 201 707 3:0:LOAD:1\n"
    "709 ite 1 109 208 708 3:7:JMP:1\n"
    "710 eq 1 19 6\n"
    "711 and 1 209 710\n"
    "712 ite 1 111 711 709 3:8:JZ:1\n"
    "713 ne 1 19 6\n"
    "714 and 1 210 713\n"
    "715 ite 1 113 714 712 3:9:JNZ:1\n"
    "716 slice 1 19 15 15\n"
    "717 and 1 211 716\n"
    "718 ite 1 115 717 715 3:10:JS:1\n"
    "719 slice 1 19 15 15\n"
    "720 not 1 719\n"
    "721 and 1 212 720\n"
    "722 ite 1 117 721 718 3:11:JNS:1\n"
    "724 ne 1 19 6\n"
    "725 slice 1 19 15 15\n"
    "726 not 1 725\n"
    "727 and 1 724 726\n"
    "728 and 1 213 727\n"
    "729 ite 1 119 728 722 3:12:JNZNS:1\n"
    "730 next 1 97 729 3:1:STORE:1\n"
    "\n"
    "; stmt_3_2\n"
    "731 not 1 203\n"
    "732 and 1 99 731\n"
    "733 ite 1 97 202 732 3:1:STORE:1\n"
    "734 next 1 99 733 3:2:ADD:1\n"
    "\n"
    "; stmt_3_3\n"
    "735 not 1 204\n"
    "736 and 1 101 735\n"
    "737 ite 1 99 203 736 3:2:ADD:1\n"
    "738 next 1 101 737 3:3:ADDI:1\n"
    "\n"
    "; stmt_3_4\n"
    "739 not 1 205\n"
    "740 and 1 103 739\n"
    "741 ite 1 101 204 740 3:3:ADDI:1\n"
    "742 next 1 103 741 3:4:SUB:1\n"
    "\n"
    "; stmt_3_5\n"
    "743 not 1 206\n"
    "744 and 1 105 743\n"
    "745 ite 1 103 205 744 3:4:SUB:1\n"
    "746 next 1 105 745 3:5:SUBI:1\n"
    "\n"
    "; stmt_3_6\n"
    "747 not 1 207\n"
    "748 and 1 107 747\n"
    "749 ite 1 105 206 748 3:5:SUBI:1\n"
    "750 next 1 107 749 3:6:CMP:1\n"
    "\n"
    "; stmt_3_7\n"
    "751 not 1 208\n"
    "752 and 1 109 751\n"
    "753 ite 1 107 207 752 3:6:CMP:1\n"
    "754 next 1 109 753 3:7:JMP:1\n"
    "\n"
    "; stmt_3_8\n"
    "755 not 1 209\n"
    "756 and 1 111 755\n"
    "757 next 1 111 756 3:8:JZ:1\n"
    "\n"
    "; stmt_3_9\n"
    "758 not 1 210\n"
    "759 and 1 113 758\n"
    "760 not 1 710\n"
    "761 and 1 209 760\n"
    "762 ite 1 111 761 759 3:8:JZ:1\n"
    "763 next 1 113 762 3:9:JNZ:1\n"
    "\n"
    "; stmt_3_10\n"
    "764 not 1 211\n"
    "765 and 1 115 764\n"
    "766 not 1 713\n"
    "767 and 1 210 766\n"
    "768 ite 1 113 767 765 3:9:JNZ:1\n"
    "769 next 1 115 768 3:10:JS:1\n"
    "\n"
    "; stmt_3_11\n"
    "770 not 1 212\n"
    "771 and 1 117 770\n"
    "772 not 1 716\n"
    "773 and 1 211 772\n"
    "774 ite 1 115 773 771 3:10:JS:1\n"
    "775 next 1 117 774 3:11:JNS:1\n"
    "\n"
    "; stmt_3_12\n"
    "776 not 1 213\n"
    "777 and 1 119 776\n"
    "778 not 1 720\n"
    "779 and 1 212 778\n"
    "780 ite 1 117 779 777 3:11:JNS:1\n"
    "781 next 1 119 780 3:12:JNZNS:1\n"
    "\n"
    "; stmt_3_13\n"
    "782 not 1 214\n"
    "783 and 1 121 782\n"
    "784 not 1 727\n"
    "785 and 1 213 784\n"
    "786 ite 1 119 785 783 3:12:JNZNS:1\n"
    "787 next 1 121 786 3:13:MEM:1\n"
    "\n"
    "; stmt_3_14\n"
    "788 not 1 215\n"
    "789 and 1 123 788\n"
    "790 ite 1 121 214 789 3:13:MEM:1\n"
    "791 next 1 123 790 3:14:CAS:1\n"
    "\n"
    "; stmt_3_15\n"
    "792 not 1 216\n"
    "793 and 1 125 792\n"
    "794 ite 1 123 215 793 3:14:CAS:1\n"
    "795 next 1 125 794 3:15:SYNC:1\n"
    "\n"
    "; stmt_3_16\n"
    "796 not 1 217\n"
    "797 and 1 127 796\n"
    "798 ite 1 125 216 797 3:15:SYNC:1\n"
    "799 next 1 127 798 3:16:EXIT:1\n"
    "\n"
    "; update accu ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu_1\n"
    "800 read 2 14 7\n"
    "801 ite 2 167 800 15 1:0:LOAD:1\n"
    "802 add 2 15 800\n"
    "803 ite 2 169 802 801 1:2:ADD:1\n"
    "804 add 2 15 7\n"
    "805 ite 2 170 804 803 1:3:ADDI:1\n"
    "806 sub 2 15 800\n"
    "807 ite 2 171 806 805 1:4:SUB:1\n"
    "808 sub 2 15 7\n"
    "809 ite 2 172 808 807 1:5:SUBI:1\n"
    "810 sub 2 15 800\n"
    "811 ite 2 173 810 809 1:6:CMP:1\n"
    "812 ite 2 180 800 811 1:13:MEM:1\n"
    "813 eq 1 21 800\n"
    "814 ite 2 813 7 6\n"
    "815 ite 2 181 814 812 1:14:CAS:1\n"
    "816 next 2 15 815\n"
    "\n"
    "; accu_2\n"
    "817 ite 2 184 800 17 2:0:LOAD:1\n"
    "818 add 2 17 800\n"
    "819 ite 2 186 818 817 2:2:ADD:1\n"
    "820 add 2 17 7\n"
    "821 ite 2 187 820 819 2:3:ADDI:1\n"
    "822 sub 2 17 800\n"
    "823 ite 2 188 822 821 2:4:SUB:1\n"
    "824 sub 2 17 7\n"
    "825 ite 2 189 824 823 2:5:SUBI:1\n"
    "826 sub 2 17 800\n"
    "827 ite 2 190 826 825 2:6:CMP:1\n"
    "828 ite 2 197 800 827 2:13:MEM:1\n"
    "829 eq 1 23 800\n"
    "830 ite 2 829 7 6\n"
    "831 ite 2 198 830 828 2:14:CAS:1\n"
    "832 next 2 17 831\n"
    "\n"
    "; accu_3\n"
    "833 ite 2 201 800 19 3:0:LOAD:1\n"
    "834 add 2 19 800\n"
    "835 ite 2 203 834 833 3:2:ADD:1\n"
    "836 add 2 19 7\n"
    "837 ite 2 204 836 835 3:3:ADDI:1\n"
    "838 sub 2 19 800\n"
    "839 ite 2 205 838 837 3:4:SUB:1\n"
    "840 sub 2 19 7\n"
    "841 ite 2 206 840 839 3:5:SUBI:1\n"
    "842 sub 2 19 800\n"
    "843 ite 2 207 842 841 3:6:CMP:1\n"
    "844 ite 2 214 800 843 3:13:MEM:1\n"
    "845 eq 1 25 800\n"
    "846 ite 2 845 7 6\n"
    "847 ite 2 215 846 844 3:14:CAS:1\n"
    "848 next 2 19 847\n"
    "\n"
    "; update CAS memory register ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; mem_1\n"
    "849 ite 2 180 800 21 1:13:MEM:1\n"
    "850 next 2 21 849\n"
    "\n"
    "; mem_2\n"
    "851 ite 2 197 800 23 2:13:MEM:1\n"
    "852 next 2 23 851\n"
    "\n"
    "; mem_3\n"
    "853 ite 2 214 800 25 3:13:MEM:1\n"
    "854 next 2 25 853\n"
    "\n"
    "; update heap ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "855 write 3 14 7 15\n"
    "856 ite 3 168 855 14 1:1:STORE:1\n"
    "857 eq 1 21 800\n"
    "858 ite 3 857 855 14\n"
    "859 ite 3 181 858 856 1:14:CAS:1\n"
    "860 write 3 14 7 17\n"
    "861 ite 3 185 860 859 2:1:STORE:1\n"
    "862 eq 1 23 800\n"
    "863 ite 3 862 860 14\n"
    "864 ite 3 198 863 861 2:14:CAS:1\n"
    "865 write 3 14 7 19\n"
    "866 ite 3 202 865 864 3:1:STORE:1\n"
    "867 eq 1 25 800\n"
    "868 ite 3 867 865 14\n"
    "869 ite 3 215 868 866 3:14:CAS:1\n"
    "870 next 3 14 869\n"
    "\n"
    "; update exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "871 or 1 129 217\n"
    "872 or 1 183 871\n"
    "873 or 1 200 872\n"
    "874 next 1 129 873\n"
    "\n"
    "; update exit code ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "875 ite 2 183 7 131 1:16:EXIT:1\n"
    "876 ite 2 200 7 875 2:16:EXIT:1\n"
    "877 ite 2 217 7 876 3:16:EXIT:1\n"
    "878 next 2 131 877\n"
    "\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  init_statement_activation(true);

  verbose = false;
  encoder->add_state_update();
  verbose = true;

  ASSERT_EQ(
    "509 not 1 167\n"
    "510 and 1 27 509\n"
    "511 next 1 27 510\n"
    "\n"
    "512 not 1 168\n"
    "513 and 1 29 512\n"
    "514 ite 1 27 167 513\n"
    "515 ite 1 41 174 514\n"
    "516 eq 1 15 6\n"
    "517 and 1 175 516\n"
    "518 ite 1 43 517 515\n"
    "519 ne 1 15 6\n"
    "520 and 1 176 519\n"
    "521 ite 1 45 520 518\n"
    "522 slice 1 15 15 15\n"
    "523 and 1 177 522\n"
    "524 ite 1 47 523 521\n"
    "525 slice 1 15 15 15\n"
    "526 not 1 525\n"
    "527 and 1 178 526\n"
    "528 ite 1 49 527 524\n"
    "530 ne 1 15 6\n"
    "531 slice 1 15 15 15\n"
    "532 not 1 531\n"
    "533 and 1 530 532\n"
    "534 and 1 179 533\n"
    "535 ite 1 51 534 528\n"
    "536 next 1 29 535\n"
    "\n"
    "537 not 1 169\n"
    "538 and 1 31 537\n"
    "539 ite 1 29 168 538\n"
    "540 next 1 31 539\n"
    "\n"
    "541 not 1 170\n"
    "542 and 1 33 541\n"
    "543 ite 1 31 169 542\n"
    "544 next 1 33 543\n"
    "\n"
    "545 not 1 171\n"
    "546 and 1 35 545\n"
    "547 ite 1 33 170 546\n"
    "548 next 1 35 547\n"
    "\n"
    "549 not 1 172\n"
    "550 and 1 37 549\n"
    "551 ite 1 35 171 550\n"
    "552 next 1 37 551\n"
    "\n"
    "553 not 1 173\n"
    "554 and 1 39 553\n"
    "555 ite 1 37 172 554\n"
    "556 next 1 39 555\n"
    "\n"
    "557 not 1 174\n"
    "558 and 1 41 557\n"
    "559 ite 1 39 173 558\n"
    "560 next 1 41 559\n"
    "\n"
    "561 not 1 175\n"
    "562 and 1 43 561\n"
    "563 next 1 43 562\n"
    "\n"
    "564 not 1 176\n"
    "565 and 1 45 564\n"
    "566 not 1 516\n"
    "567 and 1 175 566\n"
    "568 ite 1 43 567 565\n"
    "569 next 1 45 568\n"
    "\n"
    "570 not 1 177\n"
    "571 and 1 47 570\n"
    "572 not 1 519\n"
    "573 and 1 176 572\n"
    "574 ite 1 45 573 571\n"
    "575 next 1 47 574\n"
    "\n"
    "576 not 1 178\n"
    "577 and 1 49 576\n"
    "578 not 1 522\n"
    "579 and 1 177 578\n"
    "580 ite 1 47 579 577\n"
    "581 next 1 49 580\n"
    "\n"
    "582 not 1 179\n"
    "583 and 1 51 582\n"
    "584 not 1 526\n"
    "585 and 1 178 584\n"
    "586 ite 1 49 585 583\n"
    "587 next 1 51 586\n"
    "\n"
    "588 not 1 180\n"
    "589 and 1 53 588\n"
    "590 not 1 533\n"
    "591 and 1 179 590\n"
    "592 ite 1 51 591 589\n"
    "593 next 1 53 592\n"
    "\n"
    "594 not 1 181\n"
    "595 and 1 55 594\n"
    "596 ite 1 53 180 595\n"
    "597 next 1 55 596\n"
    "\n"
    "598 not 1 182\n"
    "599 and 1 57 598\n"
    "600 ite 1 55 181 599\n"
    "601 next 1 57 600\n"
    "\n"
    "602 not 1 183\n"
    "603 and 1 59 602\n"
    "604 ite 1 57 182 603\n"
    "605 next 1 59 604\n"
    "\n"
    "606 not 1 184\n"
    "607 and 1 61 606\n"
    "608 next 1 61 607\n"
    "\n"
    "609 not 1 185\n"
    "610 and 1 63 609\n"
    "611 ite 1 61 184 610\n"
    "612 ite 1 75 191 611\n"
    "613 eq 1 17 6\n"
    "614 and 1 192 613\n"
    "615 ite 1 77 614 612\n"
    "616 ne 1 17 6\n"
    "617 and 1 193 616\n"
    "618 ite 1 79 617 615\n"
    "619 slice 1 17 15 15\n"
    "620 and 1 194 619\n"
    "621 ite 1 81 620 618\n"
    "622 slice 1 17 15 15\n"
    "623 not 1 622\n"
    "624 and 1 195 623\n"
    "625 ite 1 83 624 621\n"
    "627 ne 1 17 6\n"
    "628 slice 1 17 15 15\n"
    "629 not 1 628\n"
    "630 and 1 627 629\n"
    "631 and 1 196 630\n"
    "632 ite 1 85 631 625\n"
    "633 next 1 63 632\n"
    "\n"
    "634 not 1 186\n"
    "635 and 1 65 634\n"
    "636 ite 1 63 185 635\n"
    "637 next 1 65 636\n"
    "\n"
    "638 not 1 187\n"
    "639 and 1 67 638\n"
    "640 ite 1 65 186 639\n"
    "641 next 1 67 640\n"
    "\n"
    "642 not 1 188\n"
    "643 and 1 69 642\n"
    "644 ite 1 67 187 643\n"
    "645 next 1 69 644\n"
    "\n"
    "646 not 1 189\n"
    "647 and 1 71 646\n"
    "648 ite 1 69 188 647\n"
    "649 next 1 71 648\n"
    "\n"
    "650 not 1 190\n"
    "651 and 1 73 650\n"
    "652 ite 1 71 189 651\n"
    "653 next 1 73 652\n"
    "\n"
    "654 not 1 191\n"
    "655 and 1 75 654\n"
    "656 ite 1 73 190 655\n"
    "657 next 1 75 656\n"
    "\n"
    "658 not 1 192\n"
    "659 and 1 77 658\n"
    "660 next 1 77 659\n"
    "\n"
    "661 not 1 193\n"
    "662 and 1 79 661\n"
    "663 not 1 613\n"
    "664 and 1 192 663\n"
    "665 ite 1 77 664 662\n"
    "666 next 1 79 665\n"
    "\n"
    "667 not 1 194\n"
    "668 and 1 81 667\n"
    "669 not 1 616\n"
    "670 and 1 193 669\n"
    "671 ite 1 79 670 668\n"
    "672 next 1 81 671\n"
    "\n"
    "673 not 1 195\n"
    "674 and 1 83 673\n"
    "675 not 1 619\n"
    "676 and 1 194 675\n"
    "677 ite 1 81 676 674\n"
    "678 next 1 83 677\n"
    "\n"
    "679 not 1 196\n"
    "680 and 1 85 679\n"
    "681 not 1 623\n"
    "682 and 1 195 681\n"
    "683 ite 1 83 682 680\n"
    "684 next 1 85 683\n"
    "\n"
    "685 not 1 197\n"
    "686 and 1 87 685\n"
    "687 not 1 630\n"
    "688 and 1 196 687\n"
    "689 ite 1 85 688 686\n"
    "690 next 1 87 689\n"
    "\n"
    "691 not 1 198\n"
    "692 and 1 89 691\n"
    "693 ite 1 87 197 692\n"
    "694 next 1 89 693\n"
    "\n"
    "695 not 1 199\n"
    "696 and 1 91 695\n"
    "697 ite 1 89 198 696\n"
    "698 next 1 91 697\n"
    "\n"
    "699 not 1 200\n"
    "700 and 1 93 699\n"
    "701 ite 1 91 199 700\n"
    "702 next 1 93 701\n"
    "\n"
    "703 not 1 201\n"
    "704 and 1 95 703\n"
    "705 next 1 95 704\n"
    "\n"
    "706 not 1 202\n"
    "707 and 1 97 706\n"
    "708 ite 1 95 201 707\n"
    "709 ite 1 109 208 708\n"
    "710 eq 1 19 6\n"
    "711 and 1 209 710\n"
    "712 ite 1 111 711 709\n"
    "713 ne 1 19 6\n"
    "714 and 1 210 713\n"
    "715 ite 1 113 714 712\n"
    "716 slice 1 19 15 15\n"
    "717 and 1 211 716\n"
    "718 ite 1 115 717 715\n"
    "719 slice 1 19 15 15\n"
    "720 not 1 719\n"
    "721 and 1 212 720\n"
    "722 ite 1 117 721 718\n"
    "724 ne 1 19 6\n"
    "725 slice 1 19 15 15\n"
    "726 not 1 725\n"
    "727 and 1 724 726\n"
    "728 and 1 213 727\n"
    "729 ite 1 119 728 722\n"
    "730 next 1 97 729\n"
    "\n"
    "731 not 1 203\n"
    "732 and 1 99 731\n"
    "733 ite 1 97 202 732\n"
    "734 next 1 99 733\n"
    "\n"
    "735 not 1 204\n"
    "736 and 1 101 735\n"
    "737 ite 1 99 203 736\n"
    "738 next 1 101 737\n"
    "\n"
    "739 not 1 205\n"
    "740 and 1 103 739\n"
    "741 ite 1 101 204 740\n"
    "742 next 1 103 741\n"
    "\n"
    "743 not 1 206\n"
    "744 and 1 105 743\n"
    "745 ite 1 103 205 744\n"
    "746 next 1 105 745\n"
    "\n"
    "747 not 1 207\n"
    "748 and 1 107 747\n"
    "749 ite 1 105 206 748\n"
    "750 next 1 107 749\n"
    "\n"
    "751 not 1 208\n"
    "752 and 1 109 751\n"
    "753 ite 1 107 207 752\n"
    "754 next 1 109 753\n"
    "\n"
    "755 not 1 209\n"
    "756 and 1 111 755\n"
    "757 next 1 111 756\n"
    "\n"
    "758 not 1 210\n"
    "759 and 1 113 758\n"
    "760 not 1 710\n"
    "761 and 1 209 760\n"
    "762 ite 1 111 761 759\n"
    "763 next 1 113 762\n"
    "\n"
    "764 not 1 211\n"
    "765 and 1 115 764\n"
    "766 not 1 713\n"
    "767 and 1 210 766\n"
    "768 ite 1 113 767 765\n"
    "769 next 1 115 768\n"
    "\n"
    "770 not 1 212\n"
    "771 and 1 117 770\n"
    "772 not 1 716\n"
    "773 and 1 211 772\n"
    "774 ite 1 115 773 771\n"
    "775 next 1 117 774\n"
    "\n"
    "776 not 1 213\n"
    "777 and 1 119 776\n"
    "778 not 1 720\n"
    "779 and 1 212 778\n"
    "780 ite 1 117 779 777\n"
    "781 next 1 119 780\n"
    "\n"
    "782 not 1 214\n"
    "783 and 1 121 782\n"
    "784 not 1 727\n"
    "785 and 1 213 784\n"
    "786 ite 1 119 785 783\n"
    "787 next 1 121 786\n"
    "\n"
    "788 not 1 215\n"
    "789 and 1 123 788\n"
    "790 ite 1 121 214 789\n"
    "791 next 1 123 790\n"
    "\n"
    "792 not 1 216\n"
    "793 and 1 125 792\n"
    "794 ite 1 123 215 793\n"
    "795 next 1 125 794\n"
    "\n"
    "796 not 1 217\n"
    "797 and 1 127 796\n"
    "798 ite 1 125 216 797\n"
    "799 next 1 127 798\n"
    "\n"
    "800 read 2 14 7\n"
    "801 ite 2 167 800 15\n"
    "802 add 2 15 800\n"
    "803 ite 2 169 802 801\n"
    "804 add 2 15 7\n"
    "805 ite 2 170 804 803\n"
    "806 sub 2 15 800\n"
    "807 ite 2 171 806 805\n"
    "808 sub 2 15 7\n"
    "809 ite 2 172 808 807\n"
    "810 sub 2 15 800\n"
    "811 ite 2 173 810 809\n"
    "812 ite 2 180 800 811\n"
    "813 eq 1 21 800\n"
    "814 ite 2 813 7 6\n"
    "815 ite 2 181 814 812\n"
    "816 next 2 15 815\n"
    "\n"
    "817 ite 2 184 800 17\n"
    "818 add 2 17 800\n"
    "819 ite 2 186 818 817\n"
    "820 add 2 17 7\n"
    "821 ite 2 187 820 819\n"
    "822 sub 2 17 800\n"
    "823 ite 2 188 822 821\n"
    "824 sub 2 17 7\n"
    "825 ite 2 189 824 823\n"
    "826 sub 2 17 800\n"
    "827 ite 2 190 826 825\n"
    "828 ite 2 197 800 827\n"
    "829 eq 1 23 800\n"
    "830 ite 2 829 7 6\n"
    "831 ite 2 198 830 828\n"
    "832 next 2 17 831\n"
    "\n"
    "833 ite 2 201 800 19\n"
    "834 add 2 19 800\n"
    "835 ite 2 203 834 833\n"
    "836 add 2 19 7\n"
    "837 ite 2 204 836 835\n"
    "838 sub 2 19 800\n"
    "839 ite 2 205 838 837\n"
    "840 sub 2 19 7\n"
    "841 ite 2 206 840 839\n"
    "842 sub 2 19 800\n"
    "843 ite 2 207 842 841\n"
    "844 ite 2 214 800 843\n"
    "845 eq 1 25 800\n"
    "846 ite 2 845 7 6\n"
    "847 ite 2 215 846 844\n"
    "848 next 2 19 847\n"
    "\n"
    "849 ite 2 180 800 21\n"
    "850 next 2 21 849\n"
    "\n"
    "851 ite 2 197 800 23\n"
    "852 next 2 23 851\n"
    "\n"
    "853 ite 2 214 800 25\n"
    "854 next 2 25 853\n"
    "\n"
    "855 write 3 14 7 15\n"
    "856 ite 3 168 855 14\n"
    "857 eq 1 21 800\n"
    "858 ite 3 857 855 14\n"
    "859 ite 3 181 858 856\n"
    "860 write 3 14 7 17\n"
    "861 ite 3 185 860 859\n"
    "862 eq 1 23 800\n"
    "863 ite 3 862 860 14\n"
    "864 ite 3 198 863 861\n"
    "865 write 3 14 7 19\n"
    "866 ite 3 202 865 864\n"
    "867 eq 1 25 800\n"
    "868 ite 3 867 865 14\n"
    "869 ite 3 215 868 866\n"
    "870 next 3 14 869\n"
    "\n"
    "871 or 1 129 217\n"
    "872 or 1 183 871\n"
    "873 or 1 200 872\n"
    "874 next 1 129 873\n"
    "\n"
    "875 ite 2 183 7 131\n"
    "876 ite 2 200 7 875\n"
    "877 ite 2 217 7 876\n"
    "878 next 2 131 877\n"
    "\n",
    encoder->formula.str());
}

// std::string load(Load &);
TEST_F(Btor2EncoderTest, load)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  Load l(1);

  ASSERT_EQ("34", encoder->load(l));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ("34 read 2 14 7\n", encoder->formula.str());

  /* another load from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("34", encoder->load(l));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ("", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  l.indirect = true;

  ASSERT_EQ("35", encoder->load(l));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "35"}}), encoder->nids_load_indirect);
  ASSERT_EQ("35 read 2 14 34\n", encoder->formula.str());

  /* another load from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("35", encoder->load(l));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "35"}}), encoder->nids_load_indirect);
  ASSERT_EQ("", encoder->formula.str());
}

// std::string store(Store &);
TEST_F(Btor2EncoderTest, store)
{
  add_dummy_programs(2, 1);

  init_statement_activation(true);

  Store s(1);

  encoder->thread = 1;
  ASSERT_EQ("51", encoder->store(s));
  ASSERT_EQ(Word2Word2NIDMap({{1, {{1, "51"}}}}), encoder->nids_store);
  ASSERT_EQ("51 write 3 15 7 16\n", encoder->formula.str());

  encoder->formula.str("");

  encoder->thread = 2;
  ASSERT_EQ("52", encoder->store(s));
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "51"}}},
      {2, {{1, "52"}}}}),
    encoder->nids_store);
  ASSERT_EQ("52 write 3 15 7 18\n", encoder->formula.str());

  /* another store to the same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  ASSERT_EQ("51", encoder->store(s));
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "51"}}},
      {2, {{1, "52"}}}}),
    encoder->nids_store);
  ASSERT_EQ("", encoder->formula.str());

  encoder->thread = 2;
  ASSERT_EQ("52", encoder->store(s));
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "51"}}},
      {2, {{1, "52"}}}}),
    encoder->nids_store);
  ASSERT_EQ("", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  s.indirect = true;

  encoder->thread = 1;
  ASSERT_EQ("54", encoder->store(s));
  ASSERT_EQ(Word2NIDMap({{1, "53"}}), encoder->nids_load);
  ASSERT_EQ(Word2Word2NIDMap({{1, {{1, "54"}}}}), encoder->nids_store_indirect);
  ASSERT_EQ(
    "53 read 2 15 7\n"
    "54 write 3 15 53 16\n",
    encoder->formula.str());

  encoder->formula.str("");

  encoder->thread = 2;
  ASSERT_EQ("55", encoder->store(s));
  ASSERT_EQ(Word2NIDMap({{1, "53"}}), encoder->nids_load);
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "54"}}},
      {2, {{1, "55"}}}}),
    encoder->nids_store_indirect);
  ASSERT_EQ(
    "55 write 3 15 53 18\n",
    encoder->formula.str());

  /* another store to the same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  ASSERT_EQ("54", encoder->store(s));
  ASSERT_EQ(Word2NIDMap({{1, "53"}}), encoder->nids_load);
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "54"}}},
      {2, {{1, "55"}}}}),
    encoder->nids_store_indirect);
  ASSERT_EQ("", encoder->formula.str());

  encoder->thread = 2;
  ASSERT_EQ("55", encoder->store(s));
  ASSERT_EQ(Word2NIDMap({{1, "53"}}), encoder->nids_load);
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "54"}}},
      {2, {{1, "55"}}}}),
    encoder->nids_store_indirect);
  ASSERT_EQ("", encoder->formula.str());
}

// virtual void encode (void);
TEST_F(Btor2EncoderTest, encode_sync)
{
  /* concurrent increment using SYNC */
  programs.push_back(
    create_from_file<Program>("data/increment.sync.thread.0.asm"));
  programs.push_back(
    create_from_file<Program>("data/increment.sync.thread.n.asm"));

  encoder =
    make_shared<Btor2Encoder>(
      make_shared<ProgramList>(programs), 12);

  ifstream ifs("data/increment.sync.t2.k12.btor2");
  expected.assign(istreambuf_iterator<char>(ifs), istreambuf_iterator<char>());

  ASSERT_EQ(expected, encoder->formula.str());
}

TEST_F(Btor2EncoderTest, encode_cas)
{
  /* concurrent increment using CAS */
  programs.push_back(create_from_file<Program>("data/increment.cas.asm"));
  programs.push_back(create_from_file<Program>("data/increment.cas.asm"));

  encoder =
    make_shared<Btor2Encoder>(
      make_shared<ProgramList>(programs), 12);

  ifstream ifs("data/increment.cas.t2.k12.btor2");
  expected.assign(istreambuf_iterator<char>(ifs), istreambuf_iterator<char>());

  ASSERT_EQ(expected, encoder->formula.str());
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

  ASSERT_EQ("35", encoder->encode(a));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ(
    "34 read 2 14 7\n"
    "35 add 2 15 34\n",
    encoder->formula.str());

  /* another ADD from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("36", encoder->encode(a));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ("36 add 2 15 34\n", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  a.indirect = true;

  ASSERT_EQ("38", encoder->encode(a));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "37"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "37 read 2 14 34\n"
    "38 add 2 15 37\n",
    encoder->formula.str());

  /* another ADD from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("39", encoder->encode(a));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "37"}}), encoder->nids_load_indirect);
  ASSERT_EQ("39 add 2 15 37\n", encoder->formula.str());
}

// virtual std::string encode (Addi &);
TEST_F(Btor2EncoderTest, ADDI)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Addi a(1);

  ASSERT_EQ("34", encoder->encode(a));
  ASSERT_EQ("34 add 2 15 7\n", encoder->formula.str());

  /* another ADDI with the same constant */
  encoder->formula.str("");

  ASSERT_EQ("35", encoder->encode(a));
  ASSERT_EQ("35 add 2 15 7\n", encoder->formula.str());
}

// virtual std::string encode (Sub &);
TEST_F(Btor2EncoderTest, SUB)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Sub s(1);

  ASSERT_EQ("35", encoder->encode(s));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ(
    "34 read 2 14 7\n"
    "35 sub 2 15 34\n",
    encoder->formula.str());

  /* another SUB from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("36", encoder->encode(s));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ("36 sub 2 15 34\n", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  s.indirect = true;

  ASSERT_EQ("38", encoder->encode(s));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "37"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "37 read 2 14 34\n"
    "38 sub 2 15 37\n",
    encoder->formula.str());

  /* another SUB from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("39", encoder->encode(s));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "37"}}), encoder->nids_load_indirect);
  ASSERT_EQ("39 sub 2 15 37\n", encoder->formula.str());
}

// virtual std::string encode (Subi &);
TEST_F(Btor2EncoderTest, SUBI)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Subi s(1);

  ASSERT_EQ("34", encoder->encode(s));
  ASSERT_EQ("34 sub 2 15 7\n", encoder->formula.str());

  /* another SUBI with the same constant */
  encoder->formula.str("");

  ASSERT_EQ("35", encoder->encode(s));
  ASSERT_EQ("35 sub 2 15 7\n", encoder->formula.str());
}

// virtual std::string encode (Cmp &);
TEST_F(Btor2EncoderTest, CMP)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Cmp c(1);

  ASSERT_EQ("35", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ(
    "34 read 2 14 7\n"
    "35 sub 2 15 34\n",
    encoder->formula.str());

  /* another CMP from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("36", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ("36 sub 2 15 34\n", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  c.indirect = true;

  ASSERT_EQ("38", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "37"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "37 read 2 14 34\n"
    "38 sub 2 15 37\n",
    encoder->formula.str());

  /* another CMP from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("39", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "37"}}), encoder->nids_load_indirect);
  ASSERT_EQ("39 sub 2 15 37\n", encoder->formula.str());
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

  ASSERT_EQ("34", encoder->encode(j));
  ASSERT_EQ("34 eq 1 15 6\n", encoder->formula.str());
}

// virtual std::string encode (Jnz &);
TEST_F(Btor2EncoderTest, JNZ)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Jnz j(1);

  ASSERT_EQ("34", encoder->encode(j));
  ASSERT_EQ("34 ne 1 15 6\n", encoder->formula.str());
}

// virtual std::string encode (Js &);
TEST_F(Btor2EncoderTest, JS)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Js j(1);

  ASSERT_EQ("34", encoder->encode(j));
  ASSERT_EQ("34 slice 1 15 15 15\n", encoder->formula.str());
}

// virtual std::string encode (Jns &);
TEST_F(Btor2EncoderTest, JNS)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Jns j(1);

  ASSERT_EQ("35", encoder->encode(j));
  ASSERT_EQ(
    "34 slice 1 15 15 15\n"
    "35 not 1 34\n",
    encoder->formula.str());
}

// virtual std::string encode (Jnzns &);
TEST_F(Btor2EncoderTest, JNZNS)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Jnzns j(1);

  ASSERT_EQ("38", encoder->encode(j));
  ASSERT_EQ(
    "35 ne 1 15 6\n"
    "36 slice 1 15 15 15\n"
    "37 not 1 36\n"
    "38 and 1 35 37\n",
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
  add_dummy_programs(2, 1);

  init_statement_activation(true);

  encoder->update_accu = true;

  Cas c(1);

  encoder->thread = 1;
  ASSERT_EQ("53", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(
    "51 read 2 15 7\n"
    "52 eq 1 20 51\n"
    "53 ite 2 52 7 6\n",
    encoder->formula.str());

  encoder->formula.str("");

  encoder->thread = 2;
  ASSERT_EQ("55", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(
    "54 eq 1 22 51\n"
    "55 ite 2 54 7 6\n",
    encoder->formula.str());

  /* another CAS to the same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  ASSERT_EQ("57", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(
    "56 eq 1 20 51\n"
    "57 ite 2 56 7 6\n",
    encoder->formula.str());

  encoder->formula.str("");

  encoder->thread = 2;
  ASSERT_EQ("59", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(
    "58 eq 1 22 51\n"
    "59 ite 2 58 7 6\n",
    encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  c.indirect = true;

  encoder->thread = 1;
  ASSERT_EQ("62", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "60"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "60 read 2 15 51\n"
    "61 eq 1 20 60\n"
    "62 ite 2 61 7 6\n",
    encoder->formula.str());

  encoder->formula.str("");

  encoder->thread = 2;
  ASSERT_EQ("64", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "60"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "63 eq 1 22 60\n"
    "64 ite 2 63 7 6\n",
    encoder->formula.str());

  /* another CAS to the same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  ASSERT_EQ("66", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "60"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "65 eq 1 20 60\n"
    "66 ite 2 65 7 6\n",
    encoder->formula.str());

  encoder->formula.str("");

  encoder->thread = 2;
  ASSERT_EQ("68", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "60"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "67 eq 1 22 60\n"
    "68 ite 2 67 7 6\n",
    encoder->formula.str());
}

TEST_F(Btor2EncoderTest, CAS_heap)
{
  add_dummy_programs(2, 1);

  init_statement_activation(true);

  encoder->update_accu = false;

  Cas c(1);

  encoder->thread = 1;
  ASSERT_EQ("54", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(Word2Word2NIDMap({{1, {{1, "53"}}}}), encoder->nids_store);
  ASSERT_EQ(
    "51 read 2 15 7\n"
    "52 eq 1 20 51\n"
    "53 write 3 15 7 16\n"
    "54 ite 3 52 53 15\n",
    encoder->formula.str());

  encoder->formula.str("");

  encoder->thread = 2;
  ASSERT_EQ("57", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "53"}}},
      {2, {{1, "56"}}}}),
    encoder->nids_store);
  ASSERT_EQ(
    "55 eq 1 22 51\n"
    "56 write 3 15 7 18\n"
    "57 ite 3 55 56 15\n",
    encoder->formula.str());

  /* another CAS to the same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  ASSERT_EQ("59", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "53"}}},
      {2, {{1, "56"}}}}),
    encoder->nids_store);
  ASSERT_EQ(
    "58 eq 1 20 51\n"
    "59 ite 3 58 53 15\n",
    encoder->formula.str());

  encoder->formula.str("");

  encoder->thread = 2;
  ASSERT_EQ("61", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "53"}}},
      {2, {{1, "56"}}}}),
    encoder->nids_store);
  ASSERT_EQ(
    "60 eq 1 22 51\n"
    "61 ite 3 60 56 15\n",
    encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  c.indirect = true;

  encoder->thread = 1;
  ASSERT_EQ("65", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "62"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "53"}}},
      {2, {{1, "56"}}}}),
    encoder->nids_store);
  ASSERT_EQ(Word2Word2NIDMap({{1, {{1, "64"}}}}), encoder->nids_store_indirect);
  ASSERT_EQ(
    "62 read 2 15 51\n"
    "63 eq 1 20 62\n"
    "64 write 3 15 51 16\n"
    "65 ite 3 63 64 15\n",
    encoder->formula.str());

  encoder->formula.str("");

  encoder->thread = 2;
  ASSERT_EQ("68", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "62"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "53"}}},
      {2, {{1, "56"}}}}),
    encoder->nids_store);
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "64"}}},
      {2, {{1, "67"}}}}),
    encoder->nids_store_indirect);
  ASSERT_EQ(
    "66 eq 1 22 62\n"
    "67 write 3 15 51 18\n"
    "68 ite 3 66 67 15\n",
    encoder->formula.str());

  /* another CAS to the same memory address */
  encoder->formula.str("");

  encoder->thread = 1;
  ASSERT_EQ("70", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "62"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "53"}}},
      {2, {{1, "56"}}}}),
    encoder->nids_store);
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "64"}}},
      {2, {{1, "67"}}}}),
    encoder->nids_store_indirect);
  ASSERT_EQ(
    "69 eq 1 20 62\n"
    "70 ite 3 69 64 15\n",
    encoder->formula.str());

  encoder->formula.str("");

  encoder->thread = 2;
  ASSERT_EQ("72", encoder->encode(c));
  ASSERT_EQ(Word2NIDMap({{1, "51"}}), encoder->nids_load);
  ASSERT_EQ(Word2NIDMap({{1, "62"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "53"}}},
      {2, {{1, "56"}}}}),
    encoder->nids_store);
  ASSERT_EQ(
    Word2Word2NIDMap({
      {1, {{1, "64"}}},
      {2, {{1, "67"}}}}),
    encoder->nids_store_indirect);
  ASSERT_EQ(
    "71 eq 1 22 62\n"
    "72 ite 3 71 67 15\n",
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
