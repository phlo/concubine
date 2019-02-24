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
  const char *      expected;
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
};

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
  ASSERT_EQ("23", encoder->nid_exit);
  ASSERT_EQ(vector<string>({"25", "27", "29"}), encoder->nids_stmt[1]);
  ASSERT_EQ(vector<string>({"31", "33", "35"}), encoder->nids_stmt[2]);
  ASSERT_EQ(vector<string>({"37", "39", "41"}), encoder->nids_stmt[3]);
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
    "; exit\n"
    "23 state 1 exit\n"
    "24 init 1 23 4\n"
    "\n"
    "; statement activation\n"
    "25 state 1 stmt_1_0\n"
    "26 init 1 25 5\n"
    "27 state 1 stmt_1_1\n"
    "28 init 1 27 4\n"
    "29 state 1 stmt_1_2\n"
    "30 init 1 29 4\n"
    "\n"
    "31 state 1 stmt_2_0\n"
    "32 init 1 31 5\n"
    "33 state 1 stmt_2_1\n"
    "34 init 1 33 4\n"
    "35 state 1 stmt_2_2\n"
    "36 init 1 35 4\n"
    "\n"
    "37 state 1 stmt_3_0\n"
    "38 init 1 37 5\n"
    "39 state 1 stmt_3_1\n"
    "40 init 1 39 4\n"
    "41 state 1 stmt_3_2\n"
    "42 init 1 41 4\n\n",
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
    "23 state 1 exit\n"
    "24 init 1 23 4\n"
    "\n"
    "25 state 1 stmt_1_0\n"
    "26 init 1 25 5\n"
    "27 state 1 stmt_1_1\n"
    "28 init 1 27 4\n"
    "29 state 1 stmt_1_2\n"
    "30 init 1 29 4\n"
    "\n"
    "31 state 1 stmt_2_0\n"
    "32 init 1 31 5\n"
    "33 state 1 stmt_2_1\n"
    "34 init 1 33 4\n"
    "35 state 1 stmt_2_2\n"
    "36 init 1 35 4\n"
    "\n"
    "37 state 1 stmt_3_0\n"
    "38 init 1 37 5\n"
    "39 state 1 stmt_3_1\n"
    "40 init 1 39 4\n"
    "41 state 1 stmt_3_2\n"
    "42 init 1 41 4\n\n",
    encoder->formula.str());
}

// void add_thread_scheduling ();
TEST_F(Btor2EncoderTest, add_thread_scheduling)
{
  add_dummy_programs(3, 3);

  init_states(true);

  encoder->add_thread_scheduling();

  ASSERT_EQ(NIDMap({{1, "49"}, {2, "50"}, {3, "51"}}), encoder->nids_thread);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; thread scheduling\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "49 input 1 thread_1\n"
    "50 input 1 thread_2\n"
    "51 input 1 thread_3\n"
    "\n"
    "; cardinality constraint\n"
    "52 or 1 49 50\n"
    "53 or 1 51 52\n"
    "54 or 1 29 53\n"
    "55 constraint 54\n"
    "56 nand 1 49 50\n"
    "57 nand 1 49 51\n"
    "58 nand 1 49 29\n"
    "59 nand 1 50 51\n"
    "60 nand 1 50 29\n"
    "61 nand 1 51 29\n"
    "62 and 1 56 57\n"
    "63 and 1 58 62\n"
    "64 and 1 59 63\n"
    "65 and 1 60 64\n"
    "66 and 1 61 65\n"
    "67 constraint 66\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  init_states(true);

  verbose = false;
  encoder->add_thread_scheduling();
  verbose = true;

  ASSERT_EQ(
    "49 input 1 thread_1\n"
    "50 input 1 thread_2\n"
    "51 input 1 thread_3\n"
    "\n"
    "52 or 1 49 50\n"
    "53 or 1 51 52\n"
    "54 or 1 29 53\n"
    "55 constraint 54\n"
    "56 nand 1 49 50\n"
    "57 nand 1 49 51\n"
    "58 nand 1 49 29\n"
    "59 nand 1 50 51\n"
    "60 nand 1 50 29\n"
    "61 nand 1 51 29\n"
    "62 and 1 56 57\n"
    "63 and 1 58 62\n"
    "64 and 1 59 63\n"
    "65 and 1 60 64\n"
    "66 and 1 61 65\n"
    "67 constraint 66\n\n",
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

  ASSERT_EQ(NIDMap({{1, "65"}, {2, "77"}}), encoder->nids_sync);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; synchronization constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; negated thread activation variables\n"
    "61 not 1 42 not_thread_1\n"
    "62 not 1 43 not_thread_2\n"
    "63 not 1 44 not_thread_3\n"
    "\n"
    "; synchronization condition sync_1\n"
    "64 and 1 30 34\n"
    "65 and 1 38 64 sync_1\n"
    "66 not 1 65 not_sync_1\n"
    "\n"
    "; disable threads waiting for barrier 1\n"
    "67 and 1 30 66\n"
    "68 implies 1 67 61\n"
    "69 constraint 68 sync_1_block_1\n"
    "\n"
    "70 and 1 34 66\n"
    "71 implies 1 70 62\n"
    "72 constraint 71 sync_1_block_2\n"
    "\n"
    "73 and 1 38 66\n"
    "74 implies 1 73 63\n"
    "75 constraint 74 sync_1_block_3\n"
    "\n"
    "; synchronization condition sync_2\n"
    "76 and 1 32 36\n"
    "77 and 1 40 76 sync_2\n"
    "78 not 1 77 not_sync_2\n"
    "\n"
    "; disable threads waiting for barrier 2\n"
    "79 and 1 32 78\n"
    "80 implies 1 79 61\n"
    "81 constraint 80 sync_2_block_1\n"
    "\n"
    "82 and 1 36 78\n"
    "83 implies 1 82 62\n"
    "84 constraint 83 sync_2_block_2\n"
    "\n"
    "85 and 1 40 78\n"
    "86 implies 1 85 63\n"
    "87 constraint 86 sync_2_block_3\n\n",
    encoder->formula.str());

  /* multiple calls to the same barrier */
  for (const auto & program : programs)
    for (size_t pc = 0; pc < 4; pc++)
      program->add(Instruction::Set::create("SYNC", pc % 2 + 1));

  reset_encoder(1);

  init_thread_scheduling(true);

  encoder->add_synchronization_constraints();

  ASSERT_EQ(
    vector<string>({"30", "32", "34", "36", "38", "40"}),
    encoder->nids_stmt[1]);
  ASSERT_EQ(
    vector<string>({"42", "44", "46", "48", "50", "52"}),
    encoder->nids_stmt[2]);
  ASSERT_EQ(
    vector<string>({"54", "56", "58", "60", "62", "64"}),
    encoder->nids_stmt[3]);
  ASSERT_EQ(NIDMap({{1, "95"}, {2, "113"}}), encoder->nids_sync);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; synchronization constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; negated thread activation variables\n"
    "85 not 1 66 not_thread_1\n"
    "86 not 1 67 not_thread_2\n"
    "87 not 1 68 not_thread_3\n"
    "\n"
    "; synchronization condition sync_1\n"
    "88 or 1 30 34\n"
    "89 or 1 38 88 thread_1@sync_1\n"
    "90 or 1 42 46\n"
    "91 or 1 50 90 thread_2@sync_1\n"
    "92 or 1 54 58\n"
    "93 or 1 62 92 thread_3@sync_1\n"
    "94 and 1 89 91\n"
    "95 and 1 93 94 sync_1\n"
    "96 not 1 95 not_sync_1\n"
    "\n"
    "; disable threads waiting for barrier 1\n"
    "97 and 1 89 96\n"
    "98 implies 1 97 85\n"
    "99 constraint 98 sync_1_block_1\n"
    "\n"
    "100 and 1 91 96\n"
    "101 implies 1 100 86\n"
    "102 constraint 101 sync_1_block_2\n"
    "\n"
    "103 and 1 93 96\n"
    "104 implies 1 103 87\n"
    "105 constraint 104 sync_1_block_3\n"
    "\n"
    "; synchronization condition sync_2\n"
    "106 or 1 32 36\n"
    "107 or 1 40 106 thread_1@sync_2\n"
    "108 or 1 44 48\n"
    "109 or 1 52 108 thread_2@sync_2\n"
    "110 or 1 56 60\n"
    "111 or 1 64 110 thread_3@sync_2\n"
    "112 and 1 107 109\n"
    "113 and 1 111 112 sync_2\n"
    "114 not 1 113 not_sync_2\n"
    "\n"
    "; disable threads waiting for barrier 2\n"
    "115 and 1 107 114\n"
    "116 implies 1 115 85\n"
    "117 constraint 116 sync_2_block_1\n"
    "\n"
    "118 and 1 109 114\n"
    "119 implies 1 118 86\n"
    "120 constraint 119 sync_2_block_2\n"
    "\n"
    "121 and 1 111 114\n"
    "122 implies 1 121 87\n"
    "123 constraint 122 sync_2_block_3\n\n",
    encoder->formula.str());

  /* barrier only for a subset of threads */
  for (size_t i = 0; i < programs.size() - 1; i++)
    programs[i]->add(Instruction::Set::create("SYNC", 3));

  reset_encoder(1);

  init_thread_scheduling(true);

  encoder->add_synchronization_constraints();

  ASSERT_EQ(
    vector<string>({"31", "33", "35", "37", "39", "41", "43"}),
    encoder->nids_stmt[1]);
  ASSERT_EQ(
    vector<string>({"45", "47", "49", "51", "53", "55", "57"}),
    encoder->nids_stmt[2]);
  ASSERT_EQ(
    vector<string>({"59", "61", "63", "65", "67", "69"}),
    encoder->nids_stmt[3]);
  ASSERT_EQ(NIDMap({{1, "100"}, {2, "118"}, {3, "131"}}), encoder->nids_sync);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; synchronization constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; negated thread activation variables\n"
    "90 not 1 71 not_thread_1\n"
    "91 not 1 72 not_thread_2\n"
    "92 not 1 73 not_thread_3\n"
    "\n"
    "; synchronization condition sync_1\n"
    "93 or 1 31 35\n"
    "94 or 1 39 93 thread_1@sync_1\n"
    "95 or 1 45 49\n"
    "96 or 1 53 95 thread_2@sync_1\n"
    "97 or 1 59 63\n"
    "98 or 1 67 97 thread_3@sync_1\n"
    "99 and 1 94 96\n"
    "100 and 1 98 99 sync_1\n"
    "101 not 1 100 not_sync_1\n"
    "\n"
    "; disable threads waiting for barrier 1\n"
    "102 and 1 94 101\n"
    "103 implies 1 102 90\n"
    "104 constraint 103 sync_1_block_1\n"
    "\n"
    "105 and 1 96 101\n"
    "106 implies 1 105 91\n"
    "107 constraint 106 sync_1_block_2\n"
    "\n"
    "108 and 1 98 101\n"
    "109 implies 1 108 92\n"
    "110 constraint 109 sync_1_block_3\n"
    "\n"
    "; synchronization condition sync_2\n"
    "111 or 1 33 37\n"
    "112 or 1 41 111 thread_1@sync_2\n"
    "113 or 1 47 51\n"
    "114 or 1 55 113 thread_2@sync_2\n"
    "115 or 1 61 65\n"
    "116 or 1 69 115 thread_3@sync_2\n"
    "117 and 1 112 114\n"
    "118 and 1 116 117 sync_2\n"
    "119 not 1 118 not_sync_2\n"
    "\n"
    "; disable threads waiting for barrier 2\n"
    "120 and 1 112 119\n"
    "121 implies 1 120 90\n"
    "122 constraint 121 sync_2_block_1\n"
    "\n"
    "123 and 1 114 119\n"
    "124 implies 1 123 91\n"
    "125 constraint 124 sync_2_block_2\n"
    "\n"
    "126 and 1 116 119\n"
    "127 implies 1 126 92\n"
    "128 constraint 127 sync_2_block_3\n"
    "\n"
    "; synchronization condition sync_3\n"
    "129 or 1 71 72\n"
    "130 and 1 43 57\n"
    "131 and 1 129 130 sync_3\n"
    "132 not 1 131 not_sync_3\n"
    "\n"
    "; disable threads waiting for barrier 3\n"
    "133 and 1 43 132\n"
    "134 implies 1 133 90\n"
    "135 constraint 134 sync_3_block_1\n"
    "\n"
    "136 and 1 57 132\n"
    "137 implies 1 136 91\n"
    "138 constraint 137 sync_3_block_2\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  init_thread_scheduling(true);

  verbose = false;
  encoder->add_synchronization_constraints();
  verbose = true;

  ASSERT_EQ(
    "90 not 1 71 not_thread_1\n"
    "91 not 1 72 not_thread_2\n"
    "92 not 1 73 not_thread_3\n"
    "\n"
    "93 or 1 31 35\n"
    "94 or 1 39 93 thread_1@sync_1\n"
    "95 or 1 45 49\n"
    "96 or 1 53 95 thread_2@sync_1\n"
    "97 or 1 59 63\n"
    "98 or 1 67 97 thread_3@sync_1\n"
    "99 and 1 94 96\n"
    "100 and 1 98 99 sync_1\n"
    "101 not 1 100 not_sync_1\n"
    "\n"
    "102 and 1 94 101\n"
    "103 implies 1 102 90\n"
    "104 constraint 103 sync_1_block_1\n"
    "\n"
    "105 and 1 96 101\n"
    "106 implies 1 105 91\n"
    "107 constraint 106 sync_1_block_2\n"
    "\n"
    "108 and 1 98 101\n"
    "109 implies 1 108 92\n"
    "110 constraint 109 sync_1_block_3\n"
    "\n"
    "111 or 1 33 37\n"
    "112 or 1 41 111 thread_1@sync_2\n"
    "113 or 1 47 51\n"
    "114 or 1 55 113 thread_2@sync_2\n"
    "115 or 1 61 65\n"
    "116 or 1 69 115 thread_3@sync_2\n"
    "117 and 1 112 114\n"
    "118 and 1 116 117 sync_2\n"
    "119 not 1 118 not_sync_2\n"
    "\n"
    "120 and 1 112 119\n"
    "121 implies 1 120 90\n"
    "122 constraint 121 sync_2_block_1\n"
    "\n"
    "123 and 1 114 119\n"
    "124 implies 1 123 91\n"
    "125 constraint 124 sync_2_block_2\n"
    "\n"
    "126 and 1 116 119\n"
    "127 implies 1 126 92\n"
    "128 constraint 127 sync_2_block_3\n"
    "\n"
    "129 or 1 71 72\n"
    "130 and 1 43 57\n"
    "131 and 1 129 130 sync_3\n"
    "132 not 1 131 not_sync_3\n"
    "\n"
    "133 and 1 43 132\n"
    "134 implies 1 133 90\n"
    "135 constraint 134 sync_3_block_1\n"
    "\n"
    "136 and 1 57 132\n"
    "137 implies 1 136 91\n"
    "138 constraint 137 sync_3_block_2\n\n",
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

  ASSERT_EQ(vector<string>({"83", "84", "85"}), encoder->nids_exec[1]);
  ASSERT_EQ(vector<string>({"86", "87", "88"}), encoder->nids_exec[2]);
  ASSERT_EQ(vector<string>({"89", "90", "91"}), encoder->nids_exec[3]);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; statement execution - shorthand for statement & thread activation\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "83 and 1 31 49 exec_1_0\n"
    "84 and 1 33 49 exec_1_1\n"
    "85 and 1 35 72 exec_1_2\n"
    "\n"
    "86 and 1 37 50 exec_2_0\n"
    "87 and 1 39 50 exec_2_1\n"
    "88 and 1 41 72 exec_2_2\n"
    "\n"
    "89 and 1 43 51 exec_3_0\n"
    "90 and 1 45 51 exec_3_1\n"
    "91 and 1 47 72 exec_3_2\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  init_synchronization_constraints(true);

  verbose = false;
  encoder->add_statement_execution();
  verbose = true;

  ASSERT_EQ(
    "83 and 1 31 49 exec_1_0\n"
    "84 and 1 33 49 exec_1_1\n"
    "85 and 1 35 72 exec_1_2\n"
    "\n"
    "86 and 1 37 50 exec_2_0\n"
    "87 and 1 39 50 exec_2_1\n"
    "88 and 1 41 72 exec_2_2\n"
    "\n"
    "89 and 1 43 51 exec_3_0\n"
    "90 and 1 45 51 exec_3_1\n"
    "91 and 1 47 72 exec_3_2\n\n",
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
    "71 not 1 65\n"
    "72 and 1 31 71\n"
    "73 next 1 31 72\n"
    "\n"
    "; stmt_1_1\n"
    "74 not 1 66\n"
    "75 and 1 33 74\n"
    "76 ite 1 31 65 75\n"
    "77 next 1 33 76\n"
    "\n"
    "; stmt_2_0\n"
    "78 not 1 67\n"
    "79 and 1 35 78\n"
    "80 next 1 35 79\n"
    "\n"
    "; stmt_2_1\n"
    "81 not 1 68\n"
    "82 and 1 37 81\n"
    "83 ite 1 35 67 82\n"
    "84 next 1 37 83\n"
    "\n"
    "; stmt_3_0\n"
    "85 not 1 69\n"
    "86 and 1 39 85\n"
    "87 next 1 39 86\n"
    "\n"
    "; stmt_3_1\n"
    "88 not 1 70\n"
    "89 and 1 41 88\n"
    "90 ite 1 39 69 89\n"
    "91 next 1 41 90\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  init_statement_execution(true);

  verbose = false;
  encoder->add_statement_activation();
  verbose = true;

  ASSERT_EQ(
    "71 not 1 65\n"
    "72 and 1 31 71\n"
    "73 next 1 31 72\n"
    "\n"
    "74 not 1 66\n"
    "75 and 1 33 74\n"
    "76 ite 1 31 65 75\n"
    "77 next 1 33 76\n"
    "\n"
    "78 not 1 67\n"
    "79 and 1 35 78\n"
    "80 next 1 35 79\n"
    "\n"
    "81 not 1 68\n"
    "82 and 1 37 81\n"
    "83 ite 1 35 67 82\n"
    "84 next 1 37 83\n"
    "\n"
    "85 not 1 69\n"
    "86 and 1 39 85\n"
    "87 next 1 39 86\n"
    "\n"
    "88 not 1 70\n"
    "89 and 1 41 88\n"
    "90 ite 1 39 69 89\n"
    "91 next 1 41 90\n\n",
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
    "87 not 1 75\n"
    "88 and 1 29 87\n"
    "89 next 1 29 88\n"
    "\n"
    "; stmt_1_1\n"
    "90 not 1 76\n"
    "91 and 1 31 90\n"
    "92 ite 1 29 75 91\n"
    "93 ite 1 33 77 92\n"
    "94 next 1 31 93\n"
    "\n"
    "; stmt_1_2\n"
    "95 not 1 77\n"
    "96 and 1 33 95\n"
    "97 ite 1 31 76 96\n"
    "98 next 1 33 97\n"
    "\n"
    "; stmt_1_3\n"
    "99 not 1 78\n"
    "100 and 1 35 99\n"
    "101 next 1 35 100\n"
    "\n"
    "; stmt_2_0\n"
    "102 not 1 79\n"
    "103 and 1 37 102\n"
    "104 next 1 37 103\n"
    "\n"
    "; stmt_2_1\n"
    "105 not 1 80\n"
    "106 and 1 39 105\n"
    "107 ite 1 37 79 106\n"
    "108 ite 1 41 81 107\n"
    "109 next 1 39 108\n"
    "\n"
    "; stmt_2_2\n"
    "110 not 1 81\n"
    "111 and 1 41 110\n"
    "112 ite 1 39 80 111\n"
    "113 next 1 41 112\n"
    "\n"
    "; stmt_2_3\n"
    "114 not 1 82\n"
    "115 and 1 43 114\n"
    "116 next 1 43 115\n"
    "\n"
    "; stmt_3_0\n"
    "117 not 1 83\n"
    "118 and 1 45 117\n"
    "119 next 1 45 118\n"
    "\n"
    "; stmt_3_1\n"
    "120 not 1 84\n"
    "121 and 1 47 120\n"
    "122 ite 1 45 83 121\n"
    "123 ite 1 49 85 122\n"
    "124 next 1 47 123\n"
    "\n"
    "; stmt_3_2\n"
    "125 not 1 85\n"
    "126 and 1 49 125\n"
    "127 ite 1 47 84 126\n"
    "128 next 1 49 127\n"
    "\n"
    "; stmt_3_3\n"
    "129 not 1 86\n"
    "130 and 1 51 129\n"
    "131 next 1 51 130\n\n",
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

  ASSERT_EQ(vector<string>({"30", "32", "34", "36"}), encoder->nids_stmt[1]);
  ASSERT_EQ(vector<string>({"38", "40", "42", "44"}), encoder->nids_stmt[2]);
  ASSERT_EQ(vector<string>({"46", "48", "50", "52"}), encoder->nids_stmt[3]);

  ASSERT_EQ(vector<string>({"76", "77", "78", "79"}), encoder->nids_exec[1]);
  ASSERT_EQ(vector<string>({"80", "81", "82", "83"}), encoder->nids_exec[2]);
  ASSERT_EQ(vector<string>({"84", "85", "86", "87"}), encoder->nids_exec[3]);

  ASSERT_EQ(
    "; update statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_1_0\n"
    "88 not 1 76\n"
    "89 and 1 30 88\n"
    "90 next 1 30 89\n"
    "\n"
    "; stmt_1_1\n"
    "91 not 1 77\n"
    "92 and 1 32 91\n"
    "93 ite 1 30 76 92\n"
    "94 ne 1 16 6\n"
    "95 and 1 78 94\n"
    "96 ite 1 34 95 93\n"
    "97 next 1 32 96\n"
    "\n"
    "; stmt_1_2\n"
    "98 not 1 78\n"
    "99 and 1 34 98\n"
    "100 ite 1 32 77 99\n"
    "101 next 1 34 100\n"
    "\n"
    "; stmt_1_3\n"
    "102 not 1 79\n"
    "103 and 1 36 102\n"
    "104 not 1 94\n"
    "105 and 1 78 104\n"
    "106 ite 1 34 105 103\n"
    "107 next 1 36 106\n"
    "\n"
    "; stmt_2_0\n"
    "108 not 1 80\n"
    "109 and 1 38 108\n"
    "110 next 1 38 109\n"
    "\n"
    "; stmt_2_1\n"
    "111 not 1 81\n"
    "112 and 1 40 111\n"
    "113 ite 1 38 80 112\n"
    "114 ne 1 18 6\n"
    "115 and 1 82 114\n"
    "116 ite 1 42 115 113\n"
    "117 next 1 40 116\n"
    "\n"
    "; stmt_2_2\n"
    "118 not 1 82\n"
    "119 and 1 42 118\n"
    "120 ite 1 40 81 119\n"
    "121 next 1 42 120\n"
    "\n"
    "; stmt_2_3\n"
    "122 not 1 83\n"
    "123 and 1 44 122\n"
    "124 not 1 114\n"
    "125 and 1 82 124\n"
    "126 ite 1 42 125 123\n"
    "127 next 1 44 126\n"
    "\n"
    "; stmt_3_0\n"
    "128 not 1 84\n"
    "129 and 1 46 128\n"
    "130 next 1 46 129\n"
    "\n"
    "; stmt_3_1\n"
    "131 not 1 85\n"
    "132 and 1 48 131\n"
    "133 ite 1 46 84 132\n"
    "134 ne 1 20 6\n"
    "135 and 1 86 134\n"
    "136 ite 1 50 135 133\n"
    "137 next 1 48 136\n"
    "\n"
    "; stmt_3_2\n"
    "138 not 1 86\n"
    "139 and 1 50 138\n"
    "140 ite 1 48 85 139\n"
    "141 next 1 50 140\n"
    "\n"
    "; stmt_3_3\n"
    "142 not 1 87\n"
    "143 and 1 52 142\n"
    "144 not 1 134\n"
    "145 and 1 86 144\n"
    "146 ite 1 50 145 143\n"
    "147 next 1 52 146\n\n",
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

  ASSERT_EQ(vector<string>({"30", "32", "34", "36"}), encoder->nids_stmt[1]);
  ASSERT_EQ(vector<string>({"38", "40", "42", "44"}), encoder->nids_stmt[2]);
  ASSERT_EQ(vector<string>({"46", "48", "50", "52"}), encoder->nids_stmt[3]);

  ASSERT_EQ(vector<string>({"76", "77", "78", "79"}), encoder->nids_exec[1]);
  ASSERT_EQ(vector<string>({"80", "81", "82", "83"}), encoder->nids_exec[2]);
  ASSERT_EQ(vector<string>({"84", "85", "86", "87"}), encoder->nids_exec[3]);

  ASSERT_EQ(
    "; update statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_1_0\n"
    "88 not 1 76\n"
    "89 and 1 30 88\n"
    "90 ne 1 16 6\n"
    "91 and 1 78 90\n"
    "92 ite 1 34 91 89\n"
    "93 next 1 30 92\n"
    "\n"
    "; stmt_1_1\n"
    "94 not 1 77\n"
    "95 and 1 32 94\n"
    "96 ite 1 30 76 95\n"
    "97 next 1 32 96\n"
    "\n"
    "; stmt_1_2\n"
    "98 not 1 78\n"
    "99 and 1 34 98\n"
    "100 ite 1 32 77 99\n"
    "101 next 1 34 100\n"
    "\n"
    "; stmt_1_3\n"
    "102 not 1 79\n"
    "103 and 1 36 102\n"
    "104 not 1 90\n"
    "105 and 1 78 104\n"
    "106 ite 1 34 105 103\n"
    "107 next 1 36 106\n"
    "\n"
    "; stmt_2_0\n"
    "108 not 1 80\n"
    "109 and 1 38 108\n"
    "110 ne 1 18 6\n"
    "111 and 1 82 110\n"
    "112 ite 1 42 111 109\n"
    "113 next 1 38 112\n"
    "\n"
    "; stmt_2_1\n"
    "114 not 1 81\n"
    "115 and 1 40 114\n"
    "116 ite 1 38 80 115\n"
    "117 next 1 40 116\n"
    "\n"
    "; stmt_2_2\n"
    "118 not 1 82\n"
    "119 and 1 42 118\n"
    "120 ite 1 40 81 119\n"
    "121 next 1 42 120\n"
    "\n"
    "; stmt_2_3\n"
    "122 not 1 83\n"
    "123 and 1 44 122\n"
    "124 not 1 110\n"
    "125 and 1 82 124\n"
    "126 ite 1 42 125 123\n"
    "127 next 1 44 126\n"
    "\n"
    "; stmt_3_0\n"
    "128 not 1 84\n"
    "129 and 1 46 128\n"
    "130 ne 1 20 6\n"
    "131 and 1 86 130\n"
    "132 ite 1 50 131 129\n"
    "133 next 1 46 132\n"
    "\n"
    "; stmt_3_1\n"
    "134 not 1 85\n"
    "135 and 1 48 134\n"
    "136 ite 1 46 84 135\n"
    "137 next 1 48 136\n"
    "\n"
    "; stmt_3_2\n"
    "138 not 1 86\n"
    "139 and 1 50 138\n"
    "140 ite 1 48 85 139\n"
    "141 next 1 50 140\n"
    "\n"
    "; stmt_3_3\n"
    "142 not 1 87\n"
    "143 and 1 52 142\n"
    "144 not 1 130\n"
    "145 and 1 86 144\n"
    "146 ite 1 50 145 143\n"
    "147 next 1 52 146\n\n",
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

  ASSERT_EQ(vector<string>({"30", "32", "34", "36", "38"}), encoder->nids_stmt[1]);
  ASSERT_EQ(vector<string>({"40", "42", "44", "46", "48"}), encoder->nids_stmt[2]);
  ASSERT_EQ(vector<string>({"50", "52", "54", "56", "58"}), encoder->nids_stmt[3]);

  ASSERT_EQ(vector<string>({"82", "83", "84", "85", "86"}), encoder->nids_exec[1]);
  ASSERT_EQ(vector<string>({"87", "88", "89", "90", "91"}), encoder->nids_exec[2]);
  ASSERT_EQ(vector<string>({"92", "93", "94", "95", "96"}), encoder->nids_exec[3]);

  ASSERT_EQ(
    "; update statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; stmt_1_0\n"
    "97 not 1 82\n"
    "98 and 1 30 97\n"
    "99 next 1 30 98\n"
    "\n"
    "; stmt_1_1\n"
    "100 not 1 83\n"
    "101 and 1 32 100\n"
    "102 ite 1 30 82 101\n"
    "103 eq 1 16 6\n"
    "104 and 1 84 103\n"
    "105 ite 1 34 104 102\n"
    "106 ne 1 16 6\n"
    "107 and 1 85 106\n"
    "108 ite 1 36 107 105\n"
    "109 next 1 32 108\n"
    "\n"
    "; stmt_1_2\n"
    "110 not 1 84\n"
    "111 and 1 34 110\n"
    "112 ite 1 32 83 111\n"
    "113 next 1 34 112\n"
    "\n"
    "; stmt_1_3\n"
    "114 not 1 85\n"
    "115 and 1 36 114\n"
    "116 not 1 103\n"
    "117 and 1 84 116\n"
    "118 ite 1 34 117 115\n"
    "119 next 1 36 118\n"
    "\n"
    "; stmt_1_4\n"
    "120 not 1 86\n"
    "121 and 1 38 120\n"
    "122 not 1 106\n"
    "123 and 1 85 122\n"
    "124 ite 1 36 123 121\n"
    "125 next 1 38 124\n"
    "\n"
    "; stmt_2_0\n"
    "126 not 1 87\n"
    "127 and 1 40 126\n"
    "128 next 1 40 127\n"
    "\n"
    "; stmt_2_1\n"
    "129 not 1 88\n"
    "130 and 1 42 129\n"
    "131 ite 1 40 87 130\n"
    "132 eq 1 18 6\n"
    "133 and 1 89 132\n"
    "134 ite 1 44 133 131\n"
    "135 ne 1 18 6\n"
    "136 and 1 90 135\n"
    "137 ite 1 46 136 134\n"
    "138 next 1 42 137\n"
    "\n"
    "; stmt_2_2\n"
    "139 not 1 89\n"
    "140 and 1 44 139\n"
    "141 ite 1 42 88 140\n"
    "142 next 1 44 141\n"
    "\n"
    "; stmt_2_3\n"
    "143 not 1 90\n"
    "144 and 1 46 143\n"
    "145 not 1 132\n"
    "146 and 1 89 145\n"
    "147 ite 1 44 146 144\n"
    "148 next 1 46 147\n"
    "\n"
    "; stmt_2_4\n"
    "149 not 1 91\n"
    "150 and 1 48 149\n"
    "151 not 1 135\n"
    "152 and 1 90 151\n"
    "153 ite 1 46 152 150\n"
    "154 next 1 48 153\n"
    "\n"
    "; stmt_3_0\n"
    "155 not 1 92\n"
    "156 and 1 50 155\n"
    "157 next 1 50 156\n"
    "\n"
    "; stmt_3_1\n"
    "158 not 1 93\n"
    "159 and 1 52 158\n"
    "160 ite 1 50 92 159\n"
    "161 eq 1 20 6\n"
    "162 and 1 94 161\n"
    "163 ite 1 54 162 160\n"
    "164 ne 1 20 6\n"
    "165 and 1 95 164\n"
    "166 ite 1 56 165 163\n"
    "167 next 1 52 166\n"
    "\n"
    "; stmt_3_2\n"
    "168 not 1 94\n"
    "169 and 1 54 168\n"
    "170 ite 1 52 93 169\n"
    "171 next 1 54 170\n"
    "\n"
    "; stmt_3_3\n"
    "172 not 1 95\n"
    "173 and 1 56 172\n"
    "174 not 1 161\n"
    "175 and 1 94 174\n"
    "176 ite 1 54 175 173\n"
    "177 next 1 56 176\n"
    "\n"
    "; stmt_3_4\n"
    "178 not 1 96\n"
    "179 and 1 58 178\n"
    "180 not 1 164\n"
    "181 and 1 95 180\n"
    "182 ite 1 56 181 179\n"
    "183 next 1 58 182\n\n",
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
TEST_F(Btor2EncoderTest, add_state_update_accu)
{
  add_instruction_set(3);

  init_statement_activation(true);

  for (word thread = 1; thread <= encoder->num_threads; thread++)
    {
      string thread_str = to_string(thread);

      encoder->thread = thread;

      encoder->update_accu = true;

      encoder->add_state_update(
        encoder->nids_accu[encoder->thread],
        "accu_" + thread_str,
        encoder->alters_accu);

      unsigned long nid = encoder->node;

      string nid_0_ite = to_string(nid - 16);
      string nid_2_add = to_string(nid - 15);
      string nid_2_ite = to_string(nid - 14);
      string nid_3_addi = to_string(nid - 13);
      string nid_3_ite = to_string(nid - 12);
      string nid_4_sub = to_string(nid - 11);
      string nid_4_ite = to_string(nid - 10);
      string nid_5_subi = to_string(nid - 9);
      string nid_5_ite = to_string(nid - 8);
      string nid_6_cmp = to_string(nid - 7);
      string nid_6_ite = to_string(nid - 6);
      string nid_13_mem = to_string(nid - 5);
      string nid_14_eq = to_string(nid - 4);
      string nid_14_cas = to_string(nid - 3);
      string nid_14_ite = to_string(nid - 2);
      string nid_next = to_string(nid - 1);

      ASSERT_EQ(
        "; accu_" + thread_str + "\n"
        + (thread > 1 ? "" : "507 read 2 14 7\n")
        + nid_0_ite  + " ite 1 " + encoder->nids_exec[thread][0] + " 507 " + encoder->nids_accu[thread] + " " + thread_str + ":0:LOAD:1\n"
        + nid_2_add  + " add 2 " + encoder->nids_accu[thread] + " 507\n"
        + nid_2_ite  + " ite 1 " + encoder->nids_exec[thread][2] + " " + nid_2_add + " " + nid_0_ite + " " + thread_str + ":2:ADD:1\n"
        + nid_3_addi + " add 2 " + encoder->nids_accu[thread] + " 7\n"
        + nid_3_ite  + " ite 1 " + encoder->nids_exec[thread][3] + " " + nid_3_addi + " " + nid_2_ite + " " + thread_str + ":3:ADDI:1\n"
        + nid_4_sub  + " sub 2 " + encoder->nids_accu[thread] + " 507\n"
        + nid_4_ite  + " ite 1 " + encoder->nids_exec[thread][4] + " " + nid_4_sub + " " + nid_3_ite + " " + thread_str + ":4:SUB:1\n"
        + nid_5_subi + " sub 2 " + encoder->nids_accu[thread] + " 7\n"
        + nid_5_ite  + " ite 1 " + encoder->nids_exec[thread][5] + " " + nid_5_subi + " " + nid_4_ite + " " + thread_str + ":5:SUBI:1\n"
        + nid_6_cmp  + " sub 2 " + encoder->nids_accu[thread] + " 507\n"
        + nid_6_ite  + " ite 1 " + encoder->nids_exec[thread][6] + " " + nid_6_cmp + " " + nid_5_ite + " " + thread_str + ":6:CMP:1\n"
        + nid_13_mem + " ite 1 " + encoder->nids_exec[thread][13] + " 507 " + nid_6_ite + " " + thread_str + ":13:MEM:1\n"
        + nid_14_eq  + " eq 1 "  + encoder->nids_mem[thread] + " 507\n"
        + nid_14_cas + " ite 1 " + nid_14_eq + " 7 6\n"
        + nid_14_ite + " ite 1 " + encoder->nids_exec[thread][14] + " " + nid_14_cas + " " + nid_13_mem + " " + thread_str + ":14:CAS:1\n"
        + nid_next   + " next 2 " + encoder->nids_accu[thread] + " " + nid_14_ite + "\n\n",
        encoder->formula.str());

      encoder->formula.str("");
    }
}

TEST_F(Btor2EncoderTest, add_state_update_mem)
{
  add_instruction_set(3);

  init_statement_activation(true);

  for (word thread = 1; thread <= encoder->num_threads; thread++)
    {
      string thread_str = to_string(thread);

      encoder->thread = thread;

      encoder->add_state_update(
        encoder->nids_mem[encoder->thread],
        "mem_" + thread_str,
        encoder->alters_mem);

      unsigned long nid = encoder->node;

      string nid_13_ite = to_string(nid - 2);
      string nid_next = to_string(nid - 1);

      ASSERT_EQ(
        "; mem_" + thread_str + "\n"
        + (thread > 1 ? "" : "507 read 2 14 7\n")
        + nid_13_ite + " ite 1 " + encoder->nids_exec[thread][13] + " 507 " + encoder->nids_mem[thread] + " " + thread_str + ":13:MEM:1\n"
        + nid_next +   " next 2 " + encoder->nids_mem[thread] + " " + nid_13_ite + "\n\n",
        encoder->formula.str());

      encoder->formula.str("");
    }
}

TEST_F(Btor2EncoderTest, add_state_update_heap)
{
  add_instruction_set(3);

  init_statement_activation(true);

  encoder->thread = 0;

  encoder->update_accu = false;

  encoder->add_state_update(
    encoder->nid_heap,
    "heap",
    encoder->alters_heap);

  unsigned long nid = encoder->node;

  string nid_1_1_ite = to_string(nid - 14);
  string nid_1_14_eq = to_string(nid - 12);
  string nid_1_14_cas = to_string(nid - 11);
  string nid_1_14_ite = to_string(nid - 10);
  string nid_2_1_ite = to_string(nid - 9);
  string nid_2_14_eq = to_string(nid - 8);
  string nid_2_14_cas = to_string(nid - 7);
  string nid_2_14_ite = to_string(nid - 6);
  string nid_3_1_ite = to_string(nid - 5);
  string nid_3_14_eq = to_string(nid - 4);
  string nid_3_14_cas = to_string(nid - 3);
  string nid_3_14_ite = to_string(nid - 2);
  string nid_next = to_string(nid - 1);

  ASSERT_EQ(
    "; heap\n"
    "507 write 3 14 7 15\n"
    + nid_1_1_ite  + " ite 1 " + encoder->nids_exec[1][1] + " 507 14 1:1:STORE:1\n"
    "509 read 2 14 7\n"
    + nid_1_14_eq  + " eq 1 "  + encoder->nids_mem[1] + " 509\n"
    + nid_1_14_cas + " ite 1 " + nid_1_14_eq + " 507 14\n"
    + nid_1_14_ite + " ite 1 " + encoder->nids_exec[1][14] + " " + nid_1_14_cas + " " + nid_1_1_ite + " 1:14:CAS:1\n"
    + nid_2_1_ite  + " ite 1 " + encoder->nids_exec[2][1] + " 507 " + nid_1_14_ite + " 2:1:STORE:1\n"
    + nid_2_14_eq  + " eq 1 "  + encoder->nids_mem[2] + " 509\n"
    + nid_2_14_cas + " ite 1 " + nid_2_14_eq + " 507 14\n"
    + nid_2_14_ite + " ite 1 " + encoder->nids_exec[2][14] + " " + nid_2_14_cas + " " + nid_2_1_ite + " 2:14:CAS:1\n"
    + nid_3_1_ite  + " ite 1 " + encoder->nids_exec[3][1] + " 507 " + nid_2_14_ite + " 3:1:STORE:1\n"
    + nid_3_14_eq  + " eq 1 "  + encoder->nids_mem[3] + " 509\n"
    + nid_3_14_cas + " ite 1 " + nid_3_14_eq + " 507 14\n"
    + nid_3_14_ite + " ite 1 " + encoder->nids_exec[3][14] + " " + nid_3_14_cas + " " + nid_3_1_ite + " 3:14:CAS:1\n"
    + nid_next     + " next 2 14 " + nid_3_14_ite + "\n\n",
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
    "507 read 2 14 7\n"
    "508 ite 1 165 507 15 1:0:LOAD:1\n"
    "509 add 2 15 507\n"
    "510 ite 1 167 509 508 1:2:ADD:1\n"
    "511 add 2 15 7\n"
    "512 ite 1 168 511 510 1:3:ADDI:1\n"
    "513 sub 2 15 507\n"
    "514 ite 1 169 513 512 1:4:SUB:1\n"
    "515 sub 2 15 7\n"
    "516 ite 1 170 515 514 1:5:SUBI:1\n"
    "517 sub 2 15 507\n"
    "518 ite 1 171 517 516 1:6:CMP:1\n"
    "519 ite 1 178 507 518 1:13:MEM:1\n"
    "520 eq 1 21 507\n"
    "521 ite 1 520 7 6\n"
    "522 ite 1 179 521 519 1:14:CAS:1\n"
    "523 next 2 15 522\n"
    "\n"
    "; accu_2\n"
    "524 ite 1 182 507 17 2:0:LOAD:1\n"
    "525 add 2 17 507\n"
    "526 ite 1 184 525 524 2:2:ADD:1\n"
    "527 add 2 17 7\n"
    "528 ite 1 185 527 526 2:3:ADDI:1\n"
    "529 sub 2 17 507\n"
    "530 ite 1 186 529 528 2:4:SUB:1\n"
    "531 sub 2 17 7\n"
    "532 ite 1 187 531 530 2:5:SUBI:1\n"
    "533 sub 2 17 507\n"
    "534 ite 1 188 533 532 2:6:CMP:1\n"
    "535 ite 1 195 507 534 2:13:MEM:1\n"
    "536 eq 1 23 507\n"
    "537 ite 1 536 7 6\n"
    "538 ite 1 196 537 535 2:14:CAS:1\n"
    "539 next 2 17 538\n"
    "\n"
    "; accu_3\n"
    "540 ite 1 199 507 19 3:0:LOAD:1\n"
    "541 add 2 19 507\n"
    "542 ite 1 201 541 540 3:2:ADD:1\n"
    "543 add 2 19 7\n"
    "544 ite 1 202 543 542 3:3:ADDI:1\n"
    "545 sub 2 19 507\n"
    "546 ite 1 203 545 544 3:4:SUB:1\n"
    "547 sub 2 19 7\n"
    "548 ite 1 204 547 546 3:5:SUBI:1\n"
    "549 sub 2 19 507\n"
    "550 ite 1 205 549 548 3:6:CMP:1\n"
    "551 ite 1 212 507 550 3:13:MEM:1\n"
    "552 eq 1 25 507\n"
    "553 ite 1 552 7 6\n"
    "554 ite 1 213 553 551 3:14:CAS:1\n"
    "555 next 2 19 554\n"
    "\n"
    "; update CAS memory register ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; mem_1\n"
    "556 ite 1 178 507 21 1:13:MEM:1\n"
    "557 next 2 21 556\n"
    "\n"
    "; mem_2\n"
    "558 ite 1 195 507 23 2:13:MEM:1\n"
    "559 next 2 23 558\n"
    "\n"
    "; mem_3\n"
    "560 ite 1 212 507 25 3:13:MEM:1\n"
    "561 next 2 25 560\n"
    "\n"
    "; update heap ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; heap\n"
    "562 write 3 14 7 15\n"
    "563 ite 1 166 562 14 1:1:STORE:1\n"
    "564 eq 1 21 507\n"
    "565 ite 1 564 562 14\n"
    "566 ite 1 179 565 563 1:14:CAS:1\n"
    "567 ite 1 183 562 566 2:1:STORE:1\n"
    "568 eq 1 23 507\n"
    "569 ite 1 568 562 14\n"
    "570 ite 1 196 569 567 2:14:CAS:1\n"
    "571 ite 1 200 562 570 3:1:STORE:1\n"
    "572 eq 1 25 507\n"
    "573 ite 1 572 562 14\n"
    "574 ite 1 213 573 571 3:14:CAS:1\n"
    "575 next 2 14 574\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  init_statement_activation(true);

  verbose = false;
  encoder->add_state_update();
  verbose = true;

  ASSERT_EQ(
    "507 read 2 14 7\n"
    "508 ite 1 165 507 15\n"
    "509 add 2 15 507\n"
    "510 ite 1 167 509 508\n"
    "511 add 2 15 7\n"
    "512 ite 1 168 511 510\n"
    "513 sub 2 15 507\n"
    "514 ite 1 169 513 512\n"
    "515 sub 2 15 7\n"
    "516 ite 1 170 515 514\n"
    "517 sub 2 15 507\n"
    "518 ite 1 171 517 516\n"
    "519 ite 1 178 507 518\n"
    "520 eq 1 21 507\n"
    "521 ite 1 520 7 6\n"
    "522 ite 1 179 521 519\n"
    "523 next 2 15 522\n"
    "\n"
    "524 ite 1 182 507 17\n"
    "525 add 2 17 507\n"
    "526 ite 1 184 525 524\n"
    "527 add 2 17 7\n"
    "528 ite 1 185 527 526\n"
    "529 sub 2 17 507\n"
    "530 ite 1 186 529 528\n"
    "531 sub 2 17 7\n"
    "532 ite 1 187 531 530\n"
    "533 sub 2 17 507\n"
    "534 ite 1 188 533 532\n"
    "535 ite 1 195 507 534\n"
    "536 eq 1 23 507\n"
    "537 ite 1 536 7 6\n"
    "538 ite 1 196 537 535\n"
    "539 next 2 17 538\n"
    "\n"
    "540 ite 1 199 507 19\n"
    "541 add 2 19 507\n"
    "542 ite 1 201 541 540\n"
    "543 add 2 19 7\n"
    "544 ite 1 202 543 542\n"
    "545 sub 2 19 507\n"
    "546 ite 1 203 545 544\n"
    "547 sub 2 19 7\n"
    "548 ite 1 204 547 546\n"
    "549 sub 2 19 507\n"
    "550 ite 1 205 549 548\n"
    "551 ite 1 212 507 550\n"
    "552 eq 1 25 507\n"
    "553 ite 1 552 7 6\n"
    "554 ite 1 213 553 551\n"
    "555 next 2 19 554\n"
    "\n"
    "556 ite 1 178 507 21\n"
    "557 next 2 21 556\n"
    "\n"
    "558 ite 1 195 507 23\n"
    "559 next 2 23 558\n"
    "\n"
    "560 ite 1 212 507 25\n"
    "561 next 2 25 560\n"
    "\n"
    "562 write 3 14 7 15\n"
    "563 ite 1 166 562 14\n"
    "564 eq 1 21 507\n"
    "565 ite 1 564 562 14\n"
    "566 ite 1 179 565 563\n"
    "567 ite 1 183 562 566\n"
    "568 eq 1 23 507\n"
    "569 ite 1 568 562 14\n"
    "570 ite 1 196 569 567\n"
    "571 ite 1 200 562 570\n"
    "572 eq 1 25 507\n"
    "573 ite 1 572 562 14\n"
    "574 ite 1 213 573 571\n"
    "575 next 2 14 574\n\n",
    encoder->formula.str());
}

// void preprocess ();
TEST_F(Btor2EncoderTest, preprocess)
{
  add_dummy_programs(3, 3);

  ASSERT_EQ(
    NIDMap({{0, ""}, {1, ""}, {2, ""}, {3, ""}}),
    encoder->nids_const);
}

// std::string load(Load &);
TEST_F(Btor2EncoderTest, load)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  Load l(1);

  ASSERT_EQ("33", encoder->load(l));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ("33 read 2 14 7\n", encoder->formula.str());

  /* another load from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("33", encoder->load(l));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ("", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  l.indirect = true;

  ASSERT_EQ("34", encoder->load(l));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "34"}}), encoder->nids_load_indirect);
  ASSERT_EQ("34 read 2 14 33\n", encoder->formula.str());

  /* another load from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("34", encoder->load(l));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "34"}}), encoder->nids_load_indirect);
  ASSERT_EQ("", encoder->formula.str());
}

// std::string store(Store &);
TEST_F(Btor2EncoderTest, store)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  Store s(1);

  encoder->thread = 1;

  ASSERT_EQ("33", encoder->store(s));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_store);
  ASSERT_EQ("33 write 3 14 7 15\n", encoder->formula.str());

  /* another store to the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("33", encoder->store(s));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_store);
  ASSERT_EQ("", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  s.indirect = true;

  ASSERT_EQ("35", encoder->store(s));
  ASSERT_EQ(NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_store_indirect);
  ASSERT_EQ(
    "34 read 2 14 7\n"
    "35 write 3 14 34 15\n",
    encoder->formula.str());

  /* another store to the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("35", encoder->store(s));
  ASSERT_EQ(NIDMap({{1, "34"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "35"}}), encoder->nids_store_indirect);
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

  ASSERT_EQ("34", encoder->encode(a));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(
    "33 read 2 14 7\n"
    "34 add 2 15 33\n",
    encoder->formula.str());

  /* another ADD from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("35", encoder->encode(a));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ("35 add 2 15 33\n", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  a.indirect = true;

  ASSERT_EQ("37", encoder->encode(a));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "36"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "36 read 2 14 33\n"
    "37 add 2 15 36\n",
    encoder->formula.str());

  /* another ADD from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("38", encoder->encode(a));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "36"}}), encoder->nids_load_indirect);
  ASSERT_EQ("38 add 2 15 36\n", encoder->formula.str());
}

// virtual std::string encode (Addi &);
TEST_F(Btor2EncoderTest, ADDI)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Addi a(1);

  ASSERT_EQ("33", encoder->encode(a));
  ASSERT_EQ("33 add 2 15 7\n", encoder->formula.str());

  /* another ADDI with the same constant */
  encoder->formula.str("");

  ASSERT_EQ("34", encoder->encode(a));
  ASSERT_EQ("34 add 2 15 7\n", encoder->formula.str());
}

// virtual std::string encode (Sub &);
TEST_F(Btor2EncoderTest, SUB)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Sub s(1);

  ASSERT_EQ("34", encoder->encode(s));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(
    "33 read 2 14 7\n"
    "34 sub 2 15 33\n",
    encoder->formula.str());

  /* another SUB from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("35", encoder->encode(s));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ("35 sub 2 15 33\n", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  s.indirect = true;

  ASSERT_EQ("37", encoder->encode(s));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "36"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "36 read 2 14 33\n"
    "37 sub 2 15 36\n",
    encoder->formula.str());

  /* another SUB from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("38", encoder->encode(s));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "36"}}), encoder->nids_load_indirect);
  ASSERT_EQ("38 sub 2 15 36\n", encoder->formula.str());
}

// virtual std::string encode (Subi &);
TEST_F(Btor2EncoderTest, SUBI)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Subi s(1);

  ASSERT_EQ("33", encoder->encode(s));
  ASSERT_EQ("33 sub 2 15 7\n", encoder->formula.str());

  /* another SUBI with the same constant */
  encoder->formula.str("");

  ASSERT_EQ("34", encoder->encode(s));
  ASSERT_EQ("34 sub 2 15 7\n", encoder->formula.str());
}

// virtual std::string encode (Cmp &);
TEST_F(Btor2EncoderTest, CMP)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Cmp c(1);

  ASSERT_EQ("34", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(
    "33 read 2 14 7\n"
    "34 sub 2 15 33\n",
    encoder->formula.str());

  /* another CMP from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("35", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ("35 sub 2 15 33\n", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  c.indirect = true;

  ASSERT_EQ("37", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "36"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "36 read 2 14 33\n"
    "37 sub 2 15 36\n",
    encoder->formula.str());

  /* another CMP from the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("38", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "36"}}), encoder->nids_load_indirect);
  ASSERT_EQ("38 sub 2 15 36\n", encoder->formula.str());
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

  ASSERT_EQ("33", encoder->encode(j));
  ASSERT_EQ("33 eq 1 15 6\n", encoder->formula.str());
}

// virtual std::string encode (Jnz &);
TEST_F(Btor2EncoderTest, JNZ)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Jnz j(1);

  ASSERT_EQ("33", encoder->encode(j));
  ASSERT_EQ("33 ne 1 15 6\n", encoder->formula.str());
}

// virtual std::string encode (Js &);
TEST_F(Btor2EncoderTest, JS)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Js j(1);

  ASSERT_EQ("33", encoder->encode(j));
  ASSERT_EQ("33 slice 1 15 15 15\n", encoder->formula.str());
}

// virtual std::string encode (Jns &);
TEST_F(Btor2EncoderTest, JNS)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Jns j(1);

  ASSERT_EQ("34", encoder->encode(j));
  ASSERT_EQ(
    "33 slice 1 15 15 15\n"
    "34 not 1 33\n",
    encoder->formula.str());
}

// virtual std::string encode (Jnzns &);
TEST_F(Btor2EncoderTest, JNZNS)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  Jnzns j(1);

  ASSERT_EQ("37", encoder->encode(j));
  ASSERT_EQ(
    "34 ne 1 15 6\n"
    "35 slice 1 15 15 15\n"
    "36 not 1 35\n"
    "37 and 1 34 36\n",
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

  ASSERT_EQ("35", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(
    "33 read 2 14 7\n"
    "34 eq 1 17 33\n"
    "35 ite 1 34 7 6\n",
    encoder->formula.str());

  /* another CAS to the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("37", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(
    "36 eq 1 17 33\n"
    "37 ite 1 36 7 6\n",
    encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  c.indirect = true;

  ASSERT_EQ("40", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "38"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "38 read 2 14 33\n"
    "39 eq 1 17 38\n"
    "40 ite 1 39 7 6\n",
    encoder->formula.str());

  /* another CAS to the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("42", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "38"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "41 eq 1 17 38\n"
    "42 ite 1 41 7 6\n",
    encoder->formula.str());
}

TEST_F(Btor2EncoderTest, CAS_heap)
{
  add_dummy_programs(1, 1);

  init_statement_activation(true);

  encoder->thread = 1;

  encoder->update_accu = false;

  Cas c(1);

  ASSERT_EQ("36", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(
    "33 read 2 14 7\n"
    "34 eq 1 17 33\n"
    "35 write 3 14 7 15\n"
    "36 ite 1 34 35 14\n",
    encoder->formula.str());

  /* another CAS to the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("38", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(
    "37 eq 1 17 33\n"
    "38 ite 1 37 35 14\n",
    encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  c.indirect = true;

  ASSERT_EQ("42", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "39"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "39 read 2 14 33\n"
    "40 eq 1 17 39\n"
    "41 write 3 14 33 15\n"
    "42 ite 1 40 41 14\n",
    encoder->formula.str());

  /* another CAS to the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("44", encoder->encode(c));
  ASSERT_EQ(NIDMap({{1, "33"}}), encoder->nids_load);
  ASSERT_EQ(NIDMap({{1, "39"}}), encoder->nids_load_indirect);
  ASSERT_EQ(
    "43 eq 1 17 39\n"
    "44 ite 1 43 41 14\n",
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
