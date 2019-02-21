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

  void add_declerations ()
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->formula.str("");
    }

  void init_states ()
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->add_bound();
      encoder->declare_states();
      encoder->formula.str("");
    }

  void init_thread_scheduling ()
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->add_bound();
      encoder->declare_states();
      encoder->add_thread_scheduling();
      encoder->formula.str("");
    }

  void init_synchronization_constraints ()
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->add_bound();
      encoder->declare_states();
      encoder->add_thread_scheduling();
      encoder->add_synchronization_constraints();
      encoder->formula.str("");
    }

  void init_statement_execution ()
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->add_bound();
      encoder->declare_states();
      encoder->add_thread_scheduling();
      encoder->add_synchronization_constraints();
      encoder->add_statement_execution();
      encoder->formula.str("");
    }

  void init_statement_activation ()
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->add_bound();
      encoder->declare_states();
      encoder->add_thread_scheduling();
      encoder->add_synchronization_constraints();
      encoder->add_statement_execution();
      encoder->add_statement_activation();
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
  add_declerations();

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

  add_declerations();

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

  add_declerations();

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

  add_declerations();

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

  init_states();

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

  init_states();

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

  init_thread_scheduling();

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

  init_thread_scheduling();

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

  init_thread_scheduling();

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

  init_thread_scheduling();

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

  init_synchronization_constraints();

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

  init_synchronization_constraints();

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

  init_statement_execution();

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

  init_statement_execution();

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

  init_statement_execution();

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

  init_statement_execution();

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

  init_statement_execution();

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

  init_statement_execution();

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

// void add_state_update ();
TEST_F(Btor2EncoderTest, add_state_update)
{
}

// std::string load(Load &);
TEST_F(Btor2EncoderTest, load)
{
  add_dummy_programs(1, 1);

  init_states();

  Load l = Load(1);

  ASSERT_EQ("23", encoder->load(l));
  ASSERT_EQ("23 read 2 14 7\n", encoder->formula.str());

  /* another load of the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("23", encoder->load(l));
  ASSERT_EQ("", encoder->formula.str());

  /* indirect */
  encoder->formula.str("");

  l.indirect = true;

  ASSERT_EQ("24", encoder->load(l));
  ASSERT_EQ(
    "24 read 2 14 23\n",
    encoder->formula.str());

  /* another load of the same memory address */
  encoder->formula.str("");

  ASSERT_EQ("24", encoder->load(l));
  ASSERT_EQ("", encoder->formula.str());
}

// void preprocess ();
TEST_F(Btor2EncoderTest, preprocess)
{
  add_dummy_programs(3, 3);

  ASSERT_EQ(
    NIDMap({{0, ""}, {1, ""}, {2, ""}, {3, ""}}),
    encoder->nids_const);
}

// virtual void encode (void);

// virtual std::string encode (Load &);

// virtual std::string encode (Store &);

// virtual std::string encode (Add &);

// virtual std::string encode (Addi &);

// virtual std::string encode (Sub &);

// virtual std::string encode (Subi &);

// virtual std::string encode (Cmp &);

// virtual std::string encode (Jmp &);

// virtual std::string encode (Jz &);

// virtual std::string encode (Jnz &);

// virtual std::string encode (Js &);

// virtual std::string encode (Jns &);

// virtual std::string encode (Jnzns &);

// virtual std::string encode (Mem &);

// virtual std::string encode (Cas &);

// virtual std::string encode (Sync &);

// virtual std::string encode (Exit &);

