#include <gtest/gtest.h>

#include "encoder.hh"

using namespace std;

typedef map<word, string> NIDMap;

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

  void add_declerations ()
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->formula.str("");
    }

  void add_states ()
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->declare_states();
      encoder->formula.str("");
    }

  void add_thread_scheduling ()
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->declare_states();
      encoder->add_thread_scheduling();
      encoder->formula.str("");
    }

  void add_synchronization_constraints ()
    {
      encoder->declare_sorts();
      encoder->declare_constants();
      encoder->declare_states();
      encoder->add_thread_scheduling();
      encoder->add_synchronization_constraints();
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
    encoder->constants);
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
  ASSERT_EQ(NIDMap({{1, "11"}, {2, "13"}, {3, "15"}}), encoder->nid_accu);
  ASSERT_EQ(NIDMap({{1, "17"}, {2, "19"}, {3, "21"}}), encoder->nid_mem);
  ASSERT_EQ("23", encoder->nid_exit);
  ASSERT_EQ(vector<string>({"25", "27", "29"}), encoder->nid_stmt[1]);
  ASSERT_EQ(vector<string>({"31", "33", "35"}), encoder->nid_stmt[2]);
  ASSERT_EQ(vector<string>({"37", "39", "41"}), encoder->nid_stmt[3]);
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

  add_states();

  encoder->add_thread_scheduling();

  ASSERT_EQ(NIDMap({{1, "43"}, {2, "44"}, {3, "45"}}), encoder->nid_thread);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; thread scheduling\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "43 input 1 thread_1\n"
    "44 input 1 thread_2\n"
    "45 input 1 thread_3\n"
    "\n"
    "; cardinality constraint\n"
    "46 or 1 43 44\n"
    "47 or 1 45 46\n"
    "48 or 1 23 47\n"
    "49 constraint 48\n"
    "50 nand 1 43 44\n"
    "51 nand 1 43 45\n"
    "52 nand 1 43 23\n"
    "53 nand 1 44 45\n"
    "54 nand 1 44 23\n"
    "55 nand 1 45 23\n"
    "56 and 1 50 51\n"
    "57 and 1 52 56\n"
    "58 and 1 53 57\n"
    "59 and 1 54 58\n"
    "60 and 1 55 59\n"
    "61 constraint 60\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  add_states();

  verbose = false;
  encoder->add_thread_scheduling();
  verbose = true;

  ASSERT_EQ(
    "43 input 1 thread_1\n"
    "44 input 1 thread_2\n"
    "45 input 1 thread_3\n"
    "\n"
    "46 or 1 43 44\n"
    "47 or 1 45 46\n"
    "48 or 1 23 47\n"
    "49 constraint 48\n"
    "50 nand 1 43 44\n"
    "51 nand 1 43 45\n"
    "52 nand 1 43 23\n"
    "53 nand 1 44 45\n"
    "54 nand 1 44 23\n"
    "55 nand 1 45 23\n"
    "56 and 1 50 51\n"
    "57 and 1 52 56\n"
    "58 and 1 53 57\n"
    "59 and 1 54 58\n"
    "60 and 1 55 59\n"
    "61 constraint 60\n\n",
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

  add_thread_scheduling();

  encoder->add_synchronization_constraints();

  ASSERT_EQ(NIDMap({{1, "59"}, {2, "71"}}), encoder->nid_sync);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; synchronization constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; negated thread activation variables\n"
    "55 not 1 36 not_thread_1\n"
    "56 not 1 37 not_thread_2\n"
    "57 not 1 38 not_thread_3\n"
    "\n"
    "; synchronization condition sync_1\n"
    "58 and 1 24 28\n"
    "59 and 1 32 58 sync_1\n"
    "60 not 1 59 not_sync_1\n"
    "\n"
    "; disable threads waiting for barrier 1\n"
    "61 and 1 24 60\n"
    "62 implies 1 61 55\n"
    "63 constraint 62 sync_1_block_1\n"
    "\n"
    "64 and 1 28 60\n"
    "65 implies 1 64 56\n"
    "66 constraint 65 sync_1_block_2\n"
    "\n"
    "67 and 1 32 60\n"
    "68 implies 1 67 57\n"
    "69 constraint 68 sync_1_block_3\n"
    "\n"
    "; synchronization condition sync_2\n"
    "70 and 1 26 30\n"
    "71 and 1 34 70 sync_2\n"
    "72 not 1 71 not_sync_2\n"
    "\n"
    "; disable threads waiting for barrier 2\n"
    "73 and 1 26 72\n"
    "74 implies 1 73 55\n"
    "75 constraint 74 sync_2_block_1\n"
    "\n"
    "76 and 1 30 72\n"
    "77 implies 1 76 56\n"
    "78 constraint 77 sync_2_block_2\n"
    "\n"
    "79 and 1 34 72\n"
    "80 implies 1 79 57\n"
    "81 constraint 80 sync_2_block_3\n\n",
    encoder->formula.str());

  /* multiple calls to the same barrier */
  for (const auto & program : programs)
    for (size_t pc = 0; pc < 4; pc++)
      program->add(Instruction::Set::create("SYNC", pc % 2 + 1));

  reset_encoder(1);

  add_thread_scheduling();

  encoder->add_synchronization_constraints();

  ASSERT_EQ(
    vector<string>({"24", "26", "28", "30", "32", "34"}),
    encoder->nid_stmt[1]);
  ASSERT_EQ(
    vector<string>({"36", "38", "40", "42", "44", "46"}),
    encoder->nid_stmt[2]);
  ASSERT_EQ(
    vector<string>({"48", "50", "52", "54", "56", "58"}),
    encoder->nid_stmt[3]);
  ASSERT_EQ(NIDMap({{1, "89"}, {2, "107"}}), encoder->nid_sync);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; synchronization constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; negated thread activation variables\n"
    "79 not 1 60 not_thread_1\n"
    "80 not 1 61 not_thread_2\n"
    "81 not 1 62 not_thread_3\n"
    "\n"
    "; synchronization condition sync_1\n"
    "82 or 1 24 28\n"
    "83 or 1 32 82 thread_1@sync_1\n"
    "84 or 1 36 40\n"
    "85 or 1 44 84 thread_2@sync_1\n"
    "86 or 1 48 52\n"
    "87 or 1 56 86 thread_3@sync_1\n"
    "88 and 1 83 85\n"
    "89 and 1 87 88 sync_1\n"
    "90 not 1 89 not_sync_1\n"
    "\n"
    "; disable threads waiting for barrier 1\n"
    "91 and 1 83 90\n"
    "92 implies 1 91 79\n"
    "93 constraint 92 sync_1_block_1\n"
    "\n"
    "94 and 1 85 90\n"
    "95 implies 1 94 80\n"
    "96 constraint 95 sync_1_block_2\n"
    "\n"
    "97 and 1 87 90\n"
    "98 implies 1 97 81\n"
    "99 constraint 98 sync_1_block_3\n"
    "\n"
    "; synchronization condition sync_2\n"
    "100 or 1 26 30\n"
    "101 or 1 34 100 thread_1@sync_2\n"
    "102 or 1 38 42\n"
    "103 or 1 46 102 thread_2@sync_2\n"
    "104 or 1 50 54\n"
    "105 or 1 58 104 thread_3@sync_2\n"
    "106 and 1 101 103\n"
    "107 and 1 105 106 sync_2\n"
    "108 not 1 107 not_sync_2\n"
    "\n"
    "; disable threads waiting for barrier 2\n"
    "109 and 1 101 108\n"
    "110 implies 1 109 79\n"
    "111 constraint 110 sync_2_block_1\n"
    "\n"
    "112 and 1 103 108\n"
    "113 implies 1 112 80\n"
    "114 constraint 113 sync_2_block_2\n"
    "\n"
    "115 and 1 105 108\n"
    "116 implies 1 115 81\n"
    "117 constraint 116 sync_2_block_3\n\n",
    encoder->formula.str());

  /* barrier only for a subset of threads */
  for (size_t i = 0; i < programs.size() - 1; i++)
    programs[i]->add(Instruction::Set::create("SYNC", 3));

  reset_encoder(1);

  add_thread_scheduling();

  encoder->add_synchronization_constraints();

  ASSERT_EQ(
    vector<string>({"25", "27", "29", "31", "33", "35", "37"}),
    encoder->nid_stmt[1]);
  ASSERT_EQ(
    vector<string>({"39", "41", "43", "45", "47", "49", "51"}),
    encoder->nid_stmt[2]);
  ASSERT_EQ(
    vector<string>({"53", "55", "57", "59", "61", "63"}),
    encoder->nid_stmt[3]);
  ASSERT_EQ(NIDMap({{1, "94"}, {2, "112"}, {3, "125"}}), encoder->nid_sync);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; synchronization constraints\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; negated thread activation variables\n"
    "84 not 1 65 not_thread_1\n"
    "85 not 1 66 not_thread_2\n"
    "86 not 1 67 not_thread_3\n"
    "\n"
    "; synchronization condition sync_1\n"
    "87 or 1 25 29\n"
    "88 or 1 33 87 thread_1@sync_1\n"
    "89 or 1 39 43\n"
    "90 or 1 47 89 thread_2@sync_1\n"
    "91 or 1 53 57\n"
    "92 or 1 61 91 thread_3@sync_1\n"
    "93 and 1 88 90\n"
    "94 and 1 92 93 sync_1\n"
    "95 not 1 94 not_sync_1\n"
    "\n"
    "; disable threads waiting for barrier 1\n"
    "96 and 1 88 95\n"
    "97 implies 1 96 84\n"
    "98 constraint 97 sync_1_block_1\n"
    "\n"
    "99 and 1 90 95\n"
    "100 implies 1 99 85\n"
    "101 constraint 100 sync_1_block_2\n"
    "\n"
    "102 and 1 92 95\n"
    "103 implies 1 102 86\n"
    "104 constraint 103 sync_1_block_3\n"
    "\n"
    "; synchronization condition sync_2\n"
    "105 or 1 27 31\n"
    "106 or 1 35 105 thread_1@sync_2\n"
    "107 or 1 41 45\n"
    "108 or 1 49 107 thread_2@sync_2\n"
    "109 or 1 55 59\n"
    "110 or 1 63 109 thread_3@sync_2\n"
    "111 and 1 106 108\n"
    "112 and 1 110 111 sync_2\n"
    "113 not 1 112 not_sync_2\n"
    "\n"
    "; disable threads waiting for barrier 2\n"
    "114 and 1 106 113\n"
    "115 implies 1 114 84\n"
    "116 constraint 115 sync_2_block_1\n"
    "\n"
    "117 and 1 108 113\n"
    "118 implies 1 117 85\n"
    "119 constraint 118 sync_2_block_2\n"
    "\n"
    "120 and 1 110 113\n"
    "121 implies 1 120 86\n"
    "122 constraint 121 sync_2_block_3\n"
    "\n"
    "; synchronization condition sync_3\n"
    "123 or 1 65 66\n"
    "124 and 1 37 51\n"
    "125 and 1 123 124 sync_3\n"
    "126 not 1 125 not_sync_3\n"
    "\n"
    "; disable threads waiting for barrier 3\n"
    "127 and 1 37 126\n"
    "128 implies 1 127 84\n"
    "129 constraint 128 sync_3_block_1\n"
    "\n"
    "130 and 1 51 126\n"
    "131 implies 1 130 85\n"
    "132 constraint 131 sync_3_block_2\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  add_thread_scheduling();

  verbose = false;
  encoder->add_synchronization_constraints();
  verbose = true;

  ASSERT_EQ(
    "84 not 1 65 not_thread_1\n"
    "85 not 1 66 not_thread_2\n"
    "86 not 1 67 not_thread_3\n"
    "\n"
    "87 or 1 25 29\n"
    "88 or 1 33 87 thread_1@sync_1\n"
    "89 or 1 39 43\n"
    "90 or 1 47 89 thread_2@sync_1\n"
    "91 or 1 53 57\n"
    "92 or 1 61 91 thread_3@sync_1\n"
    "93 and 1 88 90\n"
    "94 and 1 92 93 sync_1\n"
    "95 not 1 94 not_sync_1\n"
    "\n"
    "96 and 1 88 95\n"
    "97 implies 1 96 84\n"
    "98 constraint 97 sync_1_block_1\n"
    "\n"
    "99 and 1 90 95\n"
    "100 implies 1 99 85\n"
    "101 constraint 100 sync_1_block_2\n"
    "\n"
    "102 and 1 92 95\n"
    "103 implies 1 102 86\n"
    "104 constraint 103 sync_1_block_3\n"
    "\n"
    "105 or 1 27 31\n"
    "106 or 1 35 105 thread_1@sync_2\n"
    "107 or 1 41 45\n"
    "108 or 1 49 107 thread_2@sync_2\n"
    "109 or 1 55 59\n"
    "110 or 1 63 109 thread_3@sync_2\n"
    "111 and 1 106 108\n"
    "112 and 1 110 111 sync_2\n"
    "113 not 1 112 not_sync_2\n"
    "\n"
    "114 and 1 106 113\n"
    "115 implies 1 114 84\n"
    "116 constraint 115 sync_2_block_1\n"
    "\n"
    "117 and 1 108 113\n"
    "118 implies 1 117 85\n"
    "119 constraint 118 sync_2_block_2\n"
    "\n"
    "120 and 1 110 113\n"
    "121 implies 1 120 86\n"
    "122 constraint 121 sync_2_block_3\n"
    "\n"
    "123 or 1 65 66\n"
    "124 and 1 37 51\n"
    "125 and 1 123 124 sync_3\n"
    "126 not 1 125 not_sync_3\n"
    "\n"
    "127 and 1 37 126\n"
    "128 implies 1 127 84\n"
    "129 constraint 128 sync_3_block_1\n"
    "\n"
    "130 and 1 51 126\n"
    "131 implies 1 130 85\n"
    "132 constraint 131 sync_3_block_2\n\n",
    encoder->formula.str());
}

// void add_statement_execution ();
TEST_F(Btor2EncoderTest, add_statement_execution)
{
  add_dummy_programs(3, 2);

  for (const auto & program : programs)
    program->add(Instruction::Set::create("SYNC", 1));

  reset_encoder(1);

  add_synchronization_constraints();

  encoder->add_statement_execution();

  ASSERT_EQ(vector<string>({"77", "78", "79"}), encoder->nid_exec[1]);
  ASSERT_EQ(vector<string>({"80", "81", "82"}), encoder->nid_exec[2]);
  ASSERT_EQ(vector<string>({"83", "84", "85"}), encoder->nid_exec[3]);
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; statement execution - shorthand for statement & thread activation\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "77 and 1 25 43 exec_1_0\n"
    "78 and 1 27 43 exec_1_1\n"
    "79 and 1 29 66 exec_1_2\n"
    "\n"
    "80 and 1 31 44 exec_2_0\n"
    "81 and 1 33 44 exec_2_1\n"
    "82 and 1 35 66 exec_2_2\n"
    "\n"
    "83 and 1 37 45 exec_3_0\n"
    "84 and 1 39 45 exec_3_1\n"
    "85 and 1 41 66 exec_3_2\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  add_synchronization_constraints();

  verbose = false;
  encoder->add_statement_execution();
  verbose = true;

  ASSERT_EQ(
    "77 and 1 25 43 exec_1_0\n"
    "78 and 1 27 43 exec_1_1\n"
    "79 and 1 29 66 exec_1_2\n"
    "\n"
    "80 and 1 31 44 exec_2_0\n"
    "81 and 1 33 44 exec_2_1\n"
    "82 and 1 35 66 exec_2_2\n"
    "\n"
    "83 and 1 37 45 exec_3_0\n"
    "84 and 1 39 45 exec_3_1\n"
    "85 and 1 41 66 exec_3_2\n\n",
    encoder->formula.str());
}

// void Btor2Encoder::preprocess ();
TEST_F(Btor2EncoderTest, preprocess)
{
  add_dummy_programs(3, 3);

  ASSERT_EQ(
    NIDMap({{0, ""}, {1, ""}, {2, ""}, {3, ""}}),
    encoder->constants);
}
