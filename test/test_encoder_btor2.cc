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
        programs.back()->add(
          Instruction::Set::create("SYNC", pc + 1));
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
    "55 not 1 36\n"
    "56 not 1 37\n"
    "57 not 1 38\n"
    "\n"
    "; synchronization condition sync_1\n"
    "58 and 1 24 28\n"
    "59 and 1 32 58 sync_1\n"
    "60 not 1 59\n"
    "\n"
    "; disable threads waiting for barrier 1\n"
    "61 and 1 60 24\n"
    "62 implies 1 61 55\n"
    "63 constraint 62\n"
    "\n"
    "64 and 1 60 28\n"
    "65 implies 1 64 56\n"
    "66 constraint 65\n"
    "\n"
    "67 and 1 60 32\n"
    "68 implies 1 67 57\n"
    "69 constraint 68\n"
    "\n"
    "; synchronization condition sync_2\n"
    "70 and 1 26 30\n"
    "71 and 1 34 70 sync_2\n"
    "72 not 1 71\n"
    "\n"
    "; disable threads waiting for barrier 2\n"
    "73 and 1 72 26\n"
    "74 implies 1 73 55\n"
    "75 constraint 74\n"
    "\n"
    "76 and 1 72 30\n"
    "77 implies 1 76 56\n"
    "78 constraint 77\n"
    "\n"
    "79 and 1 72 34\n"
    "80 implies 1 79 57\n"
    "81 constraint 80\n\n",
    encoder->formula.str());

  /* multiple calls to the same barrier */
  programs.clear();

  // TODO
}

// void Btor2Encoder::preprocess ();
TEST_F(Btor2EncoderTest, preprocess)
{
  add_dummy_programs(3, 3);

  ASSERT_EQ(
    NIDMap({{0, ""}, {1, ""}, {2, ""}, {3, ""}}),
    encoder->constants);
}
