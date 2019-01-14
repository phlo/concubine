#include <gtest/gtest.h>

#include <fstream>

#include "encoder.hh"
#include "smtlib.hh"

using namespace std;

struct SMTLibEncoderRelationalTest : public ::testing::Test
{
  string                      expected;
  ProgramList                 programs;
  SMTLibEncoderRelationalPtr  encoder = create_encoder(1, 1);

  SMTLibEncoderRelationalPtr create_encoder (const word bound, const word step)
    {
      SMTLibEncoderRelationalPtr e =
        make_shared<SMTLibEncoderRelational>(
          make_shared<ProgramList>(programs),
          bound,
          false);

      e->step = step;
      e->thread = 1;
      e->pc = 0;

      return e;
    }

  void reset_encoder (const word bound, unsigned long step)
    {
      encoder = create_encoder(bound, step);
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

      reset_encoder(1, 1);
    }
};

// std::string imply (std::string, std::string);
TEST_F(SMTLibEncoderRelationalTest, imply)
{
  ASSERT_EQ("(assert (=> foo bar))\n", encoder->imply("foo", "bar"));
}

// std::string assign_heap (std::string, std::string);
TEST_F(SMTLibEncoderRelationalTest, assign_heap)
{
  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= heap_1 (store heap_0 #x0000 #x0001))))\n",
    encoder->assign_heap(smtlib::word2hex(0), smtlib::word2hex(1)));
}

// std::string assign_accu (std::string);
TEST_F(SMTLibEncoderRelationalTest, assign_accu)
{
  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 #x0000)))\n",
    encoder->assign_accu(smtlib::word2hex(0)));
}

// std::string assign_mem (std::string);
TEST_F(SMTLibEncoderRelationalTest, assign_mem)
{
  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= mem_1_1 #x0000)))\n",
    encoder->assign_mem(smtlib::word2hex(0)));
}

// std::string preserve_heap (void);
TEST_F(SMTLibEncoderRelationalTest, preserve_heap)
{
  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n",
    encoder->preserve_heap());
}

// std::string preserve_accu (void);
TEST_F(SMTLibEncoderRelationalTest, preserve_accu)
{
  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n",
    encoder->preserve_accu());
}

// std::string preserve_mem (void);
TEST_F(SMTLibEncoderRelationalTest, preserve_mem)
{
  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n",
    encoder->preserve_mem());
}

// void add_exit_call (void);
TEST_F(SMTLibEncoderRelationalTest, add_exit_call)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->add(Instruction::Set::create("EXIT", i));
    }

  /* step 1 */
  reset_encoder(10, 1);

  encoder->add_exit_call();

  ASSERT_EQ("", encoder->formula.str());

  /* step 2 */
  reset_encoder(10, 2);

  encoder->add_exit_call();

  expected =
    "; exit call ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; exit variable - exit_<step>\n"
    "(declare-fun exit_2 () Bool)\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* step 3 - reached bound */
  reset_encoder(3, 3);

  encoder->add_exit_call();

  expected =
    "; exit call ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; exit variable - exit_<step>\n"
    "(declare-fun exit_3 () Bool)\n"
    "\n"
    "(assert (=> exit_2 exit_3))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* verbosity */
  reset_encoder(3, 3);

  verbose = false;
  encoder->add_exit_call();
  verbose = true;

  expected =
    "(declare-fun exit_3 () Bool)\n"
    "\n"
    "(assert (=> exit_2 exit_3))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

// virtual void encode (void);
TEST_F(SMTLibEncoderRelationalTest, encode)
{
  /* concurrent increment using SYNC */
  programs.push_back(
    shared_ptr<Program>(
      new Program("data/increment.sync.thread.0.asm")));
  programs.push_back(
    shared_ptr<Program>(
      new Program("data/increment.sync.thread.n.asm")));

  encoder =
    make_shared<SMTLibEncoderRelational>(
      make_shared<ProgramList>(programs), 8);

  ifstream ifs("data/increment.sync.functional.t2.k8.smt2");
  expected.assign(istreambuf_iterator<char>(ifs), istreambuf_iterator<char>());

  ASSERT_EQ("", encoder->formula.str());
}

// virtual std::string encode (Load &);
TEST_F(SMTLibEncoderRelationalTest, LOAD)
{
  Load load = Load(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 (select heap_0 #x0001))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 stmt_2_1_1))\n",
    encoder->encode(load));

  /* indirect */
  load.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (select heap_0 (select heap_0 #x0001)))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 stmt_2_1_1))\n",
    encoder->encode(load));
}

// virtual std::string encode (Store &);
TEST_F(SMTLibEncoderRelationalTest, STORE)
{
  Store store = Store(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 (store heap_0 #x0001 accu_0_1))))\n"
    "(assert (=> exec_1_1_0 stmt_2_1_1))\n",
    encoder->encode(store));

  /* indirect */
  store.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 "
      "(= heap_1 (store heap_0 (select heap_0 #x0001) accu_0_1))))\n"
    "(assert (=> exec_1_1_0 stmt_2_1_1))\n",
    encoder->encode(store));
}

// virtual std::string encode (Add &);
TEST_F(SMTLibEncoderRelationalTest, ADD)
{
  Add add = Add(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (bvadd accu_0_1 (select heap_0 #x0001)))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 stmt_2_1_1))\n",
    encoder->encode(add));

  /* indirect */
  add.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (bvadd accu_0_1 (select heap_0 (select heap_0 #x0001))))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 stmt_2_1_1))\n",
    encoder->encode(add));
}

// virtual std::string encode (Addi &);
TEST_F(SMTLibEncoderRelationalTest, ADDI)
{
  Addi addi = Addi(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (bvadd accu_0_1 #x0001))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 stmt_2_1_1))\n",
    encoder->encode(addi));
}

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
