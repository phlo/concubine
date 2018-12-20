#include <gtest/gtest.h>

#include "encoder.hh"

using namespace std;

struct SMTLibEncoderFunctionalTest : public ::testing::Test
{
  const char *                expected;
  ProgramList                 programs;
  SMTLibEncoderFunctionalPtr  encoder = create_encoder(1, 1);

  SMTLibEncoderFunctionalPtr create_encoder (const word bound, const word step)
    {
      SMTLibEncoderFunctionalPtr e =
        make_shared<SMTLibEncoderFunctional>(
          make_shared<ProgramList>(programs),
          bound);

      e->step = step;

      return e;
    }

  void reset_encoder (const word bound, unsigned long step)
    {
      encoder = create_encoder(bound, step);
    }

  /*
  void add_dummy_programs (unsigned num, unsigned size)
    {
      InstructionPtr op = Instruction::Set::create("ADDI", 1);
      for (size_t i = 0; i < num; i++)
        {
          programs.push_back(shared_ptr<Program>(new Program()));
          for (size_t j = 0; j < size; j++)
            programs[i]->add(op);
        }

      encoder = create_encoder(1);
    }
  */
};

// void add_statement_activation (void);

// void add_thread_scheduling (void);

// void add_exit_call (void);

// void add_state_update (void);

// virtual void preprocess (void);

// virtual void encode (void);

// virtual std::string encode (Load &);
TEST_F(SMTLibEncoderFunctionalTest, LOAD)
{
  Load load = Load(1);

  ASSERT_STREQ(
    "(select heap_0 #x0001)",
    encoder->encode(load).c_str());

  /* indirect */
  load.indirect = true;

  ASSERT_STREQ(
    "(select heap_0 (select heap_0 #x0001))",
    encoder->encode(load).c_str());
}

// virtual std::string encode (Store &);
TEST_F(SMTLibEncoderFunctionalTest, STORE)
{
  Store store = Store(1);

  ASSERT_STREQ(
    "(store heap_0 #x0001 accu_0_1)",
    encoder->encode(store).c_str());

  /* indirect */
  store.indirect = true;

  ASSERT_STREQ(
    "(store heap_0 (select heap_0 #x0001) accu_0_1)",
    encoder->encode(store).c_str());
}

// virtual std::string encode (Add &);
TEST_F(SMTLibEncoderFunctionalTest, ADD)
{
  Add add = Add(1);

  ASSERT_STREQ(
    "(bvadd accu_0_1 (select heap_0 #x0001))",
    encoder->encode(add).c_str());

  /* indirect */
  add.indirect = true;

  ASSERT_STREQ(
    "(bvadd accu_0_1 (select heap_0 (select heap_0 #x0001)))",
    encoder->encode(add).c_str());
}

// virtual std::string encode (Addi &);
TEST_F(SMTLibEncoderFunctionalTest, ADDI)
{
  Addi addi = Addi(1);

  ASSERT_STREQ(
    "(bvadd accu_0_1 #x0001)",
    encoder->encode(addi).c_str());
}

// virtual std::string encode (Sub &);
TEST_F(SMTLibEncoderFunctionalTest, SUB)
{
  Sub sub = Sub(1);

  ASSERT_STREQ(
    "(bvsub accu_0_1 (select heap_0 #x0001))",
    encoder->encode(sub).c_str());

  /* indirect */
  sub.indirect = true;

  ASSERT_STREQ(
    "(bvsub accu_0_1 (select heap_0 (select heap_0 #x0001)))",
    encoder->encode(sub).c_str());
}

// virtual std::string encode (Subi &);
TEST_F(SMTLibEncoderFunctionalTest, SUBI)
{
  Subi subi = Subi(1);

  ASSERT_STREQ(
    "(bvsub accu_0_1 #x0001)",
    encoder->encode(subi).c_str());
}

// virtual std::string encode (Cmp &);
TEST_F(SMTLibEncoderFunctionalTest, CMP)
{
  Cmp cmp = Cmp(1);

  ASSERT_STREQ(
    "(bvsub accu_0_1 (select heap_0 #x0001))",
    encoder->encode(cmp).c_str());

  /* indirect */
  cmp.indirect = true;

  ASSERT_STREQ(
    "(bvsub accu_0_1 (select heap_0 (select heap_0 #x0001)))",
    encoder->encode(cmp).c_str());
}

// virtual std::string encode (Jmp &);
TEST_F(SMTLibEncoderFunctionalTest, JMP)
{
  Jmp jmp = Jmp(1);

  ASSERT_TRUE(encoder->encode(jmp).empty());
}

// virtual std::string encode (Jz &);
TEST_F(SMTLibEncoderFunctionalTest, JZ)
{
  Jz jz = Jz(1);

  ASSERT_STREQ(
    "(= accu_0_1 #x0000)",
    encoder->encode(jz).c_str());
}

// virtual std::string encode (Jnz &);
TEST_F(SMTLibEncoderFunctionalTest, JNZ)
{
  Jnz jnz = Jnz(1);

  ASSERT_STREQ(
    "(not (= accu_0_1 #x0000))",
    encoder->encode(jnz).c_str());
}

// virtual std::string encode (Js &);
TEST_F(SMTLibEncoderFunctionalTest, JS)
{
  Js js = Js(1);

  ASSERT_EQ(
    "(= #b1 ((_ extract " +
      to_string(word_size - 1) +
      " " +
      to_string(word_size - 1) +
      ") " +
      "accu_0_1))",
    encoder->encode(js));
}

// virtual std::string encode (Jns &);
TEST_F(SMTLibEncoderFunctionalTest, JNS)
{
  Jns jns = Jns(1);

  ASSERT_EQ(
    "(= #b0 ((_ extract " +
      to_string(word_size - 1) +
      " " +
      to_string(word_size - 1) +
      ") " +
      "accu_0_1))",
    encoder->encode(jns));
}

// virtual std::string encode (Jnzns &);
TEST_F(SMTLibEncoderFunctionalTest, JNZNS)
{
  Jnzns jnzns = Jnzns(1);

  ASSERT_EQ(
    "(and (not (= accu_0_1 #x0000)) (= #b0 ((_ extract " +
      to_string(word_size - 1) +
      " " +
      to_string(word_size - 1) +
      ") accu_0_1)))",
    encoder->encode(jnzns));
}

// virtual std::string encode (Mem &);
TEST_F(SMTLibEncoderFunctionalTest, MEM)
{
  Mem mem = Mem(1);

  ASSERT_STREQ(
    "(select heap_0 #x0001)",
    encoder->encode(mem).c_str());

  /* indirect */
  mem.indirect = true;

  ASSERT_STREQ(
    "(select heap_0 (select heap_0 #x0001))",
    encoder->encode(mem).c_str());
}

// virtual std::string encode (Cas &);
TEST_F(SMTLibEncoderFunctionalTest, CAS)
{
  Cas cas = Cas(1);

  ASSERT_STREQ(
    "(ite "
      "(= mem_0_1 (select heap_0 #x0001)) "
      "(store heap_0 #x0001 accu_0_1) "
      "heap_0)",
    encoder->encode(cas).c_str());

  /* indirect */
  cas.indirect = true;

  ASSERT_STREQ(
    "(ite "
      "(= mem_0_1 (select heap_0 (select heap_0 #x0001))) "
      "(store heap_0 (select heap_0 #x0001) accu_0_1) "
      "heap_0)",
    encoder->encode(cas).c_str());
}

// virtual std::string encode (Sync &);
TEST_F(SMTLibEncoderFunctionalTest, SYNC)
{
  Sync sync = Sync(1);

  ASSERT_TRUE(encoder->encode(sync).empty());
}

// virtual std::string encode (Exit &);
TEST_F(SMTLibEncoderFunctionalTest, EXIT)
{
  Exit exit = Exit(1);

  ASSERT_STREQ(
    "(assert (= exit_code #x0001))",
    encoder->encode(exit).c_str());
}

/*******************************************************************************
 * DEPRECATED
*******************************************************************************/
#ifdef __NIGNORE__
TEST_F(EncoderTest, test)
{
  const char * program1 = "../wiki/encoding/concurrent-increment.sync.thread1.asm";
  const char * program2 = "../wiki/encoding/concurrent-increment.sync.thread2.asm";

  programs.push_back(make_shared<Program>(program1));
  programs.push_back(make_shared<Program>(program2));

  encoder = make_shared<SMTLibEncoderFunctional>(make_shared<ProgramList>(programs), 3);

  encoder->encode();

  string formula = encoder->to_string();

  ASSERT_STREQ("", formula.c_str());
}
#endif
