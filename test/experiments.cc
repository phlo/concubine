#include <gtest/gtest.h>

#include <bitset>
#include <functional>
#include <memory>

#include "instruction.hh"
#include "program.hh"

namespace ConcuBinE {

struct Experimental : public ::testing::Test
{
};

////////////////////////////////////////////////////////////////////////////////

TEST(Hashing, hash)
{
  std::hash<unsigned long> hash_fn;

  unsigned long id = 0;

  ASSERT_EQ(0, hash_fn(id));
}

////////////////////////////////////////////////////////////////////////////////

#ifdef NIGNORE
struct Thread;
struct Encoder;

// type erasure
struct Instruction
{
  struct Concept
  {
    virtual uint8_t type () const = 0;

    virtual const std::string & symbol () const = 0;
    virtual void execute (Thread & t) const = 0;
    virtual std::string encode (Encoder & e) const = 0;

    virtual bool is_nullary () const = 0;
    virtual bool is_unary () const = 0;
  };

  template <class T>
  struct Model : Concept
  {
    T op;

    Model (const T & o) : op(o) {}
    Model (T && o) : op(move(o)) {}

    virtual uint8_t type () const;

    virtual const std::string & symbol () const;
    virtual void execute (Thread & t) const;
    virtual std::string encode (Encoder & e) const;

    virtual bool is_nullary () const;
    virtual bool is_unary () const;
  };

  struct Factory
    {
      static unique_ptr<unordered_map<std::string, unique_ptr<Instruction> (*) ()>> nullary;
      static unique_ptr<unordered_map<std::string, unique_ptr<Instruction> (*) (int)>> unary;

      template <class T>
      static const std::string & add_nullary (const std::string && symbol)
        {
          if (!nullary)
            nullary = make_unique<unordered_map<std::string, unique_ptr<Instruction> (*) ()>>();

          return nullary->emplace(symbol, [] () { return make_unique<Instruction>(T {}); }).first->first;
        }

      template <class T>
      static const std::string & add_unary (const std::string && symbol)
        {
          if (!unary)
            unary = make_unique<unordered_map<std::string, unique_ptr<Instruction> (*) (int)>>();

          // return nullary->emplace(symbol, [] (int arg) { T t {{{0}, arg}}; return make_unique<Instruction>(t); }).first->first;
          return symbol;
        }

      static unique_ptr<Instruction> create (std::string symbol) { return (*nullary)[symbol](); }
      static unique_ptr<Instruction> create (std::string symbol, int arg) { return (*unary)[symbol](arg); };
    };

  shared_ptr<Concept> op;

  template <class T>
  Instruction(const T & t) : op(make_shared<Model<T>>(t)) {}

  uint8_t type () const { return op->type(); }

  const std::string & symbol () const { return op->symbol(); }
  void execute (Thread & t) const { op->execute(t); }
  std::string encode (Encoder & e) const { return op->encode(e); }

  bool is_nullary () const { return op->is_nullary(); }
  bool is_unary () const { return op->is_unary(); }
};

// abstract
struct Nullary
{
  uint8_t type;
};

struct Unary : public Nullary
{
  const int arg;
};

// concrete
struct Fence : public Nullary
{
  // inline static const std::string symbol = "FENCE";
  inline static const std::string & symbol = Instruction::Factory::add_nullary<Fence>("FENCE");
};

struct Add : public Unary
{
  inline const static std::string symbol = "ADD";
  // inline static const std::string & symbol = Instruction::Factory::add_unary<Add>("ADD");
};

struct Store : public Unary
{
  inline const static std::string symbol = "STORE";
  // inline static const std::string & symbol = Instruction::Factory::add_unary<Store>("STORE");
};

struct Exit : public Unary
{
  inline const static std::string symbol = "EXIT";
  // inline static const std::string & symbol = Instruction::Factory::add_unary<Exit>("EXIT");
};

// implementation
struct Thread
{
  void execute (const Instruction & i) { std::cout << "executing "; i.execute(*this); }

  void execute (const Fence & f) { std::cout << f.symbol << eol; }
  void execute (const Add & a) { std::cout << a.symbol << eol; }
  void execute (const Store & s) { std::cout << s.symbol << eol; }
  void execute (const Exit & e) { std::cout << e.symbol << eol; }
};

struct Encoder
{
  std::string encode (const Instruction & i) { return "encoding " + i.encode(*this); }

  std::string encode (const Fence & f) { return f.symbol; }
  std::string encode (const Add & a) { return a.symbol; }
  std::string encode (const Store & s) { return s.symbol; }
  std::string encode (const Exit & e) { return e.symbol; }
};

template <class T>
uint8_t Instruction::Model<T>::type () const { return op.type; }

template <class T>
const std::string & Instruction::Model<T>::symbol () const { return op.symbol; }

template <class T>
void Instruction::Model<T>::execute (Thread & t) const { t.execute(op); }

template <class T>
std::string Instruction::Model<T>::encode (Encoder & e) const { return e.encode(op); }

template <class T>
bool Instruction::Model<T>::is_nullary () const { return is_base_of<Nullary, T>(); }

template <class T>
bool Instruction::Model<T>::is_unary () const { return is_base_of<Unary, T>(); }

unique_ptr<unordered_map<std::string, unique_ptr<Instruction> (*) ()>> Instruction::Factory::nullary;
unique_ptr<unordered_map<std::string, unique_ptr<Instruction> (*) (int)>> Instruction::Factory::unary;

TEST(Experimental, type_erasure)
{
  Nullary n {0}; (void) n;
  Unary u {{0}, 1}; (void) u;

  vector<Instruction> program {
    Instruction {Fence {{0}}},
    Instruction {Add {{{1}, 1}}},
    Instruction {Store {{{2}, 2}}},
    Instruction {Exit {{{3}, 3}}}
  };

  Thread t;
  Encoder e;

  for (const Instruction & op : program)
    {
      std::cout
        << op.symbol()
        << (op.is_unary() ? " is unary " : " is nullary ")
        << "and has type " << to_string(op.type())
        << eol
        << "  -> ";

      // op.execute(t);
      t.execute(op);

      // std::cout << "  -> " << op.encode(e) << eol;
      std::cout << "  -> " << e.encode(op) << eol;
    }

  std::cout << eol << "########################################" << eol << eol;

  for (const auto & it : *Instruction::Factory::nullary)
    {
      const unique_ptr<Instruction> op = Instruction::Factory::create(it.first);

      std::cout << "found " << op->symbol() << eol;
    }

  int arg = 0;
  for (const auto & it : *Instruction::Factory::unary)
    {
      const unique_ptr<Instruction> op = Instruction::Factory::create(it.first, arg++);

      std::cout << "found " << op->symbol() << eol;
    }
}
#endif

struct Simulator
{
  void execute (const Instruction & i) { std::cout << "executing "; i.execute(*this); }

  void execute (const Instruction::Load & l) { std::cout << l.symbol << eol; }
  // void execute (const Fence & f) { std::cout << f.symbol << eol; }
  // void execute (const Add & a) { std::cout << a.symbol << eol; }
  // void execute (const Store & s) { std::cout << s.symbol << eol; }
  // void execute (const Exit & e) { std::cout << e.symbol << eol; }
};

struct Encoder
{
  std::string encode (const Instruction & i) { return "encoding " + i.encode(*this); }

  std::string encode (const Instruction::Load & l) { return l.symbol; }
  // std::string encode (const Fence & f) { return f.symbol; }
  // std::string encode (const Add & a) { return a.symbol; }
  // std::string encode (const Store & s) { return s.symbol; }
  // std::string encode (const Exit & e) { return e.symbol; }
};

TEST(Experimental, Instruction)
{
  Instruction::Nullary n {0}; (void) n;

  Instruction::Unary u {0, 1}; (void) u;

  std::vector<Instruction> program {
    Instruction::Load {0}
  };

  // Thread t;
  // Encoder e;

  for (const Instruction & op : program)
    {
      std::cout
        << op.symbol()
        << (op.is_unary() ? " is unary " : " is nullary ")
        << "and has type " << std::bitset<8>(op.type())
        << eol;
        // << "  -> ";
//
      // // op.execute(t);
      // t.execute(op);
//
      // // std::cout << "  -> " << op.encode(e) << eol;
      // std::cout << "  -> " << e.encode(op) << eol;
    }

  std::cout << eol << "########################################" << eol << eol;

  std::cout << "nullary instructions: " << eol;
  for (const auto & it : *Instruction::nullary_factory)
    {
      const Instruction op = Instruction::create(it.first);

      std::cout << "  " << op.symbol() << eol;
    }
  std::cout << eol;

  std::cout << "unary instructions: " << eol;
  for (const auto & it : *Instruction::unary_factory)
    {
      const Instruction op = Instruction::create(it.first, 0);

      std::cout << "  " << op.symbol() << eol;
    }
  std::cout << eol;

  std::cout << "memory instructions: " << eol;
  for (const auto & it : *Instruction::memory_factory)
    {
      const Instruction op = Instruction::create(it.first, 0, false);

      std::cout << "  " << op.symbol() << eol;
    }

  std::cout << eol << "########################################" << eol << eol;

  // Instruction op1 {Instruction::Load {1, true}};
  Instruction op1 {Instruction::create("LOAD", 1, true)};
  Instruction::Concept * base = op1.model.get();

  Instruction op2 {op1};
  ASSERT_TRUE(op1.model);
  ASSERT_TRUE(op2.model);
  ASSERT_NE(op1.model.get(), op2.model.get());
  std::cout << "copy constructed" << eol;

  Instruction op3 {std::move(op1)};
  ASSERT_FALSE(op1.model);
  ASSERT_TRUE(op2.model);
  ASSERT_TRUE(op3.model);
  ASSERT_EQ(base, op3.model.get());
  ASSERT_NE(op2.model.get(), op3.model.get());
  std::cout << "move constructed" << eol;

  op1 = op2;
  ASSERT_TRUE(op1.model);
  ASSERT_TRUE(op2.model);
  ASSERT_TRUE(op3.model);
  ASSERT_NE(op1.model.get(), op2.model.get());
  ASSERT_NE(op1.model.get(), op3.model.get());
  std::cout << "copy assigned" << eol;

  op2 = std::move(op3);
  ASSERT_TRUE(op1.model);
  ASSERT_TRUE(op2.model);
  ASSERT_FALSE(op3.model);
  ASSERT_NE(op1.model.get(), op2.model.get());
  ASSERT_EQ(base, op2.model.get());
  std::cout << "move assigned" << eol;

  std::cout << eol << "########################################" << eol << eol;

  Instruction fence = Instruction::Fence {};

  ASSERT_EQ(&Instruction::Fence::symbol, &fence.symbol());

  // std::cout << "trying to get arg of a nullary instruction... " << fence.arg() << eol;

  // const Instruction::Unary & ref = fence;

  // (void) ref;
}

TEST(Experimental, Program)
{
  std::string path = "dummy.asm";
  std::istringstream code {
    "start: LOAD 1\n"
    "JMP start\n"
  };

  Program p1 (code, path);
  ASSERT_FALSE(p1.empty());
  ASSERT_FALSE(p1.labels.empty());

  Program p2 (p1);
  ASSERT_NE(&p1[0], &p2[0]);
  ASSERT_EQ(p1, p2);
  std::cout << "copy constructed" << eol;

  const Instruction * ptr = &p1[0];

  Program p3 (std::move(p1));
  ASSERT_TRUE(p1.empty());
  ASSERT_TRUE(p1.path.empty());
  ASSERT_TRUE(p1.predecessors.empty());
  ASSERT_TRUE(p1.checkpoints.empty());
  ASSERT_TRUE(p1.pc_to_label.empty());
  ASSERT_TRUE(p1.label_to_pc.empty());
  ASSERT_TRUE(p1.labels.empty());
  ASSERT_EQ(p2, p3);
  ASSERT_EQ(ptr, &p3[0]);
  std::cout << "move constructed" << eol;

  p1 = p2;
  ASSERT_EQ(p1, p3);
  ASSERT_NE(&p1[0], &p2[0]);
  ASSERT_NE(&p1[0], &p3[0]);
  std::cout << "copy assigned" << eol;

  p2 = move(p3);
  ASSERT_TRUE(p3.empty());
  ASSERT_TRUE(p3.path.empty());
  ASSERT_TRUE(p3.predecessors.empty());
  ASSERT_TRUE(p3.checkpoints.empty());
  ASSERT_TRUE(p3.pc_to_label.empty());
  ASSERT_TRUE(p3.label_to_pc.empty());
  ASSERT_TRUE(p3.labels.empty());
  ASSERT_EQ(p1, p2);
  ASSERT_EQ(ptr, &p2[0]);
  std::cout << "move assigned" << eol;

  Program::List p {p1, p2};
  std::unique_ptr<Program::List> p_ptr = std::make_unique<Program::List>(std::move(p));
  ASSERT_TRUE(p.empty());
  p = std::move(*p_ptr);
  ASSERT_FALSE(p.empty());
}

} // namespace ConcuBinE
