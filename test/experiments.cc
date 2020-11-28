/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#include <gtest/gtest.h>

#include "common.hh"

namespace ConcuBinE {

struct Experimental : public ::testing::Test
{
};

////////////////////////////////////////////////////////////////////////////////

struct Variable
{
  struct Global
    {
      size_t step;
    };

  struct Local : Global
  {
    word_t thread;
  };

  struct Boolean
    {
      bool val;
    };

  struct Bit_Vector
    {
      word_t val;
    };

  struct Heap
    {
      word_t adr;
      word_t val;
    };

  struct Thread : Local {};
  struct Accu : Local, Bit_Vector {};
  struct SB_Full : Local, Boolean {};

  struct Concept
    {
      virtual size_t step () const = 0;

      virtual word_t thread () const = 0;

      virtual word_t pc () const = 0;
      virtual void pc (word_t val) = 0;

      virtual word_t adr () const = 0;
      virtual void adr (word_t val) = 0;

      virtual word_t val () const = 0;
      virtual void val (word_t val) = 0;
    };

  template <class POD>
  struct Model : Concept
    {
      POD pod;

      Model (const POD & p) : pod(p) {}

      size_t step () const { return pod.step; };

      word_t thread () const
        {
          if constexpr(std::is_base_of<Local, POD>::value)
            return pod.thread;
          else
            assert(false);
        };

      word_t pc () const
        {
          if constexpr(std::is_base_of<Local, POD>::value)
            return pod.pc;
          else
            assert(false);
        };
      void pc (const word_t pc) { pod.pc = pc; };

      word_t adr () const { return pod.adr; };
      void adr (const word_t adr) { pod.adr = adr; };

      word_t val () const { return pod.pc; };
      void val (const word_t val) { pod.val = val; };
    };

  std::unique_ptr<Concept> model;

  template <class POD>
  Variable (const POD & pod) :
    model(std::make_unique<Model<POD>>(pod))
  {}

  size_t step () const { return model->step(); }
};


////////////////////////////////////////////////////////////////////////////////

TEST(Experimental, Variable)
{
  Variable v (Variable::Accu {0, 0, 0});

  std::cout << v.step() << eol;
}

} // namespace ConcuBinE
