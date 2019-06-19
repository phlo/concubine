#include "test_encoder.hh"

namespace Test
{
template <class E, class Impl = E>
struct SMTLib_Encoder : public Test::Encoder<E, Impl>
{
  virtual std::unique_ptr<E> init_encoder (std::unique_ptr<E> e)
    {
      e->step = e->bound;
      e->prev = e->step - 1;

      return e;
    }
};
}
