#include "test_encoder.hh"

namespace test::encoder::smtlib {

template <class E, class Impl = E>
struct Encoder : public test::encoder::Encoder<E, Impl>
{
  virtual std::unique_ptr<E> init_encoder (std::unique_ptr<E> e)
    {
      e->step = e->bound;
      e->prev = e->step - 1;

      return e;
    }
};

} // namespace test::encoder::smtlib