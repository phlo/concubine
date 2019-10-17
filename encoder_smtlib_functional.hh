#ifndef ENCODER_SMTLIB_FUNCTIONAL_HH_
#define ENCODER_SMTLIB_FUNCTIONAL_HH_

#include "encoder_smtlib.hh"

namespace ConcuBinE::smtlib {

//==============================================================================
// SMT-Lib v2.5 Functional Encoder
//==============================================================================

class Functional : public Encoder
{
public: //======================================================================

  //----------------------------------------------------------------------------
  // public constructors
  //----------------------------------------------------------------------------

  // expose constructors from ConcuBinE::smtlib::Encoder
  //
  using Encoder::Encoder;

  //----------------------------------------------------------------------------
  // public member functions inherited from ConcuBinE::smtlib::Encoder
  //----------------------------------------------------------------------------

  // main encoding function
  //
  virtual void encode ();

private: //=====================================================================

  //----------------------------------------------------------------------------
  // private member functions
  //----------------------------------------------------------------------------

  // state variable definitions
  //
  void define_accu ();
  void define_mem ();
  void define_sb_adr ();
  void define_sb_val ();
  void define_sb_full ();
  void define_stmt ();
  void define_block ();
  void define_halt ();

  void define_heap ();
  void define_exit_flag ();
  void define_exit_code ();

  //----------------------------------------------------------------------------
  // private member functions inherited from ConcuBinE::smtlib::Encoder
  //----------------------------------------------------------------------------

  // state variable definitions
  //
  virtual void define_states ();

  // double-dispatched instruction encoding functions
  //
  using Encoder::encode;
};

} // namespace ConcuBinE::smtlib

#endif
