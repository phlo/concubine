#include "cvc4.hh"

#include "smtlib.hh"

namespace ConcuBinE {

std::string CVC4::name () const { return "cvc4"; }

std::string CVC4::build_command ()
{
  return "cvc4 -L smt2 -m --output-lang=cvc4";
}

std::string CVC4::build_formula (Encoder & formula,
                                 const std::string & constraints)
{
  return
    Solver::build_formula(formula, constraints) +
    smtlib::check_sat() + eol +
    smtlib::get_model();
}

std::optional<CVC4::Variable> CVC4::parse_line (std::istringstream & line)
{
  // TODO
  (void) line;

  return {};
}

} // namespace ConcuBinE
