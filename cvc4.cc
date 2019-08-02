#include "cvc4.hh"

#include "smtlib.hh"

namespace ConcuBinE {

//==============================================================================
// CVC4
//==============================================================================

//------------------------------------------------------------------------------
// member functions
//------------------------------------------------------------------------------

// CVC4::name ------------------------------------------------------------------

std::string CVC4::name () const { return "cvc4"; }

// CVC4::build_command ---------------------------------------------------------

std::string CVC4::build_command ()
{
  return "cvc4 -L smt2 -m --output-lang=cvc4";
}

// CVC4::build_formula ---------------------------------------------------------

std::string CVC4::build_formula (Encoder & formula,
                                 const std::string & constraints)
{
  return
    Solver::build_formula(formula, constraints) +
    smtlib::check_sat() + eol +
    smtlib::get_model();
}

// CVC4::parse_line ------------------------------------------------------------

inline
bool parse_bool (std::istringstream & line, std::string & token)
{
  line >> token;
  return token == "TRUE;";
}

inline
word_t parse_bv (std::istringstream & line, std::string & token)
{
  line.seekg(static_cast<long>(line.tellg()) + 5) >> token;
  try { return std::stoul(token, NULL, 2); }
  catch (...) { throw std::runtime_error("illegal value [" + token + "]"); }
}

CVC4::Symbol CVC4::parse_line (std::istringstream & line)
{
  Symbol symbol = parse_symbol(line);

  std::string token;

  if (!std::getline(line, token, '='))
    throw std::runtime_error("missing value");

  switch (symbol)
    {
    case Symbol::accu:
    case Symbol::mem:
    case Symbol::sb_adr:
    case Symbol::sb_val:
    case Symbol::exit_code:
      value = parse_bv(line, token);
      return symbol;

    case Symbol::sb_full:
      value = parse_bool(line, token);
      return symbol;

    case Symbol::heap:
      while (line && token != "WITH")
        line >> token;

      while (line && token.back() != ';')
        {
          // skip "["
          line.seekg(static_cast<long>(line.tellg()) + 1);

          word_t address = parse_bv(line, token);

          // skip " := 0bin"
          line.seekg(static_cast<long>(line.tellg()) + 8);

          value = parse_bv(line, token);

          heap[address] = value;
        }

      return symbol;

    case Symbol::stmt:
    case Symbol::exit_flag:
    case Symbol::thread:
    case Symbol::flush:
      if (parse_bool(line, token))
        return symbol;
      else
        return Symbol::ignore;

    default: return symbol;
    }
}

} // namespace ConcuBinE
