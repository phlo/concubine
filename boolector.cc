#include "boolector.hh"

#include <iomanip>

#include "parser.hh"

namespace ConcuBinE {

//==============================================================================
// Boolector
//==============================================================================

//------------------------------------------------------------------------------
// member functions
//------------------------------------------------------------------------------

// Boolector::build_command ----------------------------------------------------

std::string Boolector::build_command ()
{
  return "boolector --model-gen"; // --output-number-format=dec
}

// Boolector::parse_line -------------------------------------------------------

Boolector::Symbol Boolector::parse_line (std::istringstream & line)
{
  std::string token;

  // parse node id
  uint64_t nid;

  if (!(line >> nid))
    {
      line >> token;
      throw std::runtime_error("parsing node id failed [" + token + ']');
    }

  // parse value
  if (!(line >> token))
    throw std::runtime_error("missing value");

  try { value = stoul(token, nullptr, 2); }
  catch (const std::logic_error &)
    {
      // array element index
      try
        {
          token = token.substr(1, token.size() - 2);
          address = stoul(token, nullptr, 2);
        }
      catch (const std::logic_error &)
        {
          throw std::runtime_error("illegal array index [" + token + "]");
        }

      // array element value
      if (!(line >> token))
        throw std::runtime_error("missing array value");

      try { value = stoul(token, nullptr, 2); }
      catch (const std::logic_error &)
        {
          throw std::runtime_error("illegal array value [" + token + "]");
        }
    }

  // parse symbol
  Symbol symbol = parse_symbol(line);

  switch (symbol)
    {
    case Symbol::stmt:
    case Symbol::exit_flag:
    case Symbol::thread:
    case Symbol::flush:
      if (value)
        return symbol;
      break;

    default: return symbol;
    }

  return Symbol::ignore;
}

// Boolector::name -------------------------------------------------------------

std::string Boolector::name () const { return "boolector"; }

} // namespace ConcuBinE
