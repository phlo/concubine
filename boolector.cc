#include "boolector.hh"

#include "parser.hh"

namespace ConcuBinE {

//==============================================================================
// Boolector
//==============================================================================

//------------------------------------------------------------------------------
// member functions
//------------------------------------------------------------------------------

// Boolector::command ----------------------------------------------------------

std::string Boolector::command ()
{
  return "boolector --model-gen"; // --output-number-format=dec
}

// Boolector::parse ------------------------------------------------------------

Boolector::Symbol Boolector::parse (std::istringstream & line)
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
      word_t address;

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

      heap[address] = value;
    }

  // parse symbol
  Symbol sym = symbol(line);

  switch (sym)
    {
    case Symbol::stmt:
    case Symbol::exit_flag:
    case Symbol::thread:
    case Symbol::flush:
      if (value)
        return sym;
      break;

    default: return sym;
    }

  return Symbol::ignore;
}

// Boolector::name -------------------------------------------------------------

std::string Boolector::name () const { return "boolector"; }

} // namespace ConcuBinE
