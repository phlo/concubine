/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#include "boolector.hh"

#include "shell.hh"
#include "smtlib.hh"
#include "trace.hh"

namespace ConcuBinE {

//==============================================================================
// Boolector
//==============================================================================

//------------------------------------------------------------------------------
// public member functions inherited from Solver
//------------------------------------------------------------------------------

// Boolector::name -------------------------------------------------------------

std::string Boolector::name () const { return "boolector"; }

// Boolector::version ----------------------------------------------------------

std::string Boolector::version () const
{
  static std::string version;

  if (version.empty())
    shell::run({name(), "--version"}).stdout >> version;

  return version;
}

// Boolector::formula ----------------------------------------------------------

std::string Boolector::formula (Encoder & encoder) const
{
  return Solver::formula(encoder) + eol + eol + smtlib::check_sat() + eol;
}

//------------------------------------------------------------------------------
// public member functions inherited from External
//------------------------------------------------------------------------------

// Boolector::command ----------------------------------------------------------

std::vector<std::string> Boolector::command () const
{
  std::vector<std::string> cmd({
    name(),
    "--model-gen",
    "--output-format=btor"
  });

  if (verbose)
    cmd.push_back("-v");

  return cmd;
}

//------------------------------------------------------------------------------
// protected member functions inherited from External
//------------------------------------------------------------------------------

// Boolector::parse ------------------------------------------------------------

Boolector::Symbol Boolector::parse (std::istringstream & line)
{
  // skip statistics
  if (line.peek() == '[')
    return Symbol::ignore;

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

} // namespace ConcuBinE
