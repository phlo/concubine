/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#include "cvc4.hh"

#include "shell.hh"
#include "smtlib.hh"
#include "trace.hh"

namespace ConcuBinE {

//==============================================================================
// CVC4
//==============================================================================

//------------------------------------------------------------------------------
// public member functions inherited from Solver
//------------------------------------------------------------------------------

// CVC4::name ------------------------------------------------------------------

std::string CVC4::name () const { return "cvc4"; }

// CVC4::version ---------------------------------------------------------------

std::string CVC4::version () const
{
  static std::string version;

  if (version.empty())
    {
      auto out = shell::run({name(), "--version"});
      do out.stdout >> version; while (out.stdout && version != "version");
      out.stdout >> version;
    }

  return version;
}

// CVC4::formula ---------------------------------------------------------------

std::string CVC4::formula (Encoder & encoder) const
{
  return
    Solver::formula(encoder) +
    eol + eol +
    smtlib::check_sat() +
    eol +
    smtlib::get_model() +
    eol;
}

//------------------------------------------------------------------------------
// public member functions inherited from External
//------------------------------------------------------------------------------

// CVC4::command ---------------------------------------------------------------

std::vector<std::string> CVC4::command () const
{
  std::vector<std::string> cmd({
    name(),
    "-L", "smt2",
    "-m",
    "--output-lang=cvc4"
  });

  if (verbose)
    cmd.push_back("-v");

  return cmd;
}

//------------------------------------------------------------------------------
// private member functions inherited from External
//------------------------------------------------------------------------------

// CVC4::parse -----------------------------------------------------------------

inline bool parse_bool (std::istringstream & line, std::string & token)
{
  line >> token;
  return token == "TRUE;";
}

inline word_t parse_bv (std::istringstream & line, std::string & token)
{
  line.seekg(static_cast<long>(line.tellg()) + 5) >> token;
  try { return std::stoul(token, nullptr, 2); }
  catch (...) { throw std::runtime_error("illegal value [" + token + "]"); }
}

CVC4::Symbol CVC4::parse (std::istringstream & line)
{
  std::string token;
  line >> token;
  std::istringstream iss(token);
  Symbol sym = symbol(iss);

  if (!std::getline(line, token, '='))
    throw std::runtime_error("missing value");

  switch (sym)
    {
    case Symbol::accu:
    case Symbol::mem:
    case Symbol::sb_adr:
    case Symbol::sb_val:
    case Symbol::exit_code:
      value = parse_bv(line, token);
      return sym;

    case Symbol::sb_full:
      value = parse_bool(line, token);
      return sym;

    case Symbol::heap:
      while (line && token != "WITH")
        line >> token;

      while (line && token.back() != ';')
        {
          // skip "["
          line.seekg(static_cast<long>(line.tellg()) + 1);

          word_t address = parse_bv(line, token);

          // skip " := "
          line >> token;

          value = parse_bv(line, token);

          heap[address] = value;
        }

      return sym;

    case Symbol::stmt:
    case Symbol::exit_flag:
    case Symbol::thread:
    case Symbol::flush:
      if (parse_bool(line, token))
        return sym;
      else
        return Symbol::ignore;

    default: return sym;
    }
}

} // namespace ConcuBinE
