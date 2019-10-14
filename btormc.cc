#include "btormc.hh"

#include "encoder.hh"
#include "trace.hh"

namespace ConcuBinE {

//==============================================================================
// BtorMC
//==============================================================================

//------------------------------------------------------------------------------
// public member functions inherited from Solver
//------------------------------------------------------------------------------

// BtorMC::name ----------------------------------------------------------------

std::string BtorMC::name () const { return "btormc"; }

// BtorMC::sat -----------------------------------------------------------------

bool BtorMC::sat (const std::string & formula, const size_t k)
{
  kmax = std::to_string(k);
  return Boolector::sat(formula);
}

// BtorMC::solve ---------------------------------------------------------------

std::unique_ptr<Trace> BtorMC::solve (Encoder & encoder)
{
  kmax = std::to_string(encoder.bound);
  return Boolector::solve(encoder);
}

//------------------------------------------------------------------------------
// public member functions inherited from External
//------------------------------------------------------------------------------

// BtorMC::command -------------------------------------------------------------

const std::vector<std::string> & BtorMC::command () const
{
  static std::vector<std::string> cmd({
    name(),
    "--trace-gen-full",
    "-kmax",
    kmax});

  if (cmd.back() != kmax)
    cmd.back() = kmax;

  return cmd;
}

//------------------------------------------------------------------------------
// private member functions inherited from External
//------------------------------------------------------------------------------

// BtorMC::symbol --------------------------------------------------------------

inline
bool starts_with (const std::string & str, const std::string & prefix)
{
  return str.find(prefix) != std::string::npos;
}

BtorMC::Symbol BtorMC::symbol (std::istringstream & line)
{
  line >> std::ws;

  std::ostringstream oss;

  for (char c = line.get();
       c != '@' && c != '#' && c != '_' && c != EOF;
       c = line.get())
    oss << c;

  std::string name = oss.str();

  if (name.empty())
    throw std::runtime_error("missing symbol");

  line.unget();

  if (name == Encoder::accu_sym)
    {
      thread = attribute(line, "thread");
      step = attribute(line, "step", '#');
      return Symbol::accu;
    }
  else if (name == Encoder::mem_sym)
    {
      thread = attribute(line, "thread");
      step = attribute(line, "step", '#');
      return Symbol::mem;
    }
  else if (name == Encoder::sb_adr_sym)
    {
      thread = attribute(line, "thread");
      step = attribute(line, "step", '#');
      return Symbol::sb_adr;
    }
  else if (name == Encoder::sb_val_sym)
    {
      thread = attribute(line, "thread");
      step = attribute(line, "step", '#');
      return Symbol::sb_val;
    }
  else if (name == Encoder::sb_full_sym)
    {
      thread = attribute(line, "thread");
      step = attribute(line, "step", '#');
      return Symbol::sb_full;
    }
  else if (name == Encoder::stmt_sym)
    {
      thread = attribute(line, "thread");
      pc = attribute(line, "pc");
      step = attribute(line, "step", '#');
      return Symbol::stmt;
    }
  else if (name == Encoder::heap_sym)
    {
      step = attribute(line, "step", '@');
      return Symbol::heap;
    }
  else if (name == Encoder::exit_flag_sym)
    {
      step = attribute(line, "step", '#');
      return Symbol::exit_flag;
    }
  else if (name == Encoder::exit_code_sym)
    {
      step = attribute(line, "step", '#');
      return Symbol::exit_code;
    }
  else if (name == Encoder::thread_sym)
    {
      thread = attribute(line, "thread");
      step = attribute(line, "step", '@');
      return Symbol::thread;
    }
  else if (name == Encoder::flush_sym)
    {
      thread = attribute(line, "thread");
      step = attribute(line, "step", '@');
      return Symbol::flush;
    }

  return Symbol::ignore;
}

// BtorMC::parse ---------------------------------------------------------------

BtorMC::Symbol BtorMC::parse (std::istringstream & line)
{
  switch (line.peek())
    {
    case 'b':
    case 'j':
    case '#':
    case '@':
    case '.':
      return {};
    default:
      return Boolector::parse(line);
    }
}

} // namespace ConcuBinE
