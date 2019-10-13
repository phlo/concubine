#include "btormc.hh"

#include "encoder.hh"

namespace ConcuBinE {

//==============================================================================
// BtorMC
//==============================================================================

// BtorMC::name ----------------------------------------------------------------

std::string BtorMC::name () const { return "btormc"; }

// BtorMC::command -------------------------------------------------------------

const std::vector<std::string> & BtorMC::command () const
{
  static std::vector<std::string> cmd({
    name(),
    "--trace-gen-full",
    "-kmax",
    ""});

  // TODO: improve
  cmd.back() = std::to_string(bound);

  return cmd;
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

// BtorMC::symbol --------------------------------------------------------------

inline
bool starts_with (const std::string & str, const std::string & prefix)
{
  return str.find(prefix) != std::string::npos;
}

BtorMC::Symbol BtorMC::symbol (std::istringstream & line)
{
  line >> std::ws;

  std::ostringstream os;
  for (char c = line.get();
       c != '@' && c != '#' && c != '_' && c != EOF;
       c = line.get())
    os << c;

  std::string name = os.str();

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

// BtorMC::sat -----------------------------------------------------------------

bool BtorMC::sat (const std::string & formula, const size_t b)
{
  bound = b;
  return Boolector::sat(formula);
}

// BtorMC::solve ---------------------------------------------------------------

std::unique_ptr<Trace> BtorMC::solve (Encoder & encoder)
{
  bound = encoder.bound;
  return Boolector::solve(encoder);
}

} // namespace ConcuBinE
