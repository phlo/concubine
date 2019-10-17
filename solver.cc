#include "solver.hh"

#include "encoder.hh"
#include "parser.hh"
#include "runtime.hh"
#include "shell.hh"
#include "trace.hh"

namespace ConcuBinE {

//==============================================================================
// Solver
//==============================================================================

// Solver::formula -------------------------------------------------------------

std::string Solver::formula (Encoder & encoder) const
{
  return encoder.formula.str();
}

//==============================================================================
// External
//==============================================================================

//------------------------------------------------------------------------------
// public member functions inherited from Solver
//------------------------------------------------------------------------------

// External::sat ---------------------------------------------------------------

bool External::sat (const std::string & input)
{
  const auto & cmd = command();

  time = runtime::measure([this, &input, &cmd] {
    stdout = std::move(shell::run(cmd, input).stdout);
  });

  std::string sat;
  return (stdout >> sat) && sat == "sat";
}

// External::solve -------------------------------------------------------------

std::unique_ptr<Trace> External::solve (Encoder & encoder)
{
  sat(formula(encoder));
  return trace(encoder);
}

//------------------------------------------------------------------------------
// protected member functions
//------------------------------------------------------------------------------

// External::attribute ---------------------------------------------------------

size_t External::attribute (std::istringstream & line,
                            const std::string & name,
                            const char delimiter)
{
  if (line.peek() != delimiter)
    {
      std::string token;
      line >> token;
      throw std::runtime_error("missing delimiter [" + token + "]");
    }

  line.get(); // discard delimiter

  size_t val;

  if (!(line >> val))
    throw std::runtime_error("missing " + name);

  return val;
}

// External::symbol ------------------------------------------------------------

External::Symbol External::symbol (std::istringstream & line)
{
  std::string name;

  if (!getline(line >> std::ws, name, '_'))
    throw std::runtime_error("missing symbol");

  line.unget(); // restore initial delimiter

  if (name == Encoder::accu_sym)
    {
      step = attribute(line, "step");
      thread = attribute(line, "thread");
      return Symbol::accu;
    }
  else if (name == Encoder::mem_sym)
    {
      step = attribute(line, "step");
      thread = attribute(line, "thread");
      return Symbol::mem;
    }
  else if (name == Encoder::sb_adr_sym)
    {
      step = attribute(line, "step");
      thread = attribute(line, "thread");
      return Symbol::sb_adr;
    }
  else if (name == Encoder::sb_val_sym)
    {
      step = attribute(line, "step");
      thread = attribute(line, "thread");
      return Symbol::sb_val;
    }
  else if (name == Encoder::sb_full_sym)
    {
      step = attribute(line, "step");
      thread = attribute(line, "thread");
      return Symbol::sb_full;
    }
  else if (name == Encoder::stmt_sym)
    {
      step = attribute(line, "step");
      thread = attribute(line, "thread");
      pc = attribute(line, "pc");
      return Symbol::stmt;
    }
  else if (name == Encoder::heap_sym)
    {
      step = attribute(line, "step");
      return Symbol::heap;
    }
  else if (name == Encoder::exit_flag_sym)
    {
      step = attribute(line, "step");
      return Symbol::exit_flag;
    }
  else if (name == Encoder::exit_code_sym)
    {
      return Symbol::exit_code;
    }
  else if (name == Encoder::thread_sym)
    {
      step = attribute(line, "step");
      thread = attribute(line, "thread");
      return Symbol::thread;
    }
  else if (name == Encoder::flush_sym)
    {
      step = attribute(line, "step");
      thread = attribute(line, "thread");
      return Symbol::flush;
    }

  return Symbol::ignore;
}

//------------------------------------------------------------------------------
// private member functions
//------------------------------------------------------------------------------

// External::update_heap -------------------------------------------------------

void External::update_heap (Trace & trace, const size_t prev, const size_t cur)
{
  const word_t t = trace.thread(prev);
  const Instruction & op = (*trace.programs)[t][trace.pc(prev, t)];

  // store buffer has been flushed
  // NOTE: heap update visible one step after flush is set
  if (trace.flush(prev))
    {
      const word_t adr = trace.sb_adr(t);
      trace.push_back_heap(cur, adr, heap[adr]);
    }
  // CAS has been executed
  else if (op.type() & Instruction::Type::atomic && trace.accu(t))
    {
      const word_t adr = op.indirect() ? heap[op.arg()] : op.arg();
      trace.push_back_heap(cur, adr, heap[adr]);
    }

  // detect uninitialized reads
  if (op.type() & Instruction::Type::read)
    {
      word_t adr = op.arg();

      if (!trace.heap(adr))
        trace.init_heap(adr, heap[adr]);

      if (op.indirect() && !trace.heap(adr = heap[adr]))
        trace.init_heap(adr, heap[adr]);
    }

  // reset heap map for the next step
  // NOTE: really necessary?
  heap.clear();
}

// External::trace -------------------------------------------------------------

std::unique_ptr<Trace> External::trace (const Encoder & encoder)
{
  size_t lineno = 2;
  size_t next = 2;
  const auto & programs = encoder.programs;
  auto trace = std::make_unique<Trace>(programs, encoder.mmap);

  for (std::string line_buf; getline(stdout, line_buf); lineno++)
    {
      // skip empty lines
      if (line_buf.empty())
        continue;

      // parse symbol
      try
        {
          std::istringstream line(line_buf);
          Symbol symbol = parse(line);

          if (symbol == Symbol::ignore)
            continue;

          // detect an eventual heap update
          // reached next step: previous state at step - 1 fully visible
          if (step > 1 && step == next)
            update_heap(*trace, next++ - 2, step - 1);

          if (symbol == Symbol::accu)
            {
              trace->push_back_accu(step, thread, value);
            }
          else if (symbol == Symbol::mem)
            {
              trace->push_back_mem(step, thread, value);
            }
          else if (symbol == Symbol::sb_adr)
            {
              trace->push_back_sb_adr(step, thread, value);
            }
          else if (symbol == Symbol::sb_val)
            {
              trace->push_back_sb_val(step, thread, value);
            }
          else if (symbol == Symbol::sb_full)
            {
              trace->push_back_sb_full(step, thread, value);
            }
          else if (symbol == Symbol::stmt)
            {
              trace->push_back_pc(step, thread, pc);
            }
          else if (symbol == Symbol::exit_flag)
            {
              break;
            }
          else if (symbol == Symbol::exit_code)
            {
              trace->exit = value;
            }
          else if (symbol == Symbol::thread)
            {
              trace->push_back_thread(step, thread);
            }
          else if (symbol == Symbol::flush)
            {
              trace->push_back_thread(step, thread);
              trace->push_back_flush(step);
            }
        }
      catch (const std::exception & e)
        {
          parser_error(name(), lineno, e.what());
        }
    }

  // detect final heap update
  if (next > encoder.bound)
    update_heap(*trace, next - 2, step);

  return trace;
}

} // namespace ConcuBinE
