#include "solver.hh"

#include <cassert>
#include <chrono>

#include "encoder.hh"
#include "parser.hh"
#include "shell.hh"

namespace ConcuBinE {

//==============================================================================
// Solver
//==============================================================================

// Solver::build_formula -------------------------------------------------------

std::string Solver::build_formula (Encoder & formula,
                                   const std::string & constraints)
{
  return formula.str() + eol + (constraints.empty() ? "" : constraints + eol);
}

//==============================================================================
// External
//==============================================================================

// External::sat ---------------------------------------------------------------

bool External::sat (const std::string & input)
{
  using namespace std::chrono;

  Shell shell;

  high_resolution_clock::time_point t = high_resolution_clock::now();

  std_out = shell.run(build_command(), input);

  time = duration_cast<milliseconds>(high_resolution_clock::now() - t).count();

  std::string sat;
  return (std_out >> sat) && sat == "sat";
}

// External::solve -------------------------------------------------------------

Trace::ptr External::solve (Encoder & formula, const std::string & constraints)
{
  sat(build_formula(formula, constraints));
  return build_trace(formula.programs);
}

// External::build_trace -------------------------------------------------------

Trace::ptr External::build_trace (const Program::List::ptr & programs)
{
  Trace::ptr trace = std::make_unique<Trace>(programs);

  // current line number
  size_t lineno = 2;

  for (std::string line_buf; getline(std_out, line_buf); lineno++)
    {
      // skip empty lines
      if (line_buf.empty())
        continue;

      // parse symbol
      try
        {
          std::istringstream line(line_buf);
          Symbol symbol = parse_line(line);

          if (symbol == Symbol::ignore)
            continue;

          // detect an eventual heap update
          // reached next step: previous state at step - 1 fully visible
          if (step > 1 && step == trace->length)
            {
              const size_t k = step - 2;
              const word_t t = trace->thread(k);

              // instruction responsible for state at step - 1
              const Instruction & op = (*programs)[t][trace->pc(k, t)];

              // store buffer has been flushed
              // NOTE: heap update visible one step after flush is set
              if (trace->flush(k))
                {
                  const word_t adr = trace->sb_adr(t);
                  trace->push_back_heap(step - 1, adr, heap[adr]);
                }
              // CAS has been executed
              else if (op.type() & Instruction::Type::atomic && trace->accu(t))
                {
                  const word_t adr = op.indirect() ? heap[op.arg()] : op.arg();
                  trace->push_back_heap(step - 1, adr, heap[adr]);
                }

              // detect uninitialized reads
              if (op.type() & Instruction::Type::read)
                {
                  word_t adr = op.arg();

                  if (!trace->heap(adr))
                    trace->init_heap(adr, heap[adr]);

                  if (op.indirect() && !trace->heap(adr = heap[adr]))
                    trace->init_heap(adr, heap[adr]);
                }

              // reset heap map for the next step
              // NOTE: really necessary?
              heap.clear();
            }

          switch (symbol)
            {
            case Symbol::accu:
              trace->push_back_accu(step, thread, value);
              break;

            case Symbol::mem:
              trace->push_back_mem(step, thread, value);
              break;

            case Symbol::sb_adr:
              trace->push_back_sb_adr(step, thread, value);
              break;

            case Symbol::sb_val:
              trace->push_back_sb_val(step, thread, value);
              break;

            case Symbol::sb_full:
              trace->push_back_sb_full(step, thread, value);
              break;

            case Symbol::thread:
              trace->push_back_thread(step, thread);
              break;

            case Symbol::stmt:
              trace->push_back_pc(step, thread, pc);
              break;

            case Symbol::flush:
              trace->push_back_thread(step, thread);
              trace->push_back_flush(step);
              break;

            case Symbol::exit_flag:
              break;

            case Symbol::exit_code:
              trace->exit = value;
              break;

            default: break;
            }
        }
      catch (const std::exception & e)
        {
          parser_error(name(), lineno, e.what());
        }
    }

  return trace;
}

// External::parse_symbol ------------------------------------------------------

size_t External::parse_symbol (std::istringstream & line,
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

External::Symbol External::parse_symbol (std::istringstream & line)
{
  std::string name;

  if (!getline(line >> std::ws, name, '_'))
    throw std::runtime_error("missing symbol");

  line.unget(); // restore initial delimiter

  if (name == Encoder::accu_sym)
    {
      step = parse_symbol(line, "step");
      thread = parse_symbol(line, "thread");
      return Symbol::accu;
    }
  else if (name == Encoder::mem_sym)
    {
      step = parse_symbol(line, "step");
      thread = parse_symbol(line, "thread");
      return Symbol::mem;
    }
  else if (name == Encoder::sb_adr_sym)
    {
      step = parse_symbol(line, "step");
      thread = parse_symbol(line, "thread");
      return Symbol::sb_adr;
    }
  else if (name == Encoder::sb_val_sym)
    {
      step = parse_symbol(line, "step");
      thread = parse_symbol(line, "thread");
      return Symbol::sb_val;
    }
  else if (name == Encoder::sb_full_sym)
    {
      step = parse_symbol(line, "step");
      thread = parse_symbol(line, "thread");
      return Symbol::sb_full;
    }
  else if (name == Encoder::stmt_sym)
    {
      step = parse_symbol(line, "step");
      thread = parse_symbol(line, "thread");
      pc = parse_symbol(line, "pc");
      return Symbol::stmt;
    }
  else if (name == Encoder::heap_sym)
    {
      step = parse_symbol(line, "step");
      return Symbol::heap;
    }
  else if (name == Encoder::exit_flag_sym)
    {
      step = parse_symbol(line, "step");
      return Symbol::exit_flag; // TODO
    }
  else if (name == Encoder::exit_code_sym)
    {
      return Symbol::exit_code;
    }
  else if (name == Encoder::thread_sym)
    {
      step = parse_symbol(line, "step");
      thread = parse_symbol(line, "thread");
      return Symbol::thread;
    }
  else if (name == Encoder::flush_sym)
    {
      step = parse_symbol(line, "step");
      thread = parse_symbol(line, "thread");
      return Symbol::flush;
    }

  return Symbol::ignore;
}

} // namespace ConcuBinE
