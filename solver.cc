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

// Solver::formula -------------------------------------------------------------

std::string Solver::formula (Encoder & encoder, const std::string & constraints)
{
  return encoder.str() + (constraints.empty() ? "" : eol + constraints);
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

  std_out = shell.run(command(), input);

  time = duration_cast<milliseconds>(high_resolution_clock::now() - t).count();

  std::string sat;
  return (std_out >> sat) && sat == "sat";
}

// External::solve -------------------------------------------------------------

Trace::ptr External::solve (Encoder & encoder, const std::string & constraints)
{
  sat(formula(encoder, constraints));
  return trace(encoder.programs);
}

// External::trace -------------------------------------------------------------

Trace::ptr External::trace (const Program::List::ptr & programs)
{
  size_t lineno = 2;
  size_t next = 2;
  Trace::ptr trace = std::make_unique<Trace>(programs);

  for (std::string line_buf; getline(std_out, line_buf); lineno++)
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
            {
              const size_t k = next++ - 2;
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

  return trace;
}

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
      return Symbol::exit_flag; // TODO
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

} // namespace ConcuBinE
