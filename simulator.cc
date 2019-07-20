#include "simulator.hh"

#include <cassert>
#include <random>
#include <sstream>

namespace ConcuBinE {

//==============================================================================
// functions
//==============================================================================

// erases a given element from a STL container
//
template <class C, class T>
inline void erase (C & container, T & val)
{
  container.erase(find(container.begin(), container.end(), val));
}

//==============================================================================
// Simulator
//==============================================================================

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

Simulator::Simulator (const Program::List::ptr & p,
                      const std::shared_ptr<MMap> & mmap,
                      const size_t b) :
  random(seed),
  programs(p),
  trace(std::make_unique<Trace>(p, mmap)),
  step(0),
  bound(b ? b : static_cast<size_t>(-1)),
  state(p->size(), State::running),
  active(p->size())
{
  for (thread = 0; thread < programs->size(); thread++)
    {
      // initialize register states
      pc(0);
      accu(0);
      mem(0);
      sb_adr(0);
      sb_val(0);
      sb_full(false);

      // collect checkpoints
      for (const auto & [c, pcs] : (*programs)[thread].checkpoints)
        threads_per_checkpoint[c].insert(thread);
    }
}

//------------------------------------------------------------------------------
// member functions
//------------------------------------------------------------------------------

// Simulator::pc ---------------------------------------------------------------

word_t Simulator::pc () const
{
  return trace->pc(thread);
}

void Simulator::pc (const word_t pc)
{
  if (pc < (*programs)[thread].size())
    trace->push_back_pc(step, thread, pc);
}

void Simulator::pc_increment () { pc(pc() + 1); }

// Simulator::accu -------------------------------------------------------------

word_t Simulator::accu () const
{
  return trace->accu(thread);
}

void Simulator::accu (const word_t value)
{
  trace->push_back_accu(step, thread, value);
}

// Simulator::mem --------------------------------------------------------------

word_t Simulator::mem () const
{
  return trace->mem(thread);
}

void Simulator::mem (const word_t value)
{
  trace->push_back_mem(step, thread, value);
}

// Simulator::sb_adr -----------------------------------------------------------

word_t Simulator::sb_adr () const
{
  return trace->sb_adr(thread);
}

void Simulator::sb_adr (const word_t value)
{
  trace->push_back_sb_adr(step, thread, value);
}

// Simulator::sb_val -----------------------------------------------------------

word_t Simulator::sb_val () const
{
  return trace->sb_val(thread);
}

void Simulator::sb_val (const word_t value)
{
  trace->push_back_sb_val(step, thread, value);
}

// Simulator::sb_full ----------------------------------------------------------

bool Simulator::sb_full () const
{
  return trace->sb_full(thread);
}

void Simulator::sb_full (const bool value)
{
  trace->push_back_sb_full(step, thread, value);
}

// Simulator::load -------------------------------------------------------------

word_t Simulator::load (const word_t address)
{
  if (sb_full() && sb_adr() == address)
    return sb_val();

  std::optional<word_t> value = trace->heap(address);

  if (!value)
    {
      value = random();
      trace->init_heap(address, *value);
    }

  return *value;
}

word_t Simulator::load (word_t address, const bool indirect)
{
  if (indirect)
    address = load(address);

  return load(address);
}

// Simulator::store ------------------------------------------------------------

void Simulator::store (word_t address,
                       const word_t value,
                       const bool indirect,
                       const bool flush)
{
  assert(!sb_full());

  if (indirect)
    address = load(address);

  if (flush)
    {
      trace->push_back_heap(step, {address, value});
    }
  else
    {
      sb_full(true);
      sb_adr(address);
      sb_val(value);
    }
}

// Simulator::flush ------------------------------------------------------------

void Simulator::flush ()
{
  assert(sb_full());
  assert(state[thread] == State::flushing);

  sb_full(false);
  state[thread] = State::running;
  trace->push_back_flush(step - 1);
  trace->push_back_heap(step, {sb_adr(), sb_val()});
}

// Simulator::execute ----------------------------------------------------------

void Simulator::execute ()
{
  const Program & program = (*programs)[thread];
  const Instruction & op = program[pc()];

  // execute instruction
  op.execute(*this);

  // set state to halted if it was the last command in the program
  if (op == program.back() && state[thread] != State::exited && !op.is_jump())
    {
      // take care if last instruction was a CHECK (bypasses WAITING)
      if (state[thread] == State::waiting)
        // remove from list of waiting threads
        threads_per_checkpoint[program.back().arg()].erase(thread);
      else
        // remove from active threads
        erase(active, thread);

      state[thread] = State::halted;
    }
}

void Simulator::execute (const Instruction::Load & l)
{
  pc_increment();

  accu(load(l.arg, l.indirect));
}

void Simulator::execute (const Instruction::Store & s)
{
  pc_increment();

  store(s.arg, accu(), s.indirect);
}

void Simulator::execute (const Instruction::Fence & f [[maybe_unused]])
{
  pc_increment();
}

void Simulator::execute (const Instruction::Add & a)
{
  pc_increment();

  accu(accu() + load(a.arg, a.indirect));
}

void Simulator::execute (const Instruction::Addi & a)
{
  pc_increment();

  accu(accu() + a.arg);
}

void Simulator::execute (const Instruction::Sub & s)
{
  pc_increment();

  accu(accu() - load(s.arg, s.indirect));
}

void Simulator::execute (const Instruction::Subi & s)
{
  pc_increment();

  accu(accu() - s.arg);
}

void Simulator::execute (const Instruction::Mul & s)
{
  pc_increment();

  accu(accu() * load(s.arg, s.indirect));
}

void Simulator::execute (const Instruction::Muli & s)
{
  pc_increment();

  accu(accu() * s.arg);
}

void Simulator::execute (const Instruction::Cmp & c)
{
  pc_increment();

  accu(accu() - load(c.arg, c.indirect));
}

void Simulator::execute (const Instruction::Jmp & j)
{
  pc(j.arg);
}

void Simulator::execute (const Instruction::Jz & j)
{
  if (accu())
    pc_increment();
  else
    pc(j.arg);
}

void Simulator::execute (const Instruction::Jnz & j)
{
  if (accu())
    pc(j.arg);
  else
    pc_increment();
}

void Simulator::execute (const Instruction::Js & j)
{
  if (static_cast<sword_t>(accu()) < 0)
    pc(j.arg);
  else
    pc_increment();
}

void Simulator::execute (const Instruction::Jns & j)
{
  if (static_cast<sword_t>(accu()) >= 0)
    pc(j.arg);
  else
    pc_increment();
}

void Simulator::execute (const Instruction::Jnzns & j)
{
  if (static_cast<sword_t>(accu()) > 0)
    pc(j.arg);
  else
    pc_increment();
}

void Simulator::execute (const Instruction::Mem & m)
{
  pc_increment();

  accu(load(m.arg, m.indirect));
  mem(accu());
}

void Simulator::execute (const Instruction::Cas & c)
{
  pc_increment();

  if (mem() == load(c.arg, c.indirect))
    {
      store(c.arg, accu(), c.indirect, true);
      accu(1);
    }
  else
    {
      accu(0);
    }
}

void Simulator::execute (const Instruction::Check & c)
{
  pc_increment();

  state[thread] = State::waiting;

  // remove from list of active threads
  erase(active, thread);

  // add to set of waiting threads
  waiting_for_checkpoint[c.arg].insert(thread);

  // all other threads already waiting at this checkpoint?
  check_and_resume(c.arg);
}

void Simulator::execute (const Instruction::Halt & h [[maybe_unused]])
{
  state[thread] = State::halted;
}

void Simulator::execute (const Instruction::Exit & e)
{
  trace->exit = e.arg;
  state[thread] = State::exited;
}

// Simulator::check_and_resume -------------------------------------------------

void Simulator::check_and_resume (word_t id)
{
  // all other threads already at this checkpoint (or halted)?
  if (waiting_for_checkpoint[id].size() >= threads_per_checkpoint[id].size())
    {
      // reset number of waiting threads
      waiting_for_checkpoint[id].clear();

      // reactivate threads
      for (const word_t t : threads_per_checkpoint[id])
        {
          state[t] = State::running;
          active.push_back(t);
        }
    }
}

// Simulator::run --------------------------------------------------------------

Trace::ptr Simulator::run (std::function<word_t()> scheduler)
{
  // activate threads
  std::iota(active.begin(), active.end(), 0);

  bool done = active.empty();

  while (!done && ++step <= bound)
    {
      thread = scheduler();

      trace->push_back_thread(step - 1, thread);

      // flush store buffer or execute instruction
      if (state[thread] == State::flushing)
        flush();
      else
        execute();

      // handle state transitions
      switch (state[thread])
        {
        // keep 'em running
        case State::running:

        // checkpoint reached
        case State::waiting: break;

        // halted - quit if all the others also stopped
        case State::halted:
          {
            // check if we were the last thread standing
            done = true;
            for (auto it = active.begin(); done && it != active.end(); ++it)
              if (state[*it] != State::halted)
                done = false;

            break;
          }

        // exiting - return exit code
        case State::exited: done = true; break;

        default:
          {
            std::ostringstream m;
            m << "illegal thread state transition "
              << State::running
              << " -> "
              << state[thread];
            throw std::runtime_error(m.str());
          }
        }
    }

  return move(trace);
}

// Simulator::simulate ---------------------------------------------------------

Trace::ptr Simulator::simulate (const Program::List::ptr & programs,
                                const std::shared_ptr<MMap> & mmap,
                                const size_t bound)
{
  Simulator sim {programs, mmap, bound};

  // random scheduler
  return sim.run([&sim] {
    sim.thread = sim.active[sim.random() % sim.active.size()];

    assert(sim.state[sim.thread] == State::running);

    // rule 2, 5, 7: store buffer may be flushed at any time or must be empty
    if (sim.sb_full())
      {
        const Instruction & op =
          (*sim.programs)[sim.thread][sim.pc()];

        if (sim.random() % 2 || op.requires_flush())
          sim.state[sim.thread] = State::flushing;
      }

    return sim.thread;
  });
}

// Simulator::replay -----------------------------------------------------------

Trace::ptr Simulator::replay (const Trace & trace, const size_t bound)
{
  Simulator sim {
    trace.programs,
    {},
    bound && bound < trace.length ? bound : trace.length - 1
  };

  // replay scheduler
  Trace::iterator it = trace.begin();

  return sim.run([&sim, &it] {
    if (it->flush)
      sim.state[it->thread] = State::flushing;

    return it++->thread;
  });
}

//==============================================================================
// non-member operators
//==============================================================================

std::ostream & operator << (std::ostream & os, Simulator::State s)
{
  return os << static_cast<char>(s);
}

} // namespace ConcuBinE
