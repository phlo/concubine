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

  // activate threads
  std::iota(active.begin(), active.end(), 0);
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
      trace->push_back_heap(step, address, value);
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

  state[thread] = State::running;
  trace->push_back_flush(step - 1);

  // skip state updates during final step
  if (step <= bound)
    {
      sb_full(false);
      trace->push_back_heap(step, sb_adr(), sb_val());
    }
}

// Simulator::execute ----------------------------------------------------------

void Simulator::execute ()
{
  // skip state updates during final step
  if (step > bound)
    return;

  const Program & program = (*programs)[thread];
  const Instruction & op = program[pc()];

  op.execute(*this);

  // set state to halted if it was the last command in the program
  if (op == program.back() && !(op.type() & Instruction::Type::control))
    {
      // take care if last instruction was a CHECK (bypasses WAITING)
      if (state[thread] == State::waiting)
        threads_per_checkpoint[program.back().arg()].erase(thread);
      else
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
  waiting_for_checkpoint[c.arg]++;

  // all other threads already at this checkpoint (or halted)?
  if (waiting_for_checkpoint[c.arg] >= threads_per_checkpoint[c.arg].size())
    {
      // reset number of waiting threads
      waiting_for_checkpoint[c.arg] = 0;

      // reactivate threads
      for (const word_t t : threads_per_checkpoint[c.arg])
        {
          state[t] = State::running;
          active.push_back(t);
        }
    }
}

void Simulator::execute (const Instruction::Halt & h [[maybe_unused]])
{
  state[thread] = State::halted;
  erase(active, thread);
}

void Simulator::execute (const Instruction::Exit & e)
{
  trace->exit = e.arg;
  state[thread] = State::exited;
}

// Simulator::run --------------------------------------------------------------

Trace::ptr Simulator::run (std::function<void()> scheduler)
{
  bool done = active.empty();

  while (!done && step <= bound)
    {
      scheduler();

      trace->push_back_thread(step++, thread);

      // flush store buffer or execute instruction
      if (state[thread] == State::flushing)
        flush();
      else
        execute();

      // handle state transitions
      switch (state[thread])
        {
        case State::running:
        case State::waiting: break;
        case State::halted: done = active.empty(); break;
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
  Simulator s (programs, mmap, bound);

  // random scheduler
  return s.run([&s] {
    s.thread = s.active[s.random() % s.active.size()];

    assert(s.state[s.thread] == State::running);

    // rule 2, 5, 7: store buffer may be flushed at any time or must be empty
    if (s.sb_full())
      {
        const Instruction & op = (*s.programs)[s.thread][s.pc()];

        if (s.random() % 2 || op.requires_flush())
          s.state[s.thread] = State::flushing;
      }
  });
}

// Simulator::replay -----------------------------------------------------------

Trace::ptr Simulator::replay (const Trace & trace, const size_t bound)
{
  Simulator s (trace.programs,
               {},
               bound && bound < trace.length ? bound : trace.length - 1);

  // copy memory map
  if (trace.mmap)
    s.trace->mmap = trace.mmap;

  // replay scheduler
  Trace::iterator it = trace.begin();

  return s.run([&s, &it] {
    if (it->flush)
      s.state[it->thread] = State::flushing;

    s.thread = it++->thread;
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
