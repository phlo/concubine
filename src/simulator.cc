/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#include "simulator.hh"

#include <cassert>
#include <random>
#include <sstream>

#include "instruction.hh"
#include "trace.hh"

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
// public member functions
//------------------------------------------------------------------------------

// Simulator::simulate ---------------------------------------------------------

std::unique_ptr<Trace> Simulator::simulate (const std::shared_ptr<Program::List> & p,
                                            const std::shared_ptr<MMap> & m,
                                            const size_t b)
{
  init(p, m, b);

  // random scheduler
  return run([this] {
    thread = active[random() % active.size()];

    assert(state[thread] == State::running);

    // rule 2, 5, 7: store buffer may be flushed at any time or must be empty
    if (sb_full())
      if (random() % 2 || (*programs)[thread][pc()].requires_flush())
        state[thread] = State::flushing;
  });
}

// Simulator::replay -----------------------------------------------------------

std::unique_ptr<Trace> Simulator::replay (const Trace & t, const size_t b)
{
  init(t.programs, t.mmap, b && b < t.size() ? bound : t.size() - 1);

  // replay scheduler
  Trace::iterator it = t.begin();

  return run([this, &it] {
    if (it->flush)
      state[it->thread] = State::flushing;

    thread = it++->thread;
  });
}

// Simulator::execute ----------------------------------------------------------

template <>
void Simulator::execute (const Instruction::Load & l)
{
  pc_increment();

  accu(load(l.arg, l.indirect));
}

template <>
void Simulator::execute (const Instruction::Store & s)
{
  pc_increment();

  store(s.arg, accu(), s.indirect);
}

template <>
void Simulator::execute (const Instruction::Fence & f [[maybe_unused]])
{
  pc_increment();
}

template <>
void Simulator::execute (const Instruction::Add & a)
{
  pc_increment();

  accu(accu() + load(a.arg, a.indirect));
}

template <>
void Simulator::execute (const Instruction::Addi & a)
{
  pc_increment();

  accu(accu() + a.arg);
}

template <>
void Simulator::execute (const Instruction::Sub & s)
{
  pc_increment();

  accu(accu() - load(s.arg, s.indirect));
}

template <>
void Simulator::execute (const Instruction::Subi & s)
{
  pc_increment();

  accu(accu() - s.arg);
}

template <>
void Simulator::execute (const Instruction::Mul & s)
{
  pc_increment();

  accu(accu() * load(s.arg, s.indirect));
}

template <>
void Simulator::execute (const Instruction::Muli & s)
{
  pc_increment();

  accu(accu() * s.arg);
}

template <>
void Simulator::execute (const Instruction::Cmp & c)
{
  pc_increment();

  accu(accu() - load(c.arg, c.indirect));
}

template <>
void Simulator::execute (const Instruction::Jmp & j)
{
  pc(j.arg);
}

template <>
void Simulator::execute (const Instruction::Jz & j)
{
  if (accu())
    pc_increment();
  else
    pc(j.arg);
}

template <>
void Simulator::execute (const Instruction::Jnz & j)
{
  if (accu())
    pc(j.arg);
  else
    pc_increment();
}

template <>
void Simulator::execute (const Instruction::Js & j)
{
  if (static_cast<sword_t>(accu()) < 0)
    pc(j.arg);
  else
    pc_increment();
}

template <>
void Simulator::execute (const Instruction::Jns & j)
{
  if (static_cast<sword_t>(accu()) >= 0)
    pc(j.arg);
  else
    pc_increment();
}

template <>
void Simulator::execute (const Instruction::Jnzns & j)
{
  if (static_cast<sword_t>(accu()) > 0)
    pc(j.arg);
  else
    pc_increment();
}

template <>
void Simulator::execute (const Instruction::Mem & m)
{
  pc_increment();

  accu(load(m.arg, m.indirect));
  mem(accu());
}

template <>
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

template <>
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

template <>
void Simulator::execute (const Instruction::Halt & h [[maybe_unused]])
{
  state[thread] = State::halted;
  erase(active, thread);
}

template <>
void Simulator::execute (const Instruction::Exit & e)
{
  trace->exit = e.arg;
  state[thread] = State::exited;
}

//------------------------------------------------------------------------------
// private member functions
//------------------------------------------------------------------------------

// Simulator::init -------------------------------------------------------------

void Simulator::init (const std::shared_ptr<Program::List> & p,
                      const std::shared_ptr<MMap> & m,
                      const size_t b)
{
  const size_t num_threads = p->size();

  random.seed(seed);
  programs = p.get();
  trace = std::make_unique<Trace>(p, m);
  bound = b ? b : static_cast<size_t>(-1);
  step = 0;

  // initialize state vector
  state.assign(num_threads, State::running);

  // activate threads
  active.resize(num_threads);
  std::iota(active.begin(), active.end(), 0);

  for (thread = 0; thread < num_threads; thread++)
    {
      // initialize register states
      pc(0);
      accu(0);
      mem(0);
      sb_adr(0);
      sb_val(0);
      sb_full(false);

      // collect checkpoints
      for (const auto & op : (*programs)[thread])
        if (!op.type())
          threads_per_checkpoint[op.arg()].insert(thread);
    }

  // reset waiting map
  waiting_for_checkpoint.clear();
}

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
  const Program & program = (*programs)[thread];
  const Instruction & op = program[pc()];

  // skip all state updates except EXIT calls during the final step
  if (step > bound && &op.symbol() != &Instruction::Exit::symbol)
    return;

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

// Simulator::run --------------------------------------------------------------

std::unique_ptr<Trace> Simulator::run (std::function<void()> scheduler)
{
  assert(trace);

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

  return std::move(trace);
}

//==============================================================================
// non-member operators
//==============================================================================

std::ostream & operator << (std::ostream & os, Simulator::State s)
{
  return os << static_cast<char>(s);
}

} // namespace ConcuBinE
