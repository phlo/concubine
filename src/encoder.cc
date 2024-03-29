/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#include "encoder.hh"

namespace ConcuBinE {

//==============================================================================
// Encoder
//==============================================================================

//------------------------------------------------------------------------------
// public constants
//------------------------------------------------------------------------------

const std::string Encoder::accu_sym      = "accu";
const std::string Encoder::mem_sym       = "mem";
const std::string Encoder::sb_adr_sym    = "sb-adr";
const std::string Encoder::sb_val_sym    = "sb-val";
const std::string Encoder::sb_full_sym   = "sb-full";
const std::string Encoder::stmt_sym      = "stmt";
const std::string Encoder::block_sym     = "block";
const std::string Encoder::halt_sym      = "halt";

const std::string Encoder::heap_sym      = "heap";
const std::string Encoder::exit_flag_sym = "exit";
const std::string Encoder::exit_code_sym = "exit-code";

const std::string Encoder::thread_sym    = "thread";
const std::string Encoder::exec_sym      = "exec";
const std::string Encoder::flush_sym     = "flush";
const std::string Encoder::check_sym     = "check";

//------------------------------------------------------------------------------
// public constructors
//------------------------------------------------------------------------------

Encoder::Encoder (const std::shared_ptr<Program::List> & p,
                  const std::shared_ptr<MMap> & m,
                  size_t b) :
  programs(p),
  mmap(m),
  bound(b),
  num_threads(p->size()),
  use_sinz_constraint(num_threads > 4)
{
  predecessors.reserve(num_threads);

  iterate_programs([this] (const Program & program)
    {
      // collect predecessors
      predecessors.push_back(program.predecessors());

      for (pc = 0; pc < program.size(); pc++)
        {
          const Instruction & op = program[pc];

          // collect statements requiring an empty store buffer
          if (op.requires_flush())
            flushes[thread].push_back(pc);

          // collect checkpoints
          if (!op.type())
            checkpoints[op.arg()][thread].push_back(pc);

          // collect explicit halt statements
          if (&op.symbol() == &Instruction::Halt::symbol)
            halts[thread].push_back(pc);

          // collect exit calls
          if (&op.symbol() == &Instruction::Exit::symbol)
            exits[thread].push_back(pc);
        }
    });

  // remove single-threaded checkpoints
  for (auto it = checkpoints.begin(); it != checkpoints.end();)
    if (it->second.size() == 1)
      it = checkpoints.erase(it);
    else
      ++it;
}

//------------------------------------------------------------------------------
// protected constants
//------------------------------------------------------------------------------

const std::string Encoder::accu_comment      = "accu variables";
const std::string Encoder::mem_comment       = "mem variables";
const std::string Encoder::sb_adr_comment    = "store buffer address variables";
const std::string Encoder::sb_val_comment    = "store buffer value variables";
const std::string Encoder::sb_full_comment   = "store buffer full variables";
const std::string Encoder::stmt_comment      = "statement activation variables";
const std::string Encoder::block_comment     = "blocking variables";
const std::string Encoder::halt_comment      = "halt variables";

const std::string Encoder::heap_comment      = "heap variable";
const std::string Encoder::exit_flag_comment = "exit flag variable";
const std::string Encoder::exit_code_comment = "exit code variable";

const std::string Encoder::thread_comment    = "thread activation variables";
const std::string Encoder::exec_comment      = "statement execution variables";
const std::string Encoder::flush_comment     = "store buffer flush variables";
const std::string Encoder::check_comment     = "checkpoint variables";

} // namespace ConcuBinE
