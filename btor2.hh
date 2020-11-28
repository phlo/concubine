/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#ifndef BTOR2_HH_
#define BTOR2_HH_

#include "common.hh"

#include <cassert>
#include <string>
#include <vector>

namespace ConcuBinE::btor2 {

//==============================================================================
// BTOR2 std::string generators for commonly used expressions
//==============================================================================

// number of generated expressions
//
extern long expressions;

using nid_t = uint64_t;

inline std::string comment (const std::string & comment)
{
  return "; " + comment;
}

const std::string comment_line =
  ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
  ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n";

inline std::string comment_section (const std::string & comment)
{
  std::string c = comment_line;
  return ((((c += "; ") += comment) += eol) += comment_line) += eol;
}

inline std::string comment_subsection (const std::string & comment)
{
  std::string c = comment_line + eol;
  c[1] = ' ';
  c[comment.size() + 2] = ' ';
  return c.replace(2, comment.size(), comment);
}

template <class ... T>
inline std::string expr (const std::string & nid, const T & ... args)
{
  expressions++;
  std::string e = nid;
  (((e += ' ') += args), ...);
  auto & end = e.back();
  if (end == ' ')
    end = eol;
  else
    e += eol;
  return e;
}

inline std::string sort_bitvec (const std::string & nid,
                                const std::string & width,
                                const std::string & sym = "")
{
  return expr(nid, "sort bitvec", width, sym);
}

inline std::string sort_array (const std::string & nid,
                               const std::string & idx_width,
                               const std::string & val_width,
                               const std::string & sym = "")
{
  return expr(nid, "sort array", idx_width, val_width, sym);
}

inline std::string constd (const std::string & nid,
                           const std::string & sid,
                           const std::string & val,
                           const std::string & sym = "")
{
  if (val == "0")
    return expr(nid, "zero", sid, sym);
  else if (val == "1")
    return expr(nid, "one", sid, sym);
  else
    return expr(nid, "constd", sid, val, sym);
}

inline std::string input (const std::string & nid,
                          const std::string & sid,
                          const std::string & sym = "")
{
  return expr(nid, "input", sid, sym);
}

inline std::string state (const std::string & nid,
                          const std::string & sid,
                          const std::string & sym = "")
{
  return expr(nid, "state", sid, sym);
}

inline std::string init (const std::string & nid,
                         const std::string & sid,
                         const std::string & state,
                         const std::string & val,
                         const std::string & sym = "")
{
  return expr(nid, "init", sid, state, val, sym);
}

inline std::string next (const std::string & nid,
                         const std::string & sid,
                         const std::string & state,
                         const std::string & val,
                         const std::string & sym = "")
{
  return expr(nid, "next", sid, state, val, sym);
}

inline std::string constraint (const std::string & nid,
                               const std::string & node,
                               const std::string & sym = "")
{
  return expr(nid, "constraint", node, sym);
}

inline std::string constraint (nid_t & nid, const std::string & sym = "")
{
  const std::string prev = std::to_string(nid - 1);
  return expr(std::to_string(nid++), "constraint", prev, sym);
}

inline std::string bad (const std::string & nid,
                        const std::string & node,
                        const std::string & sym = "")
{
  return expr(nid, "bad", node, sym);
}

inline std::string bad (nid_t & nid, const std::string & sym = "")
{
  const std::string prev = std::to_string(nid - 1);
  return expr(std::to_string(nid++), "bad", prev, sym);
}

inline std::string fair (const std::string & nid,
                         const std::string & node,
                         const std::string & sym = "")
{
  return expr(nid, "fair", node, sym);
}

inline std::string output (const std::string & nid,
                           const std::string & node,
                           const std::string & sym = "")
{
  return expr(nid, "output", node, sym);
}

inline std::string justice (const std::string & nid,
                            const std::string & num,
                            const std::vector<std::string> & conditions,
                            const std::string & sym = "")
{
  std::string e = nid;
  (((e += ' ') += "justice") += ' ') += num;

  for (const auto & s : conditions)
    (e += ' ') += s;

  if (!sym.empty())
    (e += ' ') += sym;

  return e += eol;
}

inline std::string sext (const std::string & nid,
                         const std::string & sid,
                         const std::string & node,
                         const std::string & width,
                         const std::string & sym = "")
{
  return expr(nid, "sext", sid, node, width, sym);
}

inline std::string uext (const std::string & nid,
                         const std::string & sid,
                         const std::string & node,
                         const std::string & width,
                         const std::string & sym = "")
{
  return expr(nid, "uext", sid, node, width, sym);
}

inline std::string slice (const std::string & nid,
                          const std::string & sid,
                          const std::string & node,
                          const std::string & upper,
                          const std::string & lower,
                          const std::string & sym = "")
{
  return expr(nid, "slice", sid, node, upper, lower, sym);
}

inline std::string lnot (const std::string & nid)
{
  return '-' + nid;
}

inline std::string lnot (const std::string & nid,
                         const std::string & sid,
                         const std::string & node,
                         const std::string & sym = "")
{
  return expr(nid, "not", sid, node, sym);
}

inline std::string inc (const std::string & nid,
                        const std::string & sid,
                        const std::string & node,
                        const std::string & sym = "")
{
  return expr(nid, "inc", sid, node, sym);
}

inline std::string dec (const std::string & nid,
                        const std::string & sid,
                        const std::string & node,
                        const std::string & sym = "")
{
  return expr(nid, "dec", sid, node, sym);
}

inline std::string neg (const std::string & nid,
                        const std::string & sid,
                        const std::string & node,
                        const std::string & sym = "")
{
  return expr(nid, "neg", sid, node, sym);
}

inline std::string redand (const std::string & nid,
                           const std::string & sid,
                           const std::string & node,
                           const std::string & sym = "")
{
  return expr(nid, "redand", sid, node, sym);
}

inline std::string redor (const std::string & nid,
                          const std::string & sid,
                          const std::string & node,
                          const std::string & sym = "")
{
  return expr(nid, "redor", sid, node, sym);
}

inline std::string redxor (const std::string & nid,
                           const std::string & sid,
                           const std::string & node,
                           const std::string & sym = "")
{
  return expr(nid, "redxor", sid, node, sym);
}

inline std::string iff (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "iff", sid, arg1, arg2, sym);
}

inline std::string implies (const std::string & nid,
                            const std::string & sid,
                            const std::string & arg1,
                            const std::string & arg2,
                            const std::string & sym = "")
{
  return expr(nid, "implies", sid, arg1, arg2, sym);
}

inline std::string eq (const std::string & nid,
                       const std::string & sid,
                       const std::string & arg1,
                       const std::string & arg2,
                       const std::string & sym = "")
{
  return expr(nid, "eq", sid, arg1, arg2, sym);
}

inline std::string neq (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "neq", sid, arg1, arg2, sym);
}

inline std::string sgt (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "sgt", sid, arg1, arg2, sym);
}

inline std::string ugt (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "ugt", sid, arg1, arg2, sym);
}

inline std::string sgte (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "sgte", sid, arg1, arg2, sym);
}

inline std::string ugte (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "ugte", sid, arg1, arg2, sym);
}

inline std::string slt (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "slt", sid, arg1, arg2, sym);
}

inline std::string ult (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "ult", sid, arg1, arg2, sym);
}

inline std::string slte (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "slte", sid, arg1, arg2, sym);
}

inline std::string ulte (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "ulte", sid, arg1, arg2, sym);
}

inline std::string land (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "and", sid, arg1, arg2, sym);
}

// variadic conjunction
//
inline std::string land (nid_t & nid,
                         const std::string & sid,
                         const std::vector<std::string> & args,
                         const std::string & sym = "")
{
  assert(args.size() > 1);

  auto it = args.begin();
  std::string e;
  std::string id = std::to_string(nid++);
  const std::string * arg1 = &*it;
  std::string arg2 = *++it;

  for (;;)
    {
      if (++it == args.end())
        {
          e += land(id, sid, *arg1, arg2, sym);
          break;
        }
      else
        {
          e += land(id, sid, *arg1, arg2);
        }

      arg1 = &*it;
      arg2 = std::move(id);
      id = std::to_string(nid++);
    }

  return e;
}

inline std::string nand (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "nand", sid, arg1, arg2, sym);
}

inline std::string nor (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "nor", sid, arg1, arg2, sym);
}

inline std::string lor (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "or", sid, arg1, arg2, sym);
}

// variadic disjunction
//
inline std::string lor (nid_t & nid,
                        const std::string & sid,
                        const std::vector<std::string> & args,
                        const std::string & sym = "")
{
  assert(args.size() > 1);

  auto it = args.begin();
  std::string e;
  std::string id = std::to_string(nid++);
  const std::string * arg1 = &*it;
  std::string arg2 = *++it;

  for (;;)
    {
      if (++it == args.end())
        {
          e += lor(id, sid, *arg1, arg2, sym);
          break;
        }
      else
        {
          e += lor(id, sid, *arg1, arg2);
        }

      arg1 = &*it;
      arg2 = std::move(id);
      id = std::to_string(nid++);
    }

  return e;
}

inline std::string xnor (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "xnor", sid, arg1, arg2, sym);
}

inline std::string lxor (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "xor", sid, arg1, arg2, sym);
}

inline std::string rol (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "rol", sid, arg1, arg2, sym);
}

inline std::string ror (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "ror", sid, arg1, arg2, sym);
}

inline std::string sll (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "sll", sid, arg1, arg2, sym);
}

inline std::string sra (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "sra", sid, arg1, arg2, sym);
}

inline std::string srl (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "srl", sid, arg1, arg2, sym);
}

inline std::string add (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "add", sid, arg1, arg2, sym);
}

inline std::string mul (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "mul", sid, arg1, arg2, sym);
}

inline std::string sdiv (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "sdiv", sid, arg1, arg2, sym);
}

inline std::string udiv (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "udiv", sid, arg1, arg2, sym);
}

inline std::string smod (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "smod", sid, arg1, arg2, sym);
}

inline std::string srem (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "srem", sid, arg1, arg2, sym);
}

inline std::string urem (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "urem", sid, arg1, arg2, sym);
}

inline std::string sub (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & sym = "")
{
  return expr(nid, "sub", sid, arg1, arg2, sym);
}

inline std::string saddo (const std::string & nid,
                          const std::string & sid,
                          const std::string & arg1,
                          const std::string & arg2,
                          const std::string & sym = "")
{
  return expr(nid, "saddo", sid, arg1, arg2, sym);
}

inline std::string uaddo (const std::string & nid,
                          const std::string & sid,
                          const std::string & arg1,
                          const std::string & arg2,
                          const std::string & sym = "")
{
  return expr(nid, "uaddo", sid, arg1, arg2, sym);
}

inline std::string sdivo (const std::string & nid,
                          const std::string & sid,
                          const std::string & arg1,
                          const std::string & arg2,
                          const std::string & sym = "")
{
  return expr(nid, "sdivo", sid, arg1, arg2, sym);
}

inline std::string udivo (const std::string & nid,
                          const std::string & sid,
                          const std::string & arg1,
                          const std::string & arg2,
                          const std::string & sym = "")
{
  return expr(nid, "udivo", sid, arg1, arg2, sym);
}

inline std::string smulo (const std::string & nid,
                          const std::string & sid,
                          const std::string & arg1,
                          const std::string & arg2,
                          const std::string & sym = "")
{
  return expr(nid, "smulo", sid, arg1, arg2, sym);
}

inline std::string umulo (const std::string & nid,
                          const std::string & sid,
                          const std::string & arg1,
                          const std::string & arg2,
                          const std::string & sym = "")
{
  return expr(nid, "umulo", sid, arg1, arg2, sym);
}

inline std::string ssubo (const std::string & nid,
                          const std::string & sid,
                          const std::string & arg1,
                          const std::string & arg2,
                          const std::string & sym = "")
{
  return expr(nid, "ssubo", sid, arg1, arg2, sym);
}

inline std::string usubo (const std::string & nid,
                          const std::string & sid,
                          const std::string & arg1,
                          const std::string & arg2,
                          const std::string & sym = "")
{
  return expr(nid, "usubo", sid, arg1, arg2, sym);
}

inline std::string concat (const std::string & nid,
                           const std::string & sid,
                           const std::string & arg1,
                           const std::string & arg2,
                           const std::string & sym = "")
{
  return expr(nid, "concat", sid, arg1, arg2, sym);
}

inline std::string read (const std::string & nid,
                         const std::string & sid,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & sym = "")
{
  return expr(nid, "read", sid, arg1, arg2, sym);
}

inline std::string ite (const std::string & nid,
                        const std::string & sid,
                        const std::string & arg1,
                        const std::string & arg2,
                        const std::string & arg3,
                        const std::string & sym = "")
{
  return expr(nid, "ite", sid, arg1, arg2, arg3, sym);
}

inline std::string write (const std::string & nid,
                          const std::string & sid,
                          const std::string & arg1,
                          const std::string & arg2,
                          const std::string & arg3,
                          const std::string & sym = "")
{
  return expr(nid, "write", sid, arg1, arg2, arg3, sym);
}

// boolean cardinality constraint =1: naive (pair wise)
//
inline std::string card_constraint_naive (nid_t & nid,
                                          const std::string & sid,
                                          const std::vector<std::string> & vars)
{
  const size_t n = vars.size();

  assert(n);

  std::string e;

  switch (n)
    {
    case 1:
      return constraint(std::to_string(nid++), vars.front());

    case 2:
      e = lxor(std::to_string(nid++), sid, vars.front(), vars.back());
      break;

    default:
      // >= 1
      e = lor(nid, sid, vars);
      e += constraint(nid);

      // <= 1
      std::vector<std::string> nands;

      for (auto it1 = vars.begin(); it1 != vars.end(); ++it1)
        for (auto it2 = it1 + 1; it2 != vars.end(); ++it2)
          e +=
            nand(
              nands.emplace_back(std::to_string(nid++)),
              sid,
              *it1,
              *it2);

      e += land(nid, sid, nands);
    }

  return e += constraint(nid);
}

// boolean cardinality constraint =1: Carsten Sinz's sequential counter
//
inline std::string card_constraint_sinz (nid_t & nid,
                                         const std::string & sid,
                                         const std::vector<std::string> & vars)
{
  const size_t n = vars.size();

  assert(n);

  std::string e;

  switch (n)
    {
    case 1:
      return constraint(std::to_string(nid++), vars.front());

    case 2:
      e = lxor(std::to_string(nid++), sid, vars.front(), vars.back());
      break;

    default:
      // >= 1
      e = lor(nid, sid, vars);
      e += constraint(nid);

      // n-1 auxiliary variables
      std::vector<std::string> auxs;
      auxs.reserve(n - 1);

      const auto end = --vars.end();

      for (auto it = vars.begin(); it != end; ++it)
        e +=
          input(
            auxs.emplace_back(std::to_string(nid++)),
            sid,
            *it + "_aux");

      // <= 1
      std::vector<std::string> ands;
      ands.reserve(3 * n - 4);

      auto var = vars.begin();
      auto aux = auxs.begin();

      // ¬x_1 v s_1
      e +=
        lor(
          ands.emplace_back(std::to_string(nid++)),
          sid,
          lnot(*var),
          *aux);

      while (++var != end)
        {
          // s_i-1
          const std::string & aux_prev = *aux++;

          // ¬x_i v s_i
          e +=
            lor(
              ands.emplace_back(std::to_string(nid++)),
              sid,
              lnot(*var),
              *aux);

          // ¬s_i-1 v s_i
          e +=
            lor(
              ands.emplace_back(std::to_string(nid++)),
              sid,
              lnot(aux_prev),
              *aux);

          // ¬x_i v ¬s_i-1
          e +=
            lor(
              ands.emplace_back(std::to_string(nid++)),
              sid,
              lnot(*var),
              lnot(aux_prev));
        }

      // ¬x_n v ¬s_n-1
      e +=
        lor(
          ands.emplace_back(std::to_string(nid++)),
          sid,
          lnot(*var),
          lnot(*aux));

      e += land(nid, sid, ands);
    }

  return e += constraint(nid);
}

} // namespace ConcuBinE::btor2

#endif
