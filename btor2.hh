#ifndef BTOR2_HH_
#define BTOR2_HH_

#include "common.hh"

#include <iterator>
#include <sstream>
#include <string>
#include <vector>

/*******************************************************************************
 * BTOR2 std::string generators for commonly used expressions
 *
 * Note: namespace to avoid hiding problems due to frequently occurring names
 ******************************************************************************/

namespace btor2
{
  inline std::string comment (std::string comment)
    {
      return "; " + comment;
    }

  const std::string comment_line =
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n";

  inline std::string comment_section (std::string comment)
    {
      return comment_line + "; " + comment + eol + comment_line + eol;
    }

  inline std::string comment_subsection (std::string comment)
    {
      std::string c = comment_line + eol;
      return c.replace(1, 2 + comment.size(), " " + comment + " ");
    }

  inline std::string line(std::string node, std::string sym)
    {
      return node + (!sym.empty() ? " " + sym : "") + eol;
    }

  inline std::string declare_sort (
                                   std::string nid,
                                   std::string bits,
                                   std::string sym = ""
                                  )
    {
      return line(nid + " sort bitvec " + bits, sym);
    }

  inline std::string declare_array (
                                    std::string nid,
                                    std::string idx_width,
                                    std::string val_width,
                                    std::string sym = ""
                                   )
    {
      return line(nid + " sort array " + idx_width + " " + val_width, sym);
    }

  inline std::string constd (
                             std::string nid,
                             std::string sid,
                             std::string val,
                             std::string sym = ""
                            )
    {
      return
        line(
          nid + " " +
          (val == "0"
            ? "zero " + sid
            : val == "1"
              ? "one " + sid
              : "constd " + sid + " " + val),
          sym);
    }

  inline std::string input (
                            std::string nid,
                            std::string sid,
                            std::string sym = ""
                           )
    {
      return line(nid + " input " + sid, sym);
    }

  inline std::string state (
                            std::string nid,
                            std::string sid,
                            std::string sym = ""
                           )
    {
      return line(nid + " state " + sid, sym);

    }

  inline std::string init (
                           std::string nid,
                           std::string sid,
                           std::string state,
                           std::string val,
                           std::string sym = ""
                          )
    {
      return line(nid + " init " + sid + " " + state + " " + val, sym);
    }

  inline std::string next (
                           std::string nid,
                           std::string sid,
                           std::string state,
                           std::string val,
                           std::string sym = ""
                          )
    {
      return line(nid + " next " + sid + " " + state + " " + val, sym);
    }

  inline std::string constraint (
                                 std::string nid,
                                 std::string node,
                                 std::string sym = ""
                                )
    {
      return line(nid + " constraint " + node, sym);
    }

  inline std::string constraint (unsigned long & nid, std::string sym = "")
    {
      std::string prev = std::to_string(nid - 1);
      return line(std::to_string(nid++) + " constraint " + prev, sym);
    }

  inline std::string bad (
                          std::string nid,
                          std::string node,
                          std::string sym = ""
                         )
    {
      return line(nid + " bad " + node, sym);
    }

  inline std::string bad (unsigned long & nid, std::string sym = "")
    {
      std::string prev = std::to_string(nid - 1);
      return line(std::to_string(nid++) + " bad " + prev, sym);
    }

  inline std::string fair (
                           std::string nid,
                           std::string node,
                           std::string sym = ""
                          )
    {
      return line(nid + " fair " + node, sym);
    }

  inline std::string output (
                             std::string nid,
                             std::string node,
                             std::string sym = ""
                            )
    {
      return line(nid + " output " + node, sym);
    }

  inline std::string justice (
                              std::string nid,
                              std::string num,
                              std::vector<std::string> const & conditions,
                              std::string sym = ""
                             )
    {
      std::ostringstream os;

      os << nid << " justice " << num << " ";

      std::copy(
        conditions.begin(),
        conditions.end() - 1,
        std::ostream_iterator<std::string>(os, " "));

      os << conditions.back();

      return line(os.str(), sym);
    }

  inline std::string sext (
                           std::string nid,
                           std::string sid,
                           std::string width,
                           std::string sym = ""
                          )
    {
      return line(nid + " sext " + sid + " " + width, sym);
    }

  inline std::string uext (
                           std::string nid,
                           std::string sid,
                           std::string width,
                           std::string sym = ""
                          )
    {
      return line(nid + " uext " + sid + " " + width, sym);
    }

  inline std::string slice (
                            std::string nid,
                            std::string sid,
                            std::string upper,
                            std::string lower,
                            std::string sym = ""
                           )
    {
      return line(nid + " slice " + sid + " " + upper + " " + lower, sym);
    }

  inline std::string lnot (
                           std::string nid,
                           std::string sid,
                           std::string node,
                           std::string sym = ""
                          )
    {
      return line(nid + " not " + sid + " " + node, sym);
    }

  inline std::string inc (
                          std::string nid,
                          std::string sid,
                          std::string node,
                          std::string sym = ""
                         )
    {
      return line(nid + " inc " + sid + " " + node, sym);
    }

  inline std::string dec (
                          std::string nid,
                          std::string sid,
                          std::string node,
                          std::string sym = ""
                         )
    {
      return line(nid + " dec " + sid + " " + node, sym);
    }

  inline std::string neg (
                          std::string nid,
                          std::string sid,
                          std::string node,
                          std::string sym = ""
                         )
    {
      return line(nid + " neg " + sid + " " + node, sym);
    }

  inline std::string redand (
                             std::string nid,
                             std::string sid,
                             std::string node,
                             std::string sym = ""
                            )
    {
      return line(nid + " redand " + sid + " " + node, sym);
    }

  inline std::string redor (
                            std::string nid,
                            std::string sid,
                            std::string node,
                            std::string sym = ""
                           )
    {
      return line(nid + " redor " + sid + " " + node, sym);
    }

  inline std::string redxor (
                             std::string nid,
                             std::string sid,
                             std::string node,
                             std::string sym = ""
                            )
    {
      return line(nid + " redxor " + sid + " " + node, sym);
    }

  inline std::string iff (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " iff " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string implies (
                              std::string nid,
                              std::string sid,
                              std::string arg1,
                              std::string arg2,
                              std::string sym = ""
                             )
    {
      return line(nid + " implies " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string eq (
                         std::string nid,
                         std::string sid,
                         std::string arg1,
                         std::string arg2,
                         std::string sym = ""
                        )
    {
      return line(nid + " eq " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string neq (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " neq " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string sgt (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " sgt " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string ugt (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " ugt " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string sgte (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " sgte " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string ugte (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " ugte " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string slt (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " slt " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string ult (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " ult " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string slte (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " slte " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string ulte (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " ulte " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string land (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " and " + sid + " " + arg1 + " " + arg2, sym);
    }

  /* variadic conjunction */
  inline std::string land (
                           unsigned long & nid,
                           std::string sid,
                           std::vector<std::string> const & args,
                           std::string sym = ""
                          )
    {
      std::ostringstream os;
      std::string id = std::to_string(nid++);

      os << land(id, sid, args[0], args[1]);

      for (size_t i = 2; i < args.size(); i++)
        os << land(id = std::to_string(nid++), sid, args[i], id);

      /* remove trailing space */
      std::string node = os.str();

      node.erase(node.end() - 1);

      return line(node, sym);
    }

  inline std::string nand (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " nand " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string nor (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " nor " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string lor (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " or " + sid + " " + arg1 + " " + arg2, sym);
    }

  /* variadic disjunction */
  inline std::string lor (
                           unsigned long & nid,
                           std::string sid,
                           std::vector<std::string> const & args,
                           std::string sym = ""
                          )
    {
      std::ostringstream os;
      std::string id = std::to_string(nid++);

      os << lor(id, sid, args[0], args[1]);

      for (size_t i = 2; i < args.size(); i++)
        os << lor(id = std::to_string(nid++), sid, args[i], id);

      /* remove trailing space */
      std::string node = os.str();

      node.erase(node.end() - 1);

      return line(node, sym);
    }

  inline std::string xnor (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " xnor " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string lxor (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " xor " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string rol (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " rol " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string ror (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " ror " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string sll (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " sll " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string sra (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " sra " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string srl (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " srl " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string add (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " add " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string mul (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " mul " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string sdiv (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " sdiv " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string udiv (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " udiv " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string smod (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " smod " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string srem (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " srem " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string urem (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " urem " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string sub (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string sym = ""
                         )
    {
      return line(nid + " sub " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string saddo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2,
                            std::string sym = ""
                           )
    {
      return line(nid + " saddo " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string uaddo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2,
                            std::string sym = ""
                           )
    {
      return line(nid + " uaddo " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string sdivo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2,
                            std::string sym = ""
                           )
    {
      return line(nid + " sdivo " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string udivo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2,
                            std::string sym = ""
                           )
    {
      return line(nid + " udivo " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string smulo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2,
                            std::string sym = ""
                           )
    {
      return line(nid + " smulo " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string umulo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2,
                            std::string sym = ""
                           )
    {
      return line(nid + " umulo " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string ssubo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2,
                            std::string sym = ""
                           )
    {
      return line(nid + " ssubo " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string usubo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2,
                            std::string sym = ""
                           )
    {
      return line(nid + " usubo " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string concat (
                             std::string nid,
                             std::string sid,
                             std::string arg1,
                             std::string arg2,
                             std::string sym = ""
                            )
    {
      return line(nid + " concat " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string read (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2,
                           std::string sym = ""
                          )
    {
      return line(nid + " read " + sid + " " + arg1 + " " + arg2, sym);
    }

  inline std::string ite (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string arg3,
                          std::string sym = ""
                         )
    {
      return
        line(nid + " ite " + sid + " " + arg1 + " " + arg2 + " " + arg3, sym);
    }

  inline std::string write (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2,
                            std::string arg3,
                            std::string sym = ""
                           )
    {
      return
        line(nid + " write " + sid + " " + arg1 + " " + arg2 + " " + arg3, sym);
    }

  /* boolean cardinality constraint =1: naive (pair wise) *********************/
  inline std::string
  card_constraint_naive (
                         unsigned long & nid,
                         std::string sid,
                         std::vector<std::string> const & vars
                        )
    {
      std::ostringstream os;
      std::vector<std::string>::const_iterator it1, it2;

      /* require one to be true */
      os << lor(nid, sid, vars);

      /* add >=1 constraint */
      os << constraint(nid);

      /* require at most one to be true */
      std::vector<std::string> nands;

      for (it1 = vars.begin(); it1 != vars.end(); ++it1)
        for (it2 = it1 + 1; it2 != vars.end(); ++it2)
          os <<
            nand(
              nands.emplace_back(std::to_string(nid++)),
              sid,
              *it1,
              *it2);

      // TODO: constraint for every nand instead?
      if (nands.size() > 1)
        os << land(nid, sid, nands);

      /* add <=1 constraint */
      os << constraint(nid);

      return os.str();
    }

  /* boolean cardinality constraint =1: Carsten Sinz's sequential counter *****/
  inline std::string
  card_constraint_sinz (
                        unsigned long & nid,
                        std::string sid,
                        std::vector<std::string> const & vars
                       )
    {
      std::ostringstream os;

      unsigned int n = vars.size();

      /* require one to be true */
      os << lor(nid, sid, vars);

      /* add >=1 constraint */
      os << constraint(nid);

      /* add inputs for auxiliary variables */
      std::vector<std::string> aux;

      for (size_t i = 0; i < n - 1; i++)
        os <<
          input(
            aux.emplace_back(std::to_string(nid++)),
            sid,
            "card_aux_" + std::to_string(i));

      /* Sinz's sequential counter constraint */
      std::string prev = std::to_string(nid++);

      /* ¬x_1 v s_1 */
      os << lnot(prev, sid, vars[0]);
      os << lor(prev = std::to_string(nid++), sid, aux[0], prev);
      os << constraint(std::to_string(nid++), prev);

      /* ¬x_n v ¬s_n-1 */
      std::string not_x = std::to_string(nid++);
      std::string not_s = std::to_string(nid++);

      os << lnot(not_x, sid, vars.back());
      os << lnot(not_s, sid, aux.back());
      os << lor(prev = std::to_string(nid++), sid, not_x, not_s);
      os << constraint(std::to_string(nid++), prev);

      for (size_t i = 1; i < n - 1; i++)
        {
          /* ¬x_i v s_i */
          os << lnot(not_x = std::to_string(nid++), sid, vars[i]);
          os << lor(prev = std::to_string(nid++), sid, aux[i], not_x);
          os << constraint(std::to_string(nid++), prev);

          /* ¬s_i-1 v s_i */
          os << lnot(not_s = std::to_string(nid++), sid, aux[i - 1]);
          os << lor(prev = std::to_string(nid++), sid, aux[i], not_s);
          os << constraint(std::to_string(nid++), prev);

          /* ¬x_i v ¬s_i-1 */
          os << lor(prev = std::to_string(nid++), sid, not_x, not_s);
          os << constraint(std::to_string(nid++), prev);
        }

      return os.str();
    }
}
#endif
