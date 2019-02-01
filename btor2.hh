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

  inline std::string declare_sort (std::string nid, std::string bits)
    {
      return nid + " sort bitvec " + bits + eol;
    }

  inline std::string declare_array (
                                    std::string nid,
                                    std::string idx_width,
                                    std::string val_width
                                   )
    {
      return nid + " sort array " + idx_width + " " + val_width + eol;
    }

  inline std::string constd (std::string nid, std::string sid, std::string val)
    {
      return
        nid + " " +
        (val == "0"
          ? "zero " + sid
          : val == "1"
            ? "one " + sid
            : "constd " + sid + " " + val) +
        eol;
    }

  inline std::string input (std::string nid, std::string sid)
    {
      return nid + " input " + sid + eol;
    }

  inline std::string state (std::string nid, std::string sid)
    {
      return nid + " state " + sid + eol;
    }

  inline std::string init (
                           std::string nid,
                           std::string sid,
                           std::string state,
                           std::string val
                          )
    {
      return nid + " init " + sid + " " + state + " " + val + eol;
    }

  inline std::string next (
                           std::string nid,
                           std::string sid,
                           std::string state,
                           std::string val
                          )
    {
      return nid + " next " + sid + " " + state + " " + val + eol;
    }

  inline std::string constraint (std::string nid, std::string node)
    {
      return nid + " constraint " + node + eol;
    }

  inline std::string constraint (unsigned long & nid)
    {
      std::string prev = std::to_string(nid - 1);
      return std::to_string(nid++) + " constraint " + prev + eol;
    }

  inline std::string bad (std::string nid, std::string node)
    {
      return nid + " bad " + node + eol;
    }

  inline std::string bad (unsigned long & nid)
    {
      std::string prev = std::to_string(nid - 1);
      return std::to_string(nid++) + " bad " + prev + eol;
    }

  inline std::string fair (std::string nid, std::string node)
    {
      return nid + " fair " + node + eol;
    }

  inline std::string output (std::string nid, std::string node)
    {
      return nid + " output " + node + eol;
    }

  inline std::string justice (
                              std::string nid,
                              std::string num,
                              std::vector<std::string> const & conditions
                             )
    {
      std::ostringstream os;

      os << nid << " justice " << num << " ";

      std::copy(
        conditions.begin(),
        conditions.end() - 1,
        std::ostream_iterator<std::string>(os, " "));

      os << conditions.back() << eol;

      return os.str();
    }

  inline std::string sext (std::string nid, std::string sid, std::string width)
    {
      return nid + " sext " + sid + " " + width + eol;
    }

  inline std::string uext (std::string nid, std::string sid, std::string width)
    {
      return nid + " uext " + sid + " " + width + eol;
    }

  inline std::string slice (
                            std::string nid,
                            std::string sid,
                            std::string upper,
                            std::string lower
                           )
    {
      return nid + " slice " + sid + " " + upper + " " + lower + eol;
    }

  inline std::string lnot (std::string nid, std::string sid, std::string node)
    {
      return nid + " not " + sid + " " + node + eol;
    }

  inline std::string inc (std::string nid, std::string sid, std::string node)
    {
      return nid + " inc " + sid + " " + node + eol;
    }

  inline std::string dec (std::string nid, std::string sid, std::string node)
    {
      return nid + " dec " + sid + " " + node + eol;
    }

  inline std::string neg (std::string nid, std::string sid, std::string node)
    {
      return nid + " neg " + sid + " " + node + eol;
    }

  inline std::string redand (std::string nid, std::string sid, std::string node)
    {
      return nid + " redand " + sid + " " + node + eol;
    }

  inline std::string redor (std::string nid, std::string sid, std::string node)
    {
      return nid + " redor " + sid + " " + node + eol;
    }

  inline std::string redxor (std::string nid, std::string sid, std::string node)
    {
      return nid + " redxor " + sid + " " + node + eol;
    }

  inline std::string iff (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " iff " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string implies (
                              std::string nid,
                              std::string sid,
                              std::string arg1,
                              std::string arg2
                             )
    {
      return nid + " implies " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string eq (
                         std::string nid,
                         std::string sid,
                         std::string arg1,
                         std::string arg2
                        )
    {
      return nid + " eq " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string neq (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " neq " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string sgt (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " sgt " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string ugt (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " ugt " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string sgte (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " sgte " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string ugte (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " ugte " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string slt (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " slt " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string ult (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " ult " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string slte (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " slte " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string ulte (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " ulte " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string land (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " and " + sid + " " + arg1 + " " + arg2 + eol;
    }

  /* variadic conjunction */
  inline std::string land (
                           unsigned long & nid,
                           std::string sid,
                           std::vector<std::string> const & args
                          )
    {
      std::ostringstream os;
      std::string id = std::to_string(nid++);

      os << land(id, sid, args[0], args[1]);

      for (size_t i = 2; i < args.size(); i++)
        os << land(id = std::to_string(nid++), sid, args[i], id);

      return os.str();
    }

  inline std::string nand (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " nand " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string nor (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " nor " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string lor (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " or " + sid + " " + arg1 + " " + arg2 + eol;
    }

  /* variadic disjunction */
  inline std::string lor (
                           unsigned long & nid,
                           std::string sid,
                           std::vector<std::string> const & args
                          )
    {
      std::ostringstream os;
      std::string id = std::to_string(nid++);

      os << lor(id, sid, args[0], args[1]);

      for (size_t i = 2; i < args.size(); i++)
        os << lor(id = std::to_string(nid++), sid, args[i], id);

      return os.str();
    }

  inline std::string xnor (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " xnor " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string lxor (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " xor " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string rol (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " rol " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string ror (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " ror " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string sll (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " sll " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string sra (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " sra " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string srl (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " srl " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string add (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " add " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string mul (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " mul " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string sdiv (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " sdiv " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string udiv (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " udiv " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string smod (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " smod " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string srem (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " srem " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string urem (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " urem " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string sub (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2
                         )
    {
      return nid + " sub " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string saddo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2
                           )
    {
      return nid + " saddo " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string uaddo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2
                           )
    {
      return nid + " uaddo " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string sdivo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2
                           )
    {
      return nid + " sdivo " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string udivo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2
                           )
    {
      return nid + " udivo " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string smulo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2
                           )
    {
      return nid + " smulo " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string umulo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2
                           )
    {
      return nid + " umulo " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string ssubo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2
                           )
    {
      return nid + " ssubo " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string usubo (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2
                           )
    {
      return nid + " usubo " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string concat (
                             std::string nid,
                             std::string sid,
                             std::string arg1,
                             std::string arg2
                            )
    {
      return nid + " concat " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string read (
                           std::string nid,
                           std::string sid,
                           std::string arg1,
                           std::string arg2
                          )
    {
      return nid + " read " + sid + " " + arg1 + " " + arg2 + eol;
    }

  inline std::string ite (
                          std::string nid,
                          std::string sid,
                          std::string arg1,
                          std::string arg2,
                          std::string arg3
                         )
    {
      return nid + " ite " + sid + " " + arg1 + " " + arg2 + " " + arg3 + eol;
    }

  inline std::string write (
                            std::string nid,
                            std::string sid,
                            std::string arg1,
                            std::string arg2,
                            std::string arg3
                           )
    {
      return nid + " write " + sid + " " + arg1 + " " + arg2 + " " + arg3 + eol;
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

      if (nands.size() > 1)
        os << land(nid, sid, nands);

      /* add <=1 constraint */
      os << constraint(nid);

      return os.str();
    }
}
#endif
