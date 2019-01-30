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

  inline std::string bad (std::string nid, std::string node)
    {
      return nid + " bad " + node + eol;
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
                              std::vector<std::string> conditions
                             )
    {
      std::ostringstream ss;

      ss << nid << " justice " << num << " ";

      std::copy(
        conditions.begin(),
        conditions.end() - 1,
        std::ostream_iterator<std::string>(ss, " "));

      ss << conditions.back() << eol;

      return ss.str();
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
}
#endif
