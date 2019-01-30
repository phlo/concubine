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

  inline std::string declare_sort (unsigned nid, unsigned bits)
    {
      return std::to_string(nid) + " sort bitvec " + std::to_string(bits) + eol;
    }

  inline std::string declare_array (
                                    unsigned nid,
                                    unsigned idx_width,
                                    unsigned val_width
                                   )
    {
      return
        std::to_string(nid) +
        " sort array " +
        std::to_string(idx_width) +
        " " + std::to_string(val_width) +
        eol;
    }

  inline std::string constd (unsigned nid, unsigned sid, unsigned val)
    {
      /* TODO: decide!
      if (!val)
        return std::to_string(nid) + " zero " + std::to_string(sid);
      else if (val == 1)
        return std::to_string(nid) + " one " + std::to_string(sid);
      else
        return
          std::to_string(nid) +
          " constd " +
          std::to_string(sid) +
          " " +
          std::to_string(val) +
          eol;
      */

      return
        std::to_string(nid) + " " +
        (!val
          ? "zero " + std::to_string(sid)
          : val == 1
            ? "one " + std::to_string(sid)
            : "constd " + std::to_string(sid) + " " + std::to_string(val)) +
        eol;
    }

  inline std::string input (unsigned nid, unsigned sid)
    {
      return std::to_string(nid) + " input " + std::to_string(sid) + eol;
    }

  inline std::string state (unsigned nid, unsigned sid)
    {
      return std::to_string(nid) + " state " + std::to_string(sid) + eol;
    }

  inline std::string init (
                           unsigned nid,
                           unsigned sid,
                           unsigned state,
                           unsigned val
                          )
    {
      return
        std::to_string(nid) +
        " init " +
        std::to_string(sid) +
        " " +
        std::to_string(state) +
        " " +
        std::to_string(val) +
        eol;
    }

  inline std::string next (
                           unsigned nid,
                           unsigned sid,
                           unsigned state,
                           unsigned val
                          )
    {
      return
        std::to_string(nid) +
        " next " +
        std::to_string(sid) +
        " " +
        std::to_string(state) +
        " " +
        std::to_string(val) +
        eol;
    }

  inline std::string constraint (unsigned nid, unsigned node)
    {
      return std::to_string(nid) + " constraint " + std::to_string(node) + eol;
    }

  inline std::string bad (unsigned nid, unsigned node)
    {
      return std::to_string(nid) + " bad " + std::to_string(node) + eol;
    }

  inline std::string fair (unsigned nid, unsigned node)
    {
      return std::to_string(nid) + " fair " + std::to_string(node) + eol;
    }

  inline std::string output (unsigned nid, unsigned node)
    {
      return std::to_string(nid) + " output " + std::to_string(node) + eol;
    }

  inline std::string justice (
                              unsigned nid,
                              unsigned num,
                              std::vector<unsigned> conditions
                             )
    {
      std::ostringstream ss;

      ss << nid << " justice " << num << " ";

      std::copy(
        conditions.begin(),
        conditions.end() - 1,
        std::ostream_iterator<unsigned>(ss, " "));

      ss << conditions.back() << eol;

      return ss.str();
    }

  inline std::string sext (unsigned nid, unsigned sid, unsigned width)
    {
      return
        std::to_string(nid) +
        " sext " +
        std::to_string(sid) +
        " " +
        std::to_string(width) +
        eol;
    }

  inline std::string uext (unsigned nid, unsigned sid, unsigned width)
    {
      return
        std::to_string(nid) +
        " uext " +
        std::to_string(sid) +
        " " +
        std::to_string(width) +
        eol;
    }

  inline std::string slice (
                            unsigned nid,
                            unsigned sid,
                            unsigned upper,
                            unsigned lower
                           )
    {
      return
        std::to_string(nid) +
        " slice " +
        std::to_string(sid) +
        " " +
        std::to_string(upper) +
        " " +
        std::to_string(lower) +
        eol;
    }

  inline std::string lnot (unsigned nid, unsigned sid, unsigned node)
    {
      return
        std::to_string(nid) +
        " not " +
        std::to_string(sid) +
        " " +
        std::to_string(node) +
        eol;
    }
}
#endif
