#include <cstring>

#include "btor2.hh"
#include "smtlib.hh"

#include "mmap.hh"
#include "parser.hh"

#include "encoder.hh"
#include "simulator.hh"

#include "boolector.hh"
#include "btormc.hh"
#include "z3.hh"
#include "cvc4.hh"

namespace ConcuBinE {

//==============================================================================
// global variables
//==============================================================================

bool verbose = false;
uint64_t seed = static_cast<uint64_t>(time(NULL));

//==============================================================================
// usage
//==============================================================================

void print_usage_main (const char * name)
{
  std::cout << "usage: " << name <<
  " <command> [options]" <<
  eol << eol <<
  "available commands:" << eol <<
  "  help       print help for a specific <command>" << eol <<
  "  simulate   simulate concurrent programs" << eol <<
  "  replay     reevaluates a given trace" << eol <<
  "  solve      solve concurrent programs using SMT" << eol;
}

void print_usage_help (const char * name)
{
  std::cout << "usage: " << name << " help <command>" << eol;
}

void print_usage_simulate (const char * name)
{
  std::cout << "usage: " << name <<
  " simulate [options] <program> ..." <<
  eol << eol <<
  "options:" << eol <<
  "  -k bound   execute a specific number of steps" << eol <<
  "  -m mmap    read initial heap contents from file" << eol <<
  "  -o name    output file name (default: sim.{trace,mmap})" << eol <<
  "  -s seed    random number generator's seed" << eol <<
  "  program    one ore more source files, each being executed as a separate thread" << eol;
}

void print_usage_solve (const char * name)
{
  std::cout << "usage: " << name <<
  " solve [options] <bound> <program> ..."
  << eol << eol <<
  "options:" << eol <<
  "  -c file    read constraints from file" << eol <<
  "  -e encoder use a specific encoding, options are:" << eol <<
  "             * btor2 (default)" << eol <<
  "             * smtlib-functional" << eol <<
  "             * smtlib-relational" << eol <<
  "  -m mmap    read initial heap contents from file" << eol <<
  "  -o name    output file name (default: smt.{trace,mmap})" << eol <<
  "  -p         prints the generated formula and exits" << eol <<
  "  -s solver  use a specific solver, options are:" << eol <<
  "             * btormc (default)" << eol <<
  "             * boolector" << eol <<
  "             * cvc4" << eol <<
  "             * z3" << eol <<
  "  -v         verbose formula output" << eol <<
  "  bound      execute a specific number of steps" << eol <<
  "  program    one or more programs to encode" << eol;
}

void print_usage_replay (const char * name)
{
  std::cout << "usage: " << name << " replay <trace>" << eol;
}

//==============================================================================
// submodules
//==============================================================================

void write (Trace & trace, const std::string & path)
{
  // write mmap
  if (trace.mmap)
    {
      trace.mmap->path = path + ".mmap";
      std::ofstream mmap_ofs(trace.mmap->path);
      mmap_ofs << trace.mmap->print();
    }

  // write trace
  std::ofstream trace_ofs(path + ".trace");
  trace_ofs << trace.print();
}

void print_error (const std::string & m) { std::cerr << "error: " << m << eol; }

//------------------------------------------------------------------------------
// help
//------------------------------------------------------------------------------

int help (const char * name, const int argc, const char **argv)
{
  if (argc < 1)
    {
      print_error("no command given");
      print_usage_help(name);
      return -1;
    }

  if (!strcmp(argv[0], "help"))
    print_usage_help(name);
  else if (!strcmp(argv[0], "simulate"))
    print_usage_simulate(name);
  else if (!strcmp(argv[0], "replay"))
    print_usage_replay(name);
  else if (!strcmp(argv[0], "solve"))
    print_usage_solve(name);
  else
    {
      print_error("unknown command " + std::string(argv[0]));
      print_usage_help(name);
      return -1;
    }

  return 0;
}

//------------------------------------------------------------------------------
// simulate
//------------------------------------------------------------------------------

int simulate (const char * name, const int argc, const char ** argv)
{
  if (argc < 1)
    {
      print_error("too few arguments");
      print_usage_solve(name);
      return -1;
    }

  try
    {
      // bound
      size_t bound = 0;

      // memory map
      std::shared_ptr<MMap> mmap;

      // output file name
      std::string outfile = "sim";

      // parse options
      int i = 0;
      do
        {
          if (!strcmp(argv[i], "-k"))
            {
              if (++i >= argc)
                {
                  print_error("missing bound");
                  print_usage_simulate(name);
                  return -1;
                }

              try { bound = std::stoul(argv[i], nullptr, 0); }
              catch (...)
                {
                  print_error("illegal bound [" + std::string(argv[i]) + "]");
                  return -1;
                }
            }
          else if (!strcmp(argv[i], "-m"))
            {
              if (++i >= argc)
                {
                  print_error("missing path to memory map");
                  print_usage_simulate(name);
                  return -1;
                }

              mmap = std::make_shared<MMap>(create_from_file<MMap>(argv[i]));
            }
          else if (!strcmp(argv[i], "-o"))
            {
              if (++i >= argc)
                {
                  print_error("missing output file name");
                  print_usage_simulate(name);
                  return -1;
                }

              outfile = argv[i];
            }
          else if (!strcmp(argv[i], "-s"))
            {
              if (++i >= argc)
                {
                  print_error("missing seed");
                  print_usage_simulate(name);
                  return -1;
                }

              try { seed = std::stoul(argv[i], nullptr, 0); }
              catch (...)
                {
                  print_error("illegal seed [" + std::string(argv[i]) + "]");
                  return -1;
                }
            }
          else if (argv[i][0] == '-')
            {
              print_error("unknown option [" + std::string(argv[i]) + "]");
              print_usage_simulate(name);
              return -1;
            }
          else
            break;
        }
      while (++i < argc);

      // check programs
      if (i >= argc)
        {
          print_error("missing programs");
          print_usage_simulate(name);
          return -1;
        }

      // program list
      auto programs = std::make_shared<Program::List>();

      // parse programs
      while (i < argc)
        programs->push_back(create_from_file<Program>(argv[i++]));

      // simulate
      auto trace = Simulator().simulate(programs, mmap, bound);
      write(*trace, outfile);
      return trace->exit;
    }
  catch (const std::exception & e)
    {
      print_error(e.what());
      return -1;
    }
}

//------------------------------------------------------------------------------
// solve
//------------------------------------------------------------------------------

int solve (const char * name, const int argc, const char ** argv)
{
  if (argc < 2)
    {
      print_error("too few arguments");
      print_usage_solve(name);
      return -1;
    }

  try
    {
      // only print formula
      bool pretend = false;

      // constraints file path
      std::string constraints;

      // memory map
      std::shared_ptr<MMap> mmap;

      // encoder type
      enum
        {
          btor2,
          smtlib_functional,
          smtlib_relational
        }
      encoder_type = btor2;

      const char * encoder_names[] = {
        "btor2",
        "smtlib-functional",
        "smtlib-relational"
      };

      // solver type
      enum
        {
          btormc,
          boolector,
          cvc4,
          z3
        }
      solver_type = btormc;

      const char * solver_names[] = {
        "btormc",
        "boolector",
        "cvc4",
        "z3"
      };

      // output file name
      std::string outfile = "smt";

      // parse options
      int i = 0;
      do
        if (!strcmp(argv[i], "-c"))
          {
            if (++i >= argc)
              {
                print_error("missing constraints file");
                print_usage_solve(name);
                return -1;
              }

            constraints = argv[i];
          }
        else if (!strcmp(argv[i], "-e"))
          {
            if (++i >= argc)
              {
                print_error("missing encoder");
                print_usage_solve(name);
                return -1;
              }

            if (!strcmp(argv[i], encoder_names[btor2]))
              encoder_type = btor2;
            else if (!strcmp(argv[i], encoder_names[smtlib_functional]))
              encoder_type = smtlib_functional;
            else if (!strcmp(argv[i], encoder_names[smtlib_relational]))
              encoder_type = smtlib_relational;
            else
              {
                print_error("unknown encoder [" + std::string(argv[i]) + "]");
                print_usage_solve(name);
                return -1;
              }
          }
        else if (!strcmp(argv[i], "-m"))
          {
            if (++i >= argc)
              {
                print_error("missing path to memory map");
                print_usage_solve(name);
                return -1;
              }

            mmap = std::make_shared<MMap>(create_from_file<MMap>(argv[i]));
          }
        else if (!strcmp(argv[i], "-o"))
          {
            if (++i >= argc)
              {
                print_error("missing output file name");
                print_usage_solve(name);
                return -1;
              }

            outfile = argv[i];
          }
        else if (!strcmp(argv[i], "-p"))
          {
            pretend = true;
          }
        else if (!strcmp(argv[i], "-s"))
          {
            if (++i >= argc)
              {
                print_error("missing solver");
                print_usage_solve(name);
                return -1;
              }

            if (!strcmp(argv[i], solver_names[btormc]))
              solver_type = btormc;
            else if (!strcmp(argv[i], solver_names[boolector]))
              solver_type = boolector;
            else if (!strcmp(argv[i], solver_names[cvc4]))
              solver_type = cvc4;
            else if (!strcmp(argv[i], solver_names[z3]))
              solver_type = z3;
            else
              {
                print_error("unknown solver [" + std::string(argv[i]) + "]");
                print_usage_solve(name);
                return -1;
              }
          }
        else if (!strcmp(argv[i], "-v"))
          {
            verbose = true;
          }
        else if (argv[i][0] == '-')
          {
            print_error("unknown option [" + std::string(argv[i]) + "]");
            print_usage_solve(name);
            return -1;
          }
        else
          break;
      while (++i < argc);

      // check bound
      if (i >= argc)
        {
          print_error("missing bound");
          print_usage_solve(name);
          return -1;
        }

      // parse bound
      size_t bound = 0;
      try
        {
          bound = std::stoul(argv[i++], nullptr, 0);

          if (!bound) throw std::runtime_error("");
        }
      catch (...)
        {
          print_error("illegal bound [" + std::string(argv[i - 1]) + "]");
          return -1;
        }

      // check programs
      if (i >= argc)
        {
          print_error("missing programs");
          print_usage_solve(name);
          return -1;
        }

      // list of programs
      auto programs = std::make_shared<Program::List>();

      // parse programs
      while (i < argc)
        programs->push_back(create_from_file<Program>(argv[i++]));

      // encode programs
      std::unique_ptr<Encoder> encoder;

      if (encoder_type == btor2)
        encoder = std::make_unique<btor2::Encoder>(programs, mmap, bound);
      else if (encoder_type == smtlib_functional)
        encoder = std::make_unique<smtlib::Functional>(programs, mmap, bound);
      else if (encoder_type == smtlib_relational)
        encoder = std::make_unique<smtlib::Relational>(programs, mmap, bound);

      encoder->encode();

      // append constraints
      if (!constraints.empty())
        {
          std::ifstream ifs(constraints);

          if (!ifs.is_open())
            {
              print_error(constraints + " not found");
              return -1;
            }

          encoder->formula << ifs.rdbuf();
        }
      else if (encoder_type == btor2)
        {
          auto & e = dynamic_cast<btor2::Encoder &>(*encoder);
          encoder->formula <<
            btor2::ne(
              e.nid(),
              e.sid_bool,
              e.nids_const[0],
              e.nid_exit_code) <<
            btor2::bad(e.node);
        }
      else
        {
          encoder->formula <<
            smtlib::assertion(
              smtlib::lnot(
                smtlib::equality({
                  smtlib::Encoder::exit_code_var,
                  smtlib::word2hex(0)})));
        }

      // select solver
      std::unique_ptr<Solver> solver;

      if (solver_type == btormc)
        solver = std::make_unique<BtorMC>();
      else if (solver_type == boolector)
        solver = std::make_unique<Boolector>();
      else if (solver_type == cvc4)
        solver = std::make_unique<CVC4>();
      else if (solver_type == z3)
        solver = std::make_unique<Z3>();

      // check compatibility
      if ((encoder_type == btor2 && solver_type != btormc) ||
          (encoder_type != btor2 && solver_type == btormc))
        {
          print_error(
            '[' +
            std::string(solver_names[solver_type]) +
            "] cannot be used with encoder [" +
            std::string(encoder_names[encoder_type]) +
            ']');
          return -1;
        }

      // solve
      if (pretend)
        {
          std::cout << solver->formula(*encoder);
          return 0;
        }
      else
        {
          auto trace = solver->solve(*encoder);
          write(*trace, outfile);
          return trace->exit;
        }
    }
  catch (const std::exception & e)
    {
      print_error(e.what());
      return -1;
    }
}

//------------------------------------------------------------------------------
// replay
//------------------------------------------------------------------------------

int replay (const char * name, const int argc, const char ** argv)
{
  if (!argc)
    {
      print_error("missing trace file");
      print_usage_replay(name);
      return -1;
    }

  try
    {
      // parse
      auto t1 = std::make_unique<Trace>(create_from_file<Trace>(argv[0]));

      // replay
      auto t2 = Simulator().replay(*t1);

      // compare
      if (t1->size() != t2->size())
        {
          std::cout
            << "size differs: "
            << std::to_string(t1->size())
            << " vs. "
            << std::to_string(t2->size())
            << eol;
          return 1;
        }
      else
        {
          auto it1 = t1->begin();
          auto it2 = t2->begin();

          for (; it1 != t1->end(); ++it1, ++it2)
            if (*it1 != *it2)
              {
                std::cout << "< " << t1->print(*it1) << "> " << t2->print(*it2);
                return *it1;
              }
        }

      return 0;
    }
  catch (const std::exception & e)
    {
      print_error(e.what());
      return -1;
    }
}

} // namespace ConcuBinE

//==============================================================================
// main
//==============================================================================

int main (const int argc, const char ** argv)
{
  if (argc > 1)
    {
      if (!strcmp(argv[1], "help"))
        return ConcuBinE::help(argv[0], argc - 2, argv + 2);
      else if (!strcmp(argv[1], "simulate"))
        return ConcuBinE::simulate(argv[0], argc - 2, argv + 2);
      else if (!strcmp(argv[1], "replay"))
        return ConcuBinE::replay(argv[0], argc - 2, argv + 2);
      else if (!strcmp(argv[1], "solve"))
        return ConcuBinE::solve(argv[0], argc - 2, argv + 2);
    }

  ConcuBinE::print_usage_main(argv[0]);
  return -1;
}
