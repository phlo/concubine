#include <cstring>

#include "parser.hh"

#include "btor2.hh"
#include "smtlib.hh"

#include "mmap.hh"

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
  std::cout << "usage: " << name <<
  " replay [-k <bound>] <trace>" <<
  eol << eol <<
  "  -k bound   execute a specific number of steps" << eol <<
  "  trace      the trace to replay" << eol;
}

//==============================================================================
// submodules
//==============================================================================

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
    {
      print_usage_help(name);
    }
  else if (!strcmp(argv[0], "simulate"))
    {
      print_usage_simulate(name);
    }
  else if (!strcmp(argv[0], "replay"))
    {
      print_usage_replay(name);
    }
  else if (!strcmp(argv[0], "solve"))
    {
      print_usage_solve(name);
    }
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
  size_t bound = 0;
  std::shared_ptr<MMap> mmap;
  std::string outname = "sim";
  Program::List::ptr programs = std::make_shared<Program::List>();

  for (int i = 0; i < argc; i++)
    {
      std::string arg(argv[i]);

      if (!strcmp(argv[i], "-k"))
        {
          try
            {
              if (++i >= argc)
                {
                  print_error("missing bound");
                  return -1;
                }

              bound = stoul((arg = argv[i]), nullptr, 0);
            }
          catch (...)
            {
              print_error("illegal bound [" + arg + "]");
              return -1;
            }
        }
      else if (!strcmp(argv[i], "-m"))
        {
          if (++i >= argc)
            {
              print_error("missing path to memory map");
              return -1;
            }

          try
            {
              mmap = std::make_shared<MMap>(create_from_file<MMap>(argv[i]));
            }
          catch (const std::exception & e)
            {
              print_error(e.what());
              return -1;
            }
        }
      else if (!strcmp(argv[i], "-o"))
        {
          if (++i >= argc)
            {
              print_error("missing output file name");
              return -1;
            }

          outname = argv[i];
        }
      else if (!strcmp(argv[i], "-s"))
        {
          try
            {
              if (++i >= argc)
                {
                  print_error("missing seed");
                  return -1;
                }

              seed = stoul((arg = argv[i]), nullptr, 0);
            }
          catch (...)
            {
              print_error("illegal seed [" + arg + "]");
              return -1;
            }
        }
      else if (argv[i][0] == '-')
        {
          print_error("unknown option [" + std::string(argv[i]) + "]");
          print_usage_solve(name);
          return -1;
        }
      else
        {
          try
            {
              programs->push_back(create_from_file<Program>(arg));
            }
          catch (const std::exception & e)
            {
              print_error(e.what());
              return -1;
            }
        }
    }

  if (programs->empty())
    {
      print_error("got nothing to run");
      print_usage_simulate(name);
      return -1;
    }

  // run program with given seed
  auto trace = Simulator().simulate(programs, mmap, bound);

  // write mmap
  if (trace->mmap)
    {
      trace->mmap->path = outname + ".mmap";
      std::ofstream mmap_ofs(trace->mmap->path);
      mmap_ofs << trace->mmap->print();
    }

  // write trace
  std::ofstream trace_ofs(outname + ".trace");
  trace_ofs << trace->print();

  return trace->exit;
}

//------------------------------------------------------------------------------
// solve
//------------------------------------------------------------------------------

int solve (const char * name, const int argc, const char ** argv)
{
  static const std::string encoder_btor2 = "btor2";
  static const std::string encoder_smtlib_functional = "smtlib-functional";
  static const std::string encoder_smtlib_relational = "smtlib-relational";

  static const std::string solver_btormc = "btormc";
  static const std::string solver_boolector = "boolector";
  static const std::string solver_cvc4 = "cvc4";
  static const std::string solver_z3 = "z3";

  if (argc < 2)
    {
      print_error("too few arguments");
      print_usage_solve(name);
      return -1;
    }

  try
    {
      int i = 0;

      // only print formula
      bool pretend = false;

      // additional constraints from file
      std::string constraints;

      // memory map
      std::shared_ptr<MMap> mmap;

      // encoder name
      std::string encoder_name = encoder_btor2;

      // solver name
      std::string solver_name = solver_btormc;

      // output file name
      std::string outname = "smt";

      // parse flags
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

            encoder_name = argv[i];
          }
        else if (!strcmp(argv[i], "-m"))
          {
            if (++i >= argc)
              {
                print_error("missing memory map");
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

            outname = argv[i];
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

            solver_name = argv[i];
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

      // check for bound and program
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

      // list of programs
      Program::List::ptr programs = std::make_shared<Program::List>();

      // parse programs
      while (i < argc)
        programs->push_back(create_from_file<Program>(argv[i++]));

      if (programs->empty())
        {
          print_error("missing programs");
          print_usage_solve(name);
          return -1;
        }

      // encode program
      std::unique_ptr<Encoder> encoder;

      if (encoder_name == encoder_btor2)
        encoder = std::make_unique<btor2::Encoder>(programs, mmap, bound);
      else if (encoder_name == encoder_smtlib_functional)
        encoder = std::make_unique<smtlib::Functional>(programs, mmap, bound);
      else if (encoder_name == encoder_smtlib_relational)
        encoder = std::make_unique<smtlib::Relational>(programs, mmap, bound);
      else
        {
          print_error("unknown encoder [" + encoder_name + "]");
          print_usage_solve(name);
          return -1;
        }

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
      else if (encoder_name == encoder_btor2)
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

      if (encoder_name == encoder_btor2)
        solver = std::make_unique<BtorMC>();
      else if (solver_name == solver_boolector)
        solver = std::make_unique<Boolector>();
      else if (solver_name == solver_cvc4)
        solver = std::make_unique<CVC4>();
      else if (solver_name == solver_z3)
        solver = std::make_unique<Z3>();
      else
        {
          print_error("unknown solver [" + solver_name + "]");
          print_usage_solve(name);
          return -1;
        }

      if (pretend)
        {
          std::cout << solver->formula(*encoder);
        }
      else
        {
          auto trace = solver->solve(*encoder);

          // write mmap
          if (trace->mmap)
            {
              trace->mmap->path = outname + ".mmap";
              std::ofstream mmap_ofs(trace->mmap->path);
              mmap_ofs << trace->mmap->print();
            }

          // write trace
          std::ofstream trace_ofs(outname + ".trace");
          trace_ofs << trace->print();
        }
    }
  catch (const std::exception & e)
    {
      print_error(e.what());
      return -1;
    }

  return 0;
}

//------------------------------------------------------------------------------
// replay
//------------------------------------------------------------------------------

int replay (const char * name, const int argc, const char ** argv)
{
  size_t bound = 0;
  std::string trace_path;

  for (int i = 0; i < argc; i++)
    {
      if (!strcmp(argv[i], "-k"))
        {
          try
            {
              if (++i < argc)
                bound = std::stoul(argv[i], nullptr, 0);
              else
                {
                  print_error("missing bound");
                  return -1;
                }
            }
          catch (...)
            {
              print_error("illegal bound [" + std::string(argv[i]) + "]");
              return -1;
            }
        }
      else
        {
          trace_path = argv[i];
        }
    }

  if (trace_path.empty())
    {
      print_error("no trace given");
      print_usage_replay(name);
      return -1;
    }

  try
    {
      // create and parse trace
      auto trace = std::make_unique<Trace>(create_from_file<Trace>(trace_path));

      // run given trace
      trace = Simulator().replay(*trace, bound);

      // print the result
      std::cout << trace->print();

      return trace->exit;
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
      // forward to given command's main
      if (!strcmp(argv[1], "help"))
        {
          return ConcuBinE::help(argv[0], argc - 2, argv + 2);
        }
      else if (!strcmp(argv[1], "simulate"))
        {
          return ConcuBinE::simulate(argv[0], argc - 2, argv + 2);
        }
      else if (!strcmp(argv[1], "replay"))
        {
          return ConcuBinE::replay(argv[0], argc - 2, argv + 2);
        }
      else if (!strcmp(argv[1], "solve"))
        {
          return ConcuBinE::solve(argv[0], argc - 2, argv + 2);
        }
    }

  // found no command
  ConcuBinE::print_usage_main(argv[0]);
  return -1;
}
