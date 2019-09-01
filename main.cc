#include <cstring>

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
  " <command> [<arg> ...]" <<
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
  " simulate [-k <bound>] [-s <seed>] [-v] <program> ..." <<
  eol << eol <<
  "  -k bound   execute a maximum of <bound> steps" << eol <<
  "  -s seed    random number generator's seed" << eol <<
  "  -v         verbose trace output" << eol <<
  "  program    one ore more source files, each being executed as a separate thread" << eol;
}

void print_usage_replay (const char * name)
{
  std::cout << "usage: " << name <<
  " replay [-k <bound>] [-v] <trace>" <<
  eol << eol <<
  "  -k bound   execute a maximum of <bound> steps" << eol <<
  "  -v         verbose trace output" << eol <<
  "  trace      the trace to replay" << eol;
}

void print_usage_solve (const char * name)
{
  std::cout << "usage: " << name <<
  " solve [options] <bound> <program> ..."
  << eol << eol <<
  "options:" << eol <<
  "  -c file    include additional constraints from file" << eol <<
  "  -e encoder use a specific encoding, options are:" << eol <<
  "             * smtlib-functional (default)" << eol <<
  "             * smtlib-relational" << eol <<
  "             * btor2 (implies -s boolector)" << eol <<
  "  -p         prints the generated formula and exits" << eol <<
  "  -s solver  use a specific solver, options are:" << eol <<
  "             * boolector (default)" << eol <<
  "             * z3" << eol <<
  "  -v         verbose formula output" << eol <<
  "  bound      execute a specific number of steps" << eol <<
  "  program    one or more programs to encode" << eol;
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
  Program::List::ptr programs = std::make_shared<Program::List>();

  for (int i = 0; i < argc; i++)
    {
      std::string arg(argv[i]);

      if (arg == "-v")
        {
          verbose = true;
        }
      else if (arg == "-s")
        {
          try
            {
              if (++i < argc)
                seed = stoul((arg = argv[i]), nullptr, 0);
              else
                {
                  print_error("missing seed");
                  return -1;
                }
            }
          catch (...)
            {
              print_error("illegal seed [" + arg + "]");
              return -1;
            }
        }
      else if (arg == "-k")
        {
          try
            {
              if (++i < argc)
                bound = stoul((arg = argv[i]), nullptr, 0);
              else
                {
                  print_error("missing bound");
                  return -1;
                }
            }
          catch (...)
            {
              print_error("illegal bound [" + arg + "]");
              return -1;
            }
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
  // TODO: MMap
  Trace::ptr trace = Simulator().simulate(programs, {}, bound);

  // print the result
  std::cout << trace->print();

  return trace->exit;
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
      std::string arg(argv[i]);

      if (arg == "-v")
        {
          verbose = true;
        }
      else if (arg == "-k")
        {
          try
            {
              if (++i < argc)
                bound = stoul((arg = argv[i]), nullptr, 0);
              else
                {
                  print_error("missing bound");
                  return -1;
                }
            }
          catch (...)
            {
              print_error("illegal bound [" + arg + "]");
              return -1;
            }
        }
      else
        {
          trace_path = arg;
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
      Trace::ptr trace =
        std::make_unique<Trace>(create_from_file<Trace>(trace_path));

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
      int i = 0;

      // only print formula
      bool pretend = false;

      // additional constraints from file
      std::string constraints;

      // encoder name
      std::string encoder_name = "smtlib-functional";

      // solver name
      std::string solver_name = "boolector";

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

            std::ifstream ifs(argv[i]);
            constraints.assign(
              std::istreambuf_iterator<char>(ifs),
              std::istreambuf_iterator<char>());

            if (constraints.empty())
              throw std::runtime_error(std::string(argv[i]) + " not found");
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
      if (argc < i + 2)
        {
          print_error("too few arguments");
          print_usage_solve(name);
          return -1;
        }

      // parse bound
      size_t bound = 0;
      try
        {
          bound = std::stoul(argv[i++], nullptr, 0);

          if (bound < 1) throw std::runtime_error("");
        }
      catch (...)
        {
          print_error("illegal bound [" + std::string(argv[i - 1]) + "]");
          return -1;
        }

      // list of programs (thread id == idx + 1)
      Program::List::ptr programs = std::make_shared<Program::List>();

      // parse programs
      while (i < argc)
        programs->push_back(create_from_file<Program>(argv[i++]));

      // memory map
      std::shared_ptr<MMap> mmap;

      // encode program
      std::unique_ptr<Encoder> encoder;

      if (encoder_name == "smtlib-functional")
        encoder = std::make_unique<smtlib::Functional>(programs, mmap, bound);
      else if (encoder_name == "smtlib-relational")
        encoder = std::make_unique<smtlib::Relational>(programs, mmap, bound);
      else if (encoder_name == "btor2")
        encoder = std::make_unique<btor2::Encoder>(programs, mmap, bound);
      else
        {
          print_error("unknown encoder [" + encoder_name + "]");
          print_usage_solve(name);
          return -1;
        }

      encoder->encode();

      // append constraints from file
      if (!constraints.empty())
        encoder->formula << constraints;

      // select solver
      std::unique_ptr<Solver> solver;

      if (encoder_name == "btor2")
        solver = std::make_unique<BtorMC>();
      else if (solver_name == "boolector")
        solver = std::make_unique<Boolector>();
      else if (solver_name == "z3")
        solver = std::make_unique<Z3>();
      else if (solver_name == "cvc4")
        solver = std::make_unique<CVC4>();
      else
        {
          print_error("unknown solver [" + solver_name + "]");
          print_usage_solve(name);
          return -1;
        }

      // print formula if we're pretending
      if (pretend)
        std::cout << solver->formula(*encoder);
      else
        std::cout << solver->solve(*encoder)->print();
    }
  catch (const std::exception & e)
    {
      print_error(e.what());
      return -1;
    }

  return 0;
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
