/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#include "shell.hh"

#include <cstring>
#include <unistd.h>
#include <sys/wait.h>

namespace ConcuBinE::shell {

//==============================================================================
// constants
//==============================================================================

#define READ 0
#define WRITE 1

//==============================================================================
// functions
//==============================================================================

// errmsg ----------------------------------------------------------------------

inline std::string errmsg (const std::string & msg)
{
  return "error " + msg + " [" + strerror(errno) + ']';
}

// run -------------------------------------------------------------------------

Output run (const std::vector<std::string> & command, const std::string & input)
{
  shell::Output output;

  // stdin pipe
  int std_in[2];

  // stdout pipe
  int std_out[2];

  // stderr pipe
  int std_err[2];

  // exec error pipe
  int exec_err[2];

  // pid returned by fork (0 == child)
  int pid;

  // open stdin pipe
  if (pipe(std_in))
    throw std::runtime_error(errmsg("creating stdin pipe"));

  // open stdout pipe
  if (pipe(std_out))
    throw std::runtime_error(errmsg("creating stdout pipe"));

  // open stderr pipe
  if (pipe(std_err))
    throw std::runtime_error(errmsg("creating stderr pipe"));

  // open error pipe
  if (pipe(exec_err))
    throw std::runtime_error(errmsg("creating error pipe"));

  // fork process
  pid = fork();

  // child process
  if (pid == 0)
    {
      // redirect stdin
      if (dup2(std_in[READ], STDIN_FILENO) < 0)
        throw std::runtime_error(errmsg("redirecting stdin"));

      // redirect stdout
      if (dup2(std_out[WRITE], STDOUT_FILENO) < 0)
        throw std::runtime_error(errmsg("redirecting stdout"));

      // redirect stderr
      if (dup2(std_err[WRITE], STDERR_FILENO) < 0)
        throw std::runtime_error(errmsg("redirecting stderr"));

      // close file descriptors - only used by parent
      close(std_in[READ]);
      close(std_in[WRITE]);
      close(std_out[READ]);
      close(std_out[WRITE]);
      close(std_err[READ]);
      close(std_err[WRITE]);
      close(exec_err[READ]);

      // build arguments vector
      std::vector<char *> argv;
      argv.reserve(command.size() + 1);
      for (const auto & a : command)
        argv.push_back(const_cast<char *>(a.c_str()));
      argv.push_back(nullptr);

      // run executable
      execvp(argv[0], argv.data());

      // exec should not return - if we get here, something must have happened
      const int ret = errno;
      const std::string msg = errmsg("calling exec");

      // write reason to error pipe
      write(exec_err[WRITE], msg.c_str(), msg.length());

      // close remaining file descriptor
      close(exec_err[WRITE]);

      exit(ret);
    }
  // parent process
  else if (pid > 0)
    {
      // close unused file descriptors
      close(std_in[READ]);
      close(std_out[WRITE]);
      close(std_err[WRITE]);
      close(exec_err[WRITE]);

      // ignore SIGPIPE raised by parser errors
      signal(SIGPIPE, SIG_IGN);

      // write given input to stdin of child
      if (!input.empty())
        if (write(std_in[WRITE], input.c_str(), input.length()) < 0)
          throw std::runtime_error(errmsg("writing to stdin pipe"));

      // restore default SIGPIPE handler
      signal(SIGPIPE, SIG_DFL);

      // close stdin pipe file descriptor
      close(std_in[WRITE]);

      // read buffer
      constexpr size_t nbuf = 128;
      constexpr size_t nbyte = nbuf - 1;
      char buf[nbuf];
      int n;

      // read stdout pipe
      while ((n = read(std_out[READ], buf, nbyte)) > 0)
        {
          buf[n] = 0;
          output.stdout << buf;
        }

      // read stderr pipe
      while ((n = read(std_err[READ], buf, nbyte)) > 0)
        {
          buf[n] = 0;
          output.stderr << buf;
        }

      // read error pipe
      std::string error;
      while ((n = read(exec_err[READ], buf, nbyte)) > 0)
        {
          buf[n] = 0;
          error += buf;
        }

      // close remaining file descriptors
      close(std_out[READ]);
      close(std_err[READ]);
      close(exec_err[READ]);

      // wait for child to finish and assign exit code
      int wstatus;

      waitpid(pid, &wstatus, 0);

      if (WIFEXITED(wstatus))
        output.exit = WEXITSTATUS(wstatus);
      else
        throw std::runtime_error(errmsg("child process exited prematurely"));

      // check for exec errors
      if (!error.empty())
        throw std::runtime_error(error);
    }
  // fork failed
  else
    {
      // close file descriptors
      close(std_in[READ]);
      close(std_in[WRITE]);
      close(std_out[READ]);
      close(std_out[WRITE]);
      close(std_err[READ]);
      close(std_err[WRITE]);
      close(exec_err[READ]);
      close(exec_err[WRITE]);

      throw std::runtime_error(errmsg("fork failed"));
    }

  return output;
}

} // namespace ConcuBinE::shell
