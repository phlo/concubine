#include "shell.hh"

#include <cstdio>
#include <cerrno>
#include <cstring>
#include <stdexcept>

#include <unistd.h>
#include <sys/wait.h>

#define PIPE_READ 0
#define PIPE_WRITE 1
#define BUFFER_SIZE 128

/* sysError (void) - custom strerror wrapper **********************************/
inline string sysError () { return "[" + string(strerror(errno)) + "]"; }

/* Shell::lastExitCode (void) *************************************************/
int Shell::lastExitCode () { return exitCode; }

/* Shell::run (string) ********************************************************/
string Shell::run (string cmd)
{
  string input = "";

  return run(cmd, input);
}

/* Shell::run (string, string &) **********************************************/
string Shell::run (string cmd, string & input)
{
  /* stdout read from cmd */
  string output = "";

  /* stdin pipe file descriptors */
  int stdIn[2];

  /* stdout pipe file descriptors */
  int stdOut[2];
  
  /* pid returned by fork (0 == child) */
  int pid;

  /* open stdin pipe */
  if (pipe(stdIn) < 0)
    throw runtime_error("creating input pipe " + sysError());

  /* open stdout pipe */
  if (pipe(stdOut) < 0)
    throw runtime_error("creating output pipe " + sysError());

  /* fork process */
  pid = fork();

  /* child process */
  if (pid == 0)
    {
      /* redirect stdin */
      if (dup2(stdIn[PIPE_READ], STDIN_FILENO) < 0)
        throw runtime_error("redirecting stdin " + sysError());

      /* redirect stdout */
      if (dup2(stdOut[PIPE_WRITE], STDOUT_FILENO) < 0)
        throw runtime_error("redirecting stdout " + sysError());

      /* redirect stderr */
      if (dup2(stdOut[PIPE_WRITE], STDERR_FILENO) < 0)
        throw runtime_error("redirecting stderr " + sysError());

      /* close file descriptors - only used by parent */
      close(stdIn[PIPE_READ]);
      close(stdIn[PIPE_WRITE]);
      close(stdOut[PIPE_READ]);
      close(stdOut[PIPE_WRITE]);

      /* run shell command as child process */
      execlp("bash", "bash", "-c", cmd.c_str(), static_cast<char *>(0));
      
      /* exec should not return - if we get here, an error must have happened */
      throw runtime_error("executing shell command " + sysError());
    }
  /* parent process */
  else if (pid > 0)
    {
      /* read buffer */
      char buffer[BUFFER_SIZE];

      /* close unused file descriptors */
      close(stdIn[PIPE_READ]);
      close(stdOut[PIPE_WRITE]);

      /* write given input to stdin of child */
      if (!input.empty())
        if (write(stdIn[PIPE_WRITE], input.c_str(), input.length()) < 0)
          throw runtime_error("writing to stdin " + sysError());

      /* close stdin pipe file descriptor */
      close(stdIn[PIPE_WRITE]);

      /* read stdout from child */
      int numRead = 0;
      while ((numRead = read(stdOut[PIPE_READ], buffer, BUFFER_SIZE - 1)) > 0)
        {
          buffer[numRead] = '\0';
          output += buffer;
        }

      /* close remaining file descriptors */
      close(stdOut[PIPE_READ]);

      /* wait for child to finish and assign exit code */
      int wstatus;

      waitpid(pid, &wstatus, 0);

      if (WIFEXITED(wstatus))
        exitCode = WEXITSTATUS(wstatus);
      else
        throw runtime_error("child process exited prematurely " + sysError());
    }
  /* fork failed */
  else
    {
      /* close file descriptors */
      close(stdIn[PIPE_READ]);
      close(stdIn[PIPE_WRITE]);
      close(stdOut[PIPE_READ]);
      close(stdOut[PIPE_WRITE]);

      throw runtime_error("fork failed " + sysError());
    }

  return output;
}
