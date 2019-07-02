#include "shell.hh"

#include <cstring>
#include <unistd.h>
#include <sys/wait.h>

//==============================================================================
// constants
//==============================================================================

#define PIPE_READ 0
#define PIPE_WRITE 1

#define BUFFER_SIZE 128

//==============================================================================
// functions
//==============================================================================

// sys_error -------------------------------------------------------------------

inline std::string sys_error ()
{
  return "[" + std::string(strerror(errno)) + "]";
}

//==============================================================================
// Shell
//==============================================================================

// Shell::last_exit_code -------------------------------------------------------

int Shell::last_exit_code () { return exit_code; }

// Shell::run ------------------------------------------------------------------

std::stringstream Shell::run (const std::string & cmd)
{
  return run(cmd, "");
}

std::stringstream Shell::run (const std::string & cmd,
                              const std::string & input)
{
  // stdout read from cmd
  std::stringstream output;

  // stdin pipe file descriptors
  int std_in[2];

  // stdout pipe file descriptors
  int std_out[2];

  // pid returned by fork (0 == child)
  int pid;

  // open stdin pipe
  if (pipe(std_in) < 0)
    throw std::runtime_error("creating input pipe " + sys_error());

  // open stdout pipe
  if (pipe(std_out) < 0)
    throw std::runtime_error("creating output pipe " + sys_error());

  // fork process
  pid = fork();

  // child process
  if (pid == 0)
    {
      // redirect stdin
      if (dup2(std_in[PIPE_READ], STDIN_FILENO) < 0)
        throw std::runtime_error("redirecting stdin " + sys_error());

      // redirect stdout
      if (dup2(std_out[PIPE_WRITE], STDOUT_FILENO) < 0)
        throw std::runtime_error("redirecting stdout " + sys_error());

      // redirect stderr
      if (dup2(std_out[PIPE_WRITE], STDERR_FILENO) < 0)
        throw std::runtime_error("redirecting stderr " + sys_error());

      // close file descriptors - only used by parent
      close(std_in[PIPE_READ]);
      close(std_in[PIPE_WRITE]);
      close(std_out[PIPE_READ]);
      close(std_out[PIPE_WRITE]);

      // run shell command as child process
      execlp("bash", "bash", "-c", cmd.c_str(), static_cast<char *>(0));

      // exec should not return - if we get here, an error must have happened
      throw std::runtime_error("executing shell command " + sys_error());
    }
  // parent process
  else if (pid > 0)
    {
      // read buffer
      char buffer[BUFFER_SIZE];

      // close unused file descriptors
      close(std_in[PIPE_READ]);
      close(std_out[PIPE_WRITE]);

      // write given input to stdin of child
      if (!input.empty())
        if (write(std_in[PIPE_WRITE], input.c_str(), input.length()) < 0)
          throw std::runtime_error("writing to stdin " + sys_error());

      // close stdin pipe file descriptor
      close(std_in[PIPE_WRITE]);

      // read stdout from child
      int num_read = 0;
      while ((num_read = read(std_out[PIPE_READ], buffer, BUFFER_SIZE - 1)) > 0)
        {
          buffer[num_read] = '\0';
          output << buffer;
        }

      // close remaining file descriptors
      close(std_out[PIPE_READ]);

      // wait for child to finish and assign exit code
      int wstatus;

      waitpid(pid, &wstatus, 0);

      if (WIFEXITED(wstatus))
        exit_code = WEXITSTATUS(wstatus);
      else
        throw
          std::runtime_error("child process exited prematurely " + sys_error());
    }
  // fork failed
  else
    {
      // close file descriptors
      close(std_in[PIPE_READ]);
      close(std_in[PIPE_WRITE]);
      close(std_out[PIPE_READ]);
      close(std_out[PIPE_WRITE]);

      throw std::runtime_error("fork failed " + sys_error());
    }

  return output;
}
