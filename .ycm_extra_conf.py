import os
import sys
import inspect

# base directory
root = os.path.realpath(os.path.dirname(inspect.getsourcefile(lambda:0)))

# CXXFLAGS
with open(root + "/build/Makefile") as f:
    for line in f:
        if line.startswith("CXXFLAGS"):
            flags = line.split(' = ')[1].strip().replace('..', root).split()
            break

# googletest flags
flags.append('-I')
flags.append('.')
flags.append('-isystem')
flags.append(root + '/test/lib/googletest/googletest/include')
flags.append('-pthread')
flags.append('-D__TEST__')

# recommended clang flags
flags.append('-x')
flags.append('c++')

def Settings(**kwargs):
    return { 'flags': flags }
