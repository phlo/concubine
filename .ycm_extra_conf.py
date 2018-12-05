import subprocess

# CXXFLAGS
flags = subprocess.run(['make', 'flags'], stdout=subprocess.PIPE).stdout.decode('utf-8').split()

# googletest flags
flags.append('-I')
flags.append('.')
flags.append('-isystem')
flags.append('test/lib/googletest/googletest/include')
flags.append('-pthread')
flags.append('-D__TEST__')

# recommended clang flags
flags.append('-x')
flags.append('c++')

def Settings(**kwargs):
    return { 'flags': flags }
