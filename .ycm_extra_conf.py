import subprocess

flags = subprocess.run(['make', 'flags'], stdout=subprocess.PIPE).stdout.decode('utf-8').split()

flags.append('-x')
flags.append('c++')

def Settings(**kwargs):
    return { 'flags': flags }
