# compiler flags
CXX = g++
#CXX =	clang++
CFLAGS = -std=c++11 -g -O2
CXXFLAGS = $(CFLAGS) $(WFLAGS)
WFLAGS = -pedantic -Wall -Wextra -Wundef -Wformat=2 -Wmissing-include-dirs -Wswitch-default -Wunused -Wuninitialized -Wshadow -Wcast-qual -Wcast-align -Wold-style-cast -Wdisabled-optimization -Wredundant-decls -Wstrict-overflow -Wsign-conversion -Werror
LDFLAGS =

# additional command definitions
RM = rm -rf

# source files (excluding main.cc)
SRC = instructionset.cc \
      schedule.cc \
      program.cc \
      machine.cc \
      parser.cc \
      thread.cc \
      encoder.cc \
      verifier.cc \
      shell.cc \
      solver.cc \
      boolector.cc

# object files
OBJ = $(subst .cc,.o,$(SRC))

# executable name
MAIN = psimsmt

# run tests
test: build
	$(MAKE) -C test

# build executable
build: $(MAIN)

# rebuild executable
rebuild: clean build

# build main and link executable
$(MAIN): $(OBJ) main.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) $(OBJ) main.cc -o $(MAIN)

# delete generated files
clean:
	$(MAKE) -C test clean
	$(RM) *.o *.dSYM $(MAIN)

# find trailing whitespaces
trim:
	grep "\s\+$$" -n *.{hh,cc} Makefile test/*.{hh,cc} test/Makefile

# export compiler flags for sub-make
export CXX CFLAGS OBJ MAIN

.PHONY: test run_forever run_cas run_cas_forever trim

# program files
CT=test/data/increment.checker.asm
T1=test/data/increment.asm
T2=test/data/increment.cas.asm

BV=5
PV=test/data/load.store.arithmetic.asm
SV=test/data/load.store.arithmetic.spec.smt

SCHEDULE=data/increment.invalid.schedule

# demo targets
run: run_forever

run_forever: $(MAIN)
	./run_forever ./simulate_with_random_seed $(CT) $(T1) $(T1)

run_cas: $(MAIN)
	./simulate_with_random_seed $(CT) $(T2) $(T2)

run_cas_forever: $(MAIN)
	./run_forever ./simulate_with_random_seed $(CT) $(T2) $(T2)

run_replay: $(MAIN)
	cd test && ../$(MAIN) replay -v $(SCHEDULE)

run_verify: $(MAIN)
	./$(MAIN) verify $(BV) $(PV) $(SV)

run_verify_pretend: $(MAIN)
	./$(MAIN) verify -p $(BV) $(PV) $(SV)
