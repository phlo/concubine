# compiler flags
CXX = g++
#CXX =	clang++
CXXFLAGS = -std=c++11 -g -O2 $(WFLAGS)
WFLAGS = -pedantic -Wall -Wextra -Wundef -Wdouble-promotion -Wformat=2 -Wmissing-include-dirs -Wswitch-default -Wunused -Wuninitialized -Wshadow -Wcast-qual -Wcast-align -Wold-style-cast -Wdisabled-optimization -Wredundant-decls -Wstrict-overflow=5 -Wsign-conversion -Werror
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

# deprecated
CT=data/increment.checker.asm
T1=data/increment.asm
T2=data/increment.cas.asm

BV=11
PV=data/test/verify/increment-loop-lt2.asm
SV=data/test/verify/increment-loop-lt2.spec.smt

SEED_ERROR=15
SEED_VALID=86

SCHEDULE=data/increment.valid.schedule

# run tests
test: $(OBJ)
	$(MAKE) -C test

# build executable
build: $(MAIN)

# rebuild executable
rebuild: clean build

# deprecated: run test targets
run: run_verify

run_forever: $(MAIN)
	./run_forever ./simulate_with_random_seed $(CT) $(T1) $(T1)

run_cas: $(MAIN)
	./simulate_with_random_seed $(CT) $(T2) $(T2)

run_cas_forever: $(MAIN)
	./run_forever ./simulate_with_random_seed $(CT) $(T2) $(T2)

run_replay: $(MAIN)
	./$(MAIN) replay -v $(SCHEDULE)

run_verify: $(MAIN)
	./$(MAIN) verify $(BV) $(PV) $(SV)

run_verify_pretend: $(MAIN)
	./$(MAIN) verify -p $(BV) $(PV) $(SV)

# build main and link executable
$(MAIN): $(OBJ) main.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) $(OBJ) main.cc -o $(MAIN)

# delete generated files
clean:
	$(MAKE) -C test clean
	$(RM) *.o *.dSYM $(MAIN)

# export compiler flags for sub-make
export CXX CXXFLAGS OBJ

.PHONY: test run_forever run_cas run_cas_forever
