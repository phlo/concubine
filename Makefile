# compiler flags
CXX      = g++
#CXX      = clang++
CFLAGS   = -std=c++17 -g -ggdb #-O2
CXXFLAGS = $(CFLAGS) $(WFLAGS)
WFLAGS   = -pedantic \
           -Wall \
           -Wextra \
           -Wundef \
           -Wformat=2 \
           -Wmissing-include-dirs \
           -Wswitch-default \
           -Wunused \
           -Wuninitialized \
           -Wshadow \
           -Wcast-qual \
           -Wcast-align \
           -Wold-style-cast \
           -Wdisabled-optimization \
           -Wredundant-decls \
           -Wstrict-overflow \
           -Wsign-conversion \
           -Werror \
           -Wfatal-errors
LDFLAGS  = -lz3

# source files (excluding main.cc)
SRC = boolector.cc \
      btormc.cc \
      cvc4.cc \
      encoder.cc \
      instructionset.cc \
      program.cc \
      schedule.cc \
      shell.cc \
      simulator.cc \
      solver.cc \
      thread.cc \
      z3.cc

# object files
OBJ = $(subst .cc,.o,$(SRC))

# executable name
MAIN = concubine

# run tests
.PHONY: test
test: build
	$(MAKE) -C test

# debug
.PHONY: debug
debug: build
	$(MAKE) -C test debug

# valgrind
.PHONY: valgrind
valgrind: build
	$(MAKE) -C test valgrind

# build executable
.PHONY: build
build: $(MAIN)

# rebuild executable
.PHONY: rebuild
rebuild: clean build

# build main and link executable
$(MAIN): $(OBJ) main.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) $(OBJ) main.cc -o $(MAIN)

# delete generated files
.PHONY: clean
clean:
	$(MAKE) -C test clean
	-rm -rf *.o *.d *.dSYM $(MAIN)

# find trailing whitespaces
.PHONY: trim
trim:
	grep "\s\+$$" -n *.{hh,cc} Makefile test/*.{hh,cc} test/Makefile

# print CFLAGS
.PHONY: flags
flags:
	@echo $(CXXFLAGS)

# export compiler flags for sub-make
export CXX CXXFLAGS OBJ

# auto-dependency generation
include dependencies.mk

# demo #########################################################################

# program files
CT=test/data/increment.checker.asm
T1=test/data/increment.asm
T2=test/data/increment.cas.asm

BV=5
PV=test/data/load.store.arithmetic.asm
SV=test/data/load.store.arithmetic.spec.smt

SCHEDULE=data/increment.invalid.schedule

# demo targets
.PHONY: run
run: run_forever

.PHONY: run_forever
run_forever: $(MAIN)
	./run_forever ./simulate_with_random_seed $(CT) $(T1) $(T1)

.PHONY: run_cas
run_cas: $(MAIN)
	./simulate_with_random_seed $(CT) $(T2) $(T2)

.PHONY: run_cas_forever
run_cas_forever: $(MAIN)
	./run_forever ./simulate_with_random_seed $(CT) $(T2) $(T2)

.PHONY: run_replay
run_replay: $(MAIN)
	cd test && ../$(MAIN) replay -v $(SCHEDULE)

.PHONY: run_verify
run_verify: $(MAIN)
	./$(MAIN) verify $(BV) $(PV) $(SV)

.PHONY: run_verify_pretend
run_verify_pretend: $(MAIN)
	@./$(MAIN) verify -p $(BV) $(PV) $(SV)
