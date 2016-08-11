#CXX=clang++
CXX=g++
WFLAGS=-pedantic -Wall -Wextra -Wundef -Wdouble-promotion -Wformat=2 -Wmissing-include-dirs -Wswitch-default -Wunused -Wuninitialized -Wshadow -Wcast-qual -Wcast-align -Wold-style-cast -Wdisabled-optimization -Wredundant-decls -Wstrict-overflow=5 -Wsign-conversion -Werror
CXXFLAGS=-std=c++11 -g $(WFLAGS) -O2
LDFLAGS=$(CXXFLAGS)
LDLIBS=
RM=rm -rf

SRCS=instructionset.cc \
		 schedule.cc \
		 program.cc \
		 machine.cc \
		 parser.cc \
		 thread.cc \
		 encoder.cc

OBJS=$(subst .cc,.o,$(SRCS))

MAIN=psimsmt

CT=data/increment.checker.asm
T1=data/increment.asm
T2=data/increment.cas.asm

SEED_ERROR=15
SEED_VALID=86

SCHEDULE=data/increment.valid.schedule

build: clean all

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
	./$(MAIN) verify 3 $(T1)

$(MAIN): $(OBJS) main.cc
	$(CXX) $(LDFLAGS) -o $(MAIN) $(OBJS) main.cc $(LDLIBS)

all: $(MAIN)

clean:
	$(RM) *.o *.dSYM $(MAIN)

.PHONY: run_forever run_cas run_cas_forever
