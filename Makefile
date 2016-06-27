#CXX=clang++
CXX=g++
WFLAGS=-pedantic -Wall -Wextra -Wundef -Wdouble-promotion -Wformat=2 -Wmissing-include-dirs -Wswitch-default -Wunused -Wuninitialized -Wshadow -Wcast-qual -Wcast-align -Wold-style-cast -Wdisabled-optimization -Wredundant-decls -Wstrict-overflow=5 -Wsign-conversion -Werror
CXXFLAGS=-std=c++11 -g $(WFLAGS) -O2
LDFLAGS=$(CXXFLAGS)
LDLIBS=
RM=rm -rf

SRCS=instructionset.cc program.cc schedule.cc parser.cc machine.cc thread.cc
OBJS=$(subst .cc,.o,$(SRCS))

MAIN=psimsmt

CT=data/increment_checker.asm
T1=data/increment.asm
T2=data/increment.cas.asm

SEED_ERROR=15
SEED_VALID=86

SCHEDULE=data/increment.valid.schedule

build: clean all

run: run_forever

run_forever: $(MAIN)
	./run_forever

run_cas: $(MAIN)
	./run_cas

run_cas_forever: $(MAIN)
	./run_cas_forever

run_replay: $(MAIN)
	./$(MAIN) replay -v $(SCHEDULE)

run_unroll: $(MAIN)
	./$(MAIN) unroll -v -a 10 $(T2)

$(MAIN): $(OBJS) main.cc
	$(CXX) $(LDFLAGS) -o $(MAIN) $(OBJS) main.cc $(LDLIBS)

all: $(MAIN)

clean:
	$(RM) *.o *.dSYM $(MAIN)

.PHONY: run_forever run_cas run_cas_forever
