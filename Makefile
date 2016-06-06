#CXX=clang++
CXX=g++
WFLAGS=-pedantic -Wall -Wextra -Wundef -Wdouble-promotion -Wformat=2 -Wmissing-include-dirs -Wswitch-default -Wunused -Wuninitialized -Wshadow -Wcast-qual -Wcast-align -Wold-style-cast -Wmissing-declarations -Wdisabled-optimization -Wredundant-decls -Wstrict-overflow=5 -Wsign-conversion -Werror
CXXFLAGS=-std=c++11 -g $(WFLAGS) -O2
LDFLAGS=$(CXXFLAGS)
LDLIBS=
RM=rm -rf

SRCS=instructionset.cc program.cc schedule.cc parser.cc machine.cc thread.cc
OBJS=$(subst .cc,.o,$(SRCS))

SIMULATOR=simulator
SIMULATOR_OBJS=$(OBJS) main_simulator.cc

REPLAY=replay
REPLAY_OBJS=$(OBJS) main_replay.cc

CT=data/increment_checker.asm
T1=data/increment.asm
T2=data/increment.cas.asm

SEED_ERROR=15
SEED_VALID=86

SCHEDULE=data/increment.valid.schedule

build: clean all

run: run_forever

run_replay: $(REPLAY)
	./replay -v $(SCHEDULE)

run_forever: $(SIMULATOR)
	{ \
  while true; do \
    ./run_no_cas; \
    ret=$$?; \
    if [ "$$ret" != "0" ]; then \
      exit $$ret; \
    fi; \
  done \
}

run_cas_forever: $(SIMULATOR)
	{ \
  while true; do \
    ./run_cas; \
    ret=$$?; \
    if [ "$$ret" != "0" ]; then \
      exit $$ret; \
    fi; \
  done \
}

run_cas: $(SIMULATOR)
	./run_cas

run_valid: $(SIMULATOR)
	./run_no_cas

run_schedule: $(REPLAY)
	./$(REPLAY) $(SCHEDULE)

$(SIMULATOR): $(SIMULATOR_OBJS)
	$(CXX) $(LDFLAGS) -o $(SIMULATOR) $(SIMULATOR_OBJS) $(LDLIBS)

$(REPLAY): $(REPLAY_OBJS)
	$(CXX) $(LDFLAGS) -o $(REPLAY) $(REPLAY_OBJS) $(LDLIBS)

all: $(SIMULATOR) $(REPLAY)

clean:
	$(RM) *.o *.dSYM $(SIMULATOR) $(REPLAY)
