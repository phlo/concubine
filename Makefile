CXX=clang++
#WFLAGS=-pedantic -Wall -Wextra
WFLAGS=-pedantic -Wall -Wno-unused -Wextra -Wcast-align -Wcast-qual -Wctor-dtor-privacy -Wdisabled-optimization -Wformat=2 -Winit-self -Wmissing-declarations -Wmissing-include-dirs -Wold-style-cast -Woverloaded-virtual -Wredundant-decls -Wshadow -Wsign-promo -Wstrict-overflow=5 -Wswitch-default -Wundef -Werror -Wsign-conversion
CXXFLAGS=-std=c++11 -g $(WFLAGS) -O3
LDFLAGS=$(CXXFLAGS)
LDLIBS=
RM=rm -f

SRCS=main.cc instructionset.cc program.cc parser.cc machine.cc thread.cc
OBJS=$(subst .cc,.o,$(SRCS))

EXECUTABLE=simulator

CT=asm/increment_checker.asm
T1=asm/increment.asm
T2=$(T1)

SEED_ERROR=15
SEED_VALID=86

build: clean all

run: run_valid

run_forever: all
	./$(EXECUTABLE) -c $(CT) -t $(T1) -t $(T2)

run_valid: all
	./$(EXECUTABLE) -s $(SEED_VALID) $(CT) $(T1) $(T2)

run_error: all
	./$(EXECUTABLE) -s $(SEED_ERROR) $(CT) $(T1) $(T2)

all: $(EXECUTABLE)

$(EXECUTABLE): $(OBJS)
	$(CXX) $(LDFLAGS) -o $(EXECUTABLE) $(OBJS) $(LDLIBS)

clean:
	$(RM) $(OBJS)
