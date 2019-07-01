# NOTE: depends on exported variables by parent Makefile
# - CXX
# - CXXFLAGS
# - OBJ

# googletest root
GTEST_DIR = lib/googletest/googletest

# googletest library
GTEST_LIB = $(GTEST_DIR)/make/gtest-all.o

# compiler flags (exported from parent makefile)
CXXFLAGS += -isystem $(GTEST_DIR)/include \
			-I../ \
			-pthread \
			-lboolector \
			-lz3 \
			-D__TEST__

# object files of code to test (exported)
OBJ := $(addprefix ../,$(OBJ))

# test source files
SRC := $(wildcard test_*.cc)

# object files of test cases (test_*.cc)
TEST_OBJ := $(subst .cc,.o,$(SRC))

# main file
TEST_MAIN := main_gtest.cc

# executable name
TEST_RUN := run_all_tests

# gtest filter
GTEST_FILTER = --gtest_filter=

# GTEST_FILTER += "*"
# GTEST_FILTER += *Encoder*
GTEST_FILTER += Encoder_Test.*
GTEST_FILTER += SMTLib_Test.*
GTEST_FILTER += SMTLib_Encoder_Test.*
GTEST_FILTER += SMTLib_Encoder_Functional_Test.*
GTEST_FILTER += SMTLib_Encoder_Relational_Test.*
GTEST_FILTER += Btor2_Test.*
GTEST_FILTER += Btor2_Encoder_Test.*
GTEST_FILTER += Thread_Test.*
# GTEST_FILTER += Simulator_Test.*
# GTEST_FILTER += Main_Test.*
# GTEST_FILTER += Experimental.*
GTEST_FILTER += Instruction_Test.*
GTEST_FILTER += Program_Test.*
# GTEST_FILTER += Schedule_Test.*
# GTEST_FILTER += Shell_Test.*
# GTEST_FILTER += Boolector_Test.*
# GTEST_FILTER += BtorMC_Test.*
# GTEST_FILTER += Z3_Test.*
# GTEST_FILTER += CVC4_Test.*

GTEST_FILTER := $(shell echo ${GTEST_FILTER} | sed -e 's/ /:/g')

# run tests
.PHONY: run
run: $(TEST_RUN)
	./$(TEST_RUN) $(GTEST_FILTER)

# debug tests
.PHONY: debug
debug: $(TEST_RUN)
	gdb --args $(TEST_RUN) $(GTEST_FILTER)

# valgrind tests
VALGRIND = valgrind \
           -v \
           --leak-check=full \
           --show-leak-kinds=all \
           --undef-value-errors=no

.PHONY: valgrind
valgrind: $(TEST_RUN)
	$(VALGRIND) ./$(TEST_RUN) $(GTEST_FILTER)

# run experiments
.PHONY: experiments
experiments: experimental
	./$<

EXPERIMENTS = experiments.cc \
			  ../instruction.hh ../instruction.cc \
			  ../program.hh ../program.cc

experimental: $(EXPERIMENTS) $(GTEST_LIB)
	$(CXX) $(CXXFLAGS) $^ $(TEST_MAIN) -o $@

# build executable containing all test cases
$(TEST_RUN): $(GTEST_LIB) $(OBJ) $(TEST_OBJ)
	$(CXX) $(CXXFLAGS) $^ $(TEST_MAIN) -o $@

# build googletest library
$(GTEST_DIR):
	git submodule update --init

$(GTEST_LIB): $(GTEST_DIR)
	CXXFLAGS="" $(MAKE) -C $(dir $(GTEST_LIB)) $(notdir $(GTEST_LIB))

# delete generated files
.PHONY: clean
clean:
	-rm -rf *.o *.d *.dSYM $(TEST_RUN)

# delete generated files and libraries
.PHONY: clean-all
clean-all: clean
	$(MAKE) -C $(dir $(GTEST_LIB)) clean

# auto-dependency generation
include ../dependencies.mk
