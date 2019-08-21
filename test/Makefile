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
            -D__TEST__

# linker flags (exported from parent makefile)
LDFLAGS += -lboolector

ifeq ($(CXX),g++)
	# std::filesystem
	LDFLAGS += -lstdc++fs
else
	# std::filesystem
	LDFLAGS += -lc++fs
endif

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
GTEST_FILTER += Encoder.*
# GTEST_FILTER += smtlib.*
GTEST_FILTER += smtlib_Encoder.*
GTEST_FILTER += smtlib_Functional.*
GTEST_FILTER += smtlib_Relational.*
# GTEST_FILTER += btor2.*
GTEST_FILTER += btor2_Encoder.*
# GTEST_FILTER += Simulator.*
# GTEST_FILTER += Main.*
# GTEST_FILTER += Experimental.*
# GTEST_FILTER += Instruction.*
# GTEST_FILTER += Program.*
# GTEST_FILTER += Trace.*
# GTEST_FILTER += MMap.*
# GTEST_FILTER += Shell.*
# GTEST_FILTER += Boolector.*
# GTEST_FILTER += BtorMC.litmus*
# GTEST_FILTER += Z3.*
# GTEST_FILTER += CVC4.*

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

EXPERIMENTS = experiments.cc

experimental: $(EXPERIMENTS) $(GTEST_LIB)
	$(CXX) $(CXXFLAGS) $^ $(TEST_MAIN) -o $@

# build executable containing all test cases
$(TEST_RUN): $(GTEST_LIB) $(OBJ) $(TEST_OBJ) $(TEST_MAIN)
	$(CXX) $(CXXFLAGS) $^ $(LDFLAGS) -o $@

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
