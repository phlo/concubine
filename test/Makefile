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

# run all tests
.PHONY: run
run: $(TEST_RUN)
	# ./$(TEST_RUN) --gtest_filter=SMTLibEncoderFunctional*
	# ./$(TEST_RUN) --gtest_filter=SMTLibEncoderRelational*
	# ./$(TEST_RUN) --gtest_filter=Btor2*
	./$(TEST_RUN) --gtest_filter=BtorMC*
	# ./$(TEST_RUN)

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
