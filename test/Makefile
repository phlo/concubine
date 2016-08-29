# NOTE: depends on exported variables by parent Makefile
#       - CFLAGS
#       - OBJ
#       - MAIN

# googletest root
GTEST_DIR = lib/googletest/googletest

# googletest library
GTEST_LIB = $(GTEST_DIR)/make/gtest-all.o

# compiler flags (exported from parent makefile)
CXXFLAGS = $(CFLAGS) \
           $(WFLAGS) \
           -isystem $(GTEST_DIR)/include \
           -I../ \
           -pthread \
           -D__TEST__

# compiler warnings
WFLAGS = -pedantic -Wall -Wextra

# object files of code to test (exported)
OBJ := $(addprefix ../,$(OBJ))

# object files of test cases (test_*.cc)
TEST_OBJ := $(subst .cc,.o,$(wildcard test_*.cc))

# main file
TEST_MAIN := main_gtest.cc

# executable name
TEST_RUN := run_all_tests

# run all tests
run: $(TEST_RUN)
	./$(TEST_RUN)

# build executable containing all test cases
$(TEST_RUN): $(OBJ) $(TEST_OBJ) $(GTEST_LIB)
	$(CXX) $(CXXFLAGS) $^ $(TEST_MAIN) -o $@

# build googletest library
$(GTEST_LIB):
	make -C $(dir $(GTEST_LIB)) $(notdir $(GTEST_LIB))

# delete generated files
clean:
	-rm -rf *.o *.dSYM $(TEST_RUN)

# delete generated files and libraries
clean-all: clean
	make -C $(dir $(GTEST_LIB)) clean

.PHONY: run clean clean-all
