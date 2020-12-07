GTEST_FILTER = --gtest_filter=

GTEST_FILTER += "*"
# GTEST_FILTER += Encoder.*
# GTEST_FILTER += smtlib.*
# GTEST_FILTER += smtlib_Encoder.*
# GTEST_FILTER += smtlib_Functional.*
# GTEST_FILTER += smtlib_Relational.*
# GTEST_FILTER += btor2.*
# GTEST_FILTER += btor2_Encoder.*
# GTEST_FILTER += Simulator.*
# GTEST_FILTER += Main.*
# GTEST_FILTER += Experimental.*
# GTEST_FILTER += Instruction.*
# GTEST_FILTER += Program.*
# GTEST_FILTER += Trace.*
# GTEST_FILTER += MMap.*
# GTEST_FILTER += Shell.*
# GTEST_FILTER += Boolector.*
# GTEST_FILTER += BtorMC.*
# GTEST_FILTER += Z3.*
# GTEST_FILTER += CVC4.*

GTEST_FILTER := $(shell echo ${GTEST_FILTER} | sed -e 's/ /:/g')

GTEST_CMD = $(BUILDDIR)/$(GTEST_APP) $(GTEST_FILTER)
GTEST_DIR = ../test/lib/googletest/googletest
GTEST_LIB = $(GTEST_DIR)/make/gtest-all.o

$(GTEST_LIB):
	git submodule update --init --depth 1
	CXXFLAGS="" $(MAKE) -C $(dir $(GTEST_LIB)) $(notdir $(GTEST_LIB))

#------------------------------------------------------------------------------#

GTEST_APP = bin/gtest
GTEST_SRC = $(subst ../test/,,$(sort $(wildcard ../test/test_*.cc)))
GTEST_OBJ = $(subst .cc,.o,$(GTEST_SRC))

VPATH += :../test

$(GTEST_APP): CXXFLAGS += -isystem $(GTEST_DIR)/include -I../src -D__TEST__
$(GTEST_APP): LDFLAGS += -lpthread
$(GTEST_APP): $(OBJ) $(GTEST_OBJ) main_gtest.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) $(WFLAGS) $(GTEST_LIB) $^ -o $@

$(GTEST_OBJ): $(GTEST_LIB)

#------------------------------------------------------------------------------#

.PHONY: test
test: $(APP) $(GTEST_APP)
	cd .. && $(GTEST_CMD)

.PHONY: test-deps
test-deps: $(APP) $(GTEST_APP)
	cd .. && . ./scripts/set-search-path.sh -f && $(GTEST_CMD)

#------------------------------------------------------------------------------#

.PHONY: debug
debug: $(APP) $(GTEST_APP)
	cd .. && gdb --args $(GTEST_CMD)

#------------------------------------------------------------------------------#

VALGRIND = valgrind \
           -v \
           --leak-check=full \
           --show-leak-kinds=all \
           --undef-value-errors=no

.PHONY: valgrind
valgrind: $(APP) $(GTEST_APP)
	cd .. && $(VALGRIND) $(GTEST_CMD)

#------------------------------------------------------------------------------#

.PHONY: clean
clean:
	rm -rf bin
	rm -f *.o *.d
	rm -f *.gcda *.gcno *.gcov gmon.out
