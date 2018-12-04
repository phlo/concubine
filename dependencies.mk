# auto-dependency generation
#
# see http://make.mad-scientist.net/papers/advanced-auto-dependency-generation/#combine
DEPFLAGS = -MT $@ -MMD -MP -MF $*.d
MAKE_C = $(CC) $(DEPFLAGS) $(CFLAGS) $(CXXFLAGS) -c $<
MAKE_CXX = $(CXX) $(DEPFLAGS) $(CXXFLAGS) -c $<

%.o: %.c
%.o: %.c %.d
	$(MAKE_C)

%.o: %.cc
%.o: %.cc %.d
	$(MAKE_CXX)

%.o: %.cpp
%.o: %.cpp %.d
	$(MAKE_CXX)

%.o: %.cxx
%.o: %.cxx %.d
	$(MAKE_CXX)

%.d: ;
.PRECIOUS: %.d

include $(wildcard *.d)
