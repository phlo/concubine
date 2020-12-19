#!/bin/bash

DEPSDIR=deps/install
BUILDDIR=build

#------------------------------------------------------------------------------#

debug=no
check=no
pedantic=no
symbols=no
coverage=no
profile=no
static=no
options=""

#------------------------------------------------------------------------------#

usage () {
cat << EOF
usage: $(basename $0) [ <option> ... ]

where '<option>' is one of the following

-h|--help          print this command line summary
-g|--debug         compile with debugging information (implies '-c')
-c|--check         compile with assertion checking
-p|--pedantic      compile with '-Werror' and a pedantic set of warning flags
-s|--symbols       compile '-ggdb3' (implies '-g')

--static           compile with '-static' linker flag

--coverage         compile with '-ftest-coverage -fprofile-arcs' for 'gcov'
--profile          compile with '-pg' for 'gprof'

-f...              pass '-f<option>[=<val>]' options to the Makefile
-O|-O[123]         pass '-O' or '-O[123]' to the Makefile

-j|-j...           pass a jobs option to the Makefile (for parallel builds)

The environment variable CXX can be used to set a different C++ compiler than
the default 'g++'. Similarly you can add additional compilation options by
setting CXXFLAGS. For example

  CXX=clang++ CXXFLAGS=-fPIC $0

will enforce to use 'clang++' as C++ compiler and also produce position
independent code. In order to be shell independent we also allow to have the
following form. Thus for instance

  $0 CXX="g++-8" CXXFLAGS="-fPIC -fsanitize=address"

will have the same effect as

  CXX="g++-8" $0 -fPIC -fsanitize=address
EOF
exit 0
}

#------------------------------------------------------------------------------#

msg () {
  echo "[configure.sh] $*"
}

die () {
  echo "[configure.sh] error: $*" 1>&2
  exit 1
}

#------------------------------------------------------------------------------#

[ -f src/main.cc ] || die "not called from base directory"

while [ $# -gt 0 ]
do
  case $1 in
    -h|--help) usage;;

    -g|--debug) debug=yes;;
    -c|--check) check=yes;;
    -p|--pedantic) pedantic=yes;;
    -s|--symbols) symbols=yes; debug=yes;;

    --static) static=yes;;

    --coverage) coverage=yes;;
    --profile) profile=yes;;

    -f*) [ -z $options ] && options="$1" || options="$options $1";;
    -O|-O1|-O2|-O3) optimization="$1";;

    -j*) MAKEFLAGS="$1";;

    CXX=*) CXX="`expr \"$1\" : 'CXX=\(.*\)'`";;
    CXXFLAGS=*) CXXFLAGS="`expr \"$1\" : 'CXXFLAGS=\(.*\)'`";;

    *) die "invalid option '$1' (try '-h')";;
  esac
  shift
done

#------------------------------------------------------------------------------#

[ -z "$CXX" ] && CXX="g++"

[ ! -z "$CXXFLAGS" ] && CXXFLAGS="$CXXFLAGS "
CXXFLAGS="${CXXFLAGS}-std=c++17"

[ $symbols = yes ] && debug=yes
if [ $debug = yes ]
then
  check=yes
  CXXFLAGS="$CXXFLAGS -g"
  [ $symbols = yes ] && CXXFLAGS="$CXXFLAGS -ggdb3"
else
  [ -z "$optimization" ] && optimization="-O3"
fi

[ ! -z "$optimization" ] && CXXFLAGS="$CXXFLAGS $optimization"
[ ! -z "$options" ] && CXXFLAGS="$CXXFLAGS $options"
[ $coverage = yes ] && CXXFLAGS="$CXXFLAGS -ftest-coverage -fprofile-arcs"
[ $profile = yes ] && CXXFLAGS="$CXXFLAGS -pg"
[ $check = no ] && CXXFLAGS="$CXXFLAGS -DNDEBUG"

WFLAGS="-Wall -Wextra"
[ $pedantic = yes ] && WFLAGS="\
-pedantic \
-Werror \
-Wfatal-errors \
$WFLAGS \
-Wcast-align \
-Wcast-qual \
-Wdisabled-optimization \
-Wformat=2 \
-Wmissing-include-dirs \
-Wold-style-cast \
-Wredundant-decls \
-Wshadow \
-Wsign-conversion \
-Wstrict-overflow \
-Wswitch-default \
-Wundef \
-Wuninitialized \
-Wunused\
"

LDFLAGS="-lz3"
[ $static = yes ] && die "static linking not yet supported"

#------------------------------------------------------------------------------#

echo '#include "z3++.h"' \
  | g++ -H -fsyntax-only -x c++ -I${DEPSDIR}/include - > /dev/null 2>&1 \
    || die "missing z3 (either install system wide or use 'scripts/setup-z3')"

if [ -f ${DEPSDIR}/lib/libz3.so ]
then
  CXXFLAGS="$CXXFLAGS -I../${DEPSDIR}/include"
  LDFLAGS="-L../${DEPSDIR}/lib -Wl,-rpath,$(realpath ${DEPSDIR}/lib) $LDFLAGS"
  WFLAGS=${WFLAGS/ -Wold-style-cast/}
  WFLAGS=${WFLAGS/ -Wsign-conversion/}
  WFLAGS=${WFLAGS/ -Wshadow/}
fi

#------------------------------------------------------------------------------#

msg "using '$CXX $CXXFLAGS $LDFLAGS $WFLAGS'"

mkdir -p $BUILDDIR
cd $BUILDDIR || die "failed to create 'build' directory"

rm -rf Makefile
sed \
  -e "s#@CXX@#$CXX#" \
  -e "s#@CXXFLAGS@#$CXXFLAGS#" \
  -e "s#@LDFLAGS@#$LDFLAGS#" \
  -e "s#@WFLAGS@#$WFLAGS#" \
  -e "s#@MAKEFLAGS@#$MAKEFLAGS#" \
  ../Makefile.in > Makefile

msg "run 'cd build && make' to build ConcuBinE"
