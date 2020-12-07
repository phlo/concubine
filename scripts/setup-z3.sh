#!/bin/bash
#
# Install shared library.

source "$(dirname $0)/setup-utils.sh"

dir="${DEPS_DIR}/z3"
version="z3-4.8.9"

download_github "Z3Prover/z3" "$version" "$dir"

cd "$dir"

./configure

cd build

make -j${NPROC}

install_include ../src/api/c++/z3++.h
install_lib libz3.so
