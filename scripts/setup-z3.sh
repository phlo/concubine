#!/bin/bash
#
# Install shared library.

source "$(dirname $0)/setup-utils.sh"

dir="${DEPS_DIR}/z3"
version="z3-4.8.9"

download_github "Z3Prover/z3" "$version" "$dir"

cd "$dir"

./configure --prefix=${DEPS_DIR}/install

cd build

make -j${NPROC}
make install

rm "${INSTALL_BIN_DIR}/z3"
