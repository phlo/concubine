#!/bin/bash
#
# Requires 'gmp' and 'toml'!

source "$(dirname $0)/setup-utils.sh"

dir="${DEPS_DIR}/cvc4"
version="1.8"

download_github "CVC4/CVC4" "$version" "$dir"

cd "$dir"

./contrib/get-antlr-3.4
./contrib/get-cadical
# ldconfig -p | grep -q "libgmp" || ./contrib/get-gmp-dev

./configure.sh --cadical

cd build

make -j${NPROC}

install_bin bin/cvc4
