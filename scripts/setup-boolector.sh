#!/bin/bash
#
# Using current master since '3.2.1' doesn't support '--output-format=btor'.

source "$(dirname $0)/setup-utils.sh"

dir="${DEPS_DIR}/boolector"
version="59e230fcb75e723c3054fd23a1884288efa747fd"

download_github "boolector/boolector" "$version" "$dir"

cd "$dir"

./contrib/setup-btor2tools.sh
./contrib/setup-cadical.sh

./configure.sh

cd build

make -j${NPROC}

install_bin bin/{boolector,btormc}
