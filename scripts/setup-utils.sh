#!/usr/bin/env bash
#
# This script defines common utility functions used by the contrib/setup-*.sh
# scripts.
#
# Stolen from https://github.com/Boolector/boolector.

set -e -o pipefail

die () {
  echo "[setup-utils.sh] error: $*" 1>&2
  exit 1
}

[ -f src/main.cc ] || die "$(basename $0) not called from base directory"

DEPS_DIR="$(pwd)/deps"
INSTALL_DIR="${DEPS_DIR}/install"
INSTALL_LIB_DIR="${INSTALL_DIR}/lib"
INSTALL_INCLUDE_DIR="${INSTALL_DIR}/include"
INSTALL_BIN_DIR="${INSTALL_DIR}/bin"

mkdir -p "$DEPS_DIR"
mkdir -p "$INSTALL_BIN_DIR"
mkdir -p "$INSTALL_INCLUDE_DIR"
mkdir -p "$INSTALL_LIB_DIR"

if type nproc > /dev/null 2>&1; then
  NPROC=$(nproc)
elif [ "$(uname -s)" == "Darwin" ]; then
  NPROC=$(sysctl -n hw.physicalcpu)
else
  NPROC=2
fi

function download_github
{
  local repo="$1"
  local version="$2"
  local location="$3"
  local name=$(echo "$repo" | cut -d '/' -f 2)
  local archive="$name-$version.tar.gz"

  curl -o "$archive" -L "https://github.com/$repo/archive/$version.tar.gz"

  rm -rf "$location"
  tar xfvz "$archive"
  rm "$archive"
  mv "$name-$version" "$location"
}

function install_bin
{
  cp $* "$INSTALL_BIN_DIR"
}

function install_include
{
  cp $* "$INSTALL_INCLUDE_DIR"
}

function install_lib
{
  cp $* "$INSTALL_LIB_DIR"
}
