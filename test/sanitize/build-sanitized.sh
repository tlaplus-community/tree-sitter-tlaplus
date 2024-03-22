#!/bin/bash
set -e

CC=${CC:-clang}
CXX=${CXX:-clang++}
LINK=${LINK:-clang++}

sanitizer_flags="-fsanitize=address,undefined -fno-omit-frame-pointer"

CFLAGS=${CFLAGS:-"$sanitizer_flags"}
CXXFLAGS=${CXXFLAGS:-"$sanitizer_flags"}

export CC
export CXX
export LINK
export CFLAGS
export CXXFLAGS

sanitize_dir=test/sanitize
lang_name="tlaplus"
ts_lang="tree_sitter_${lang_name}"
dependencies_dir=test/dependencies
ts_dir=$dependencies_dir/tree-sitter
src_dir="src"
out_dir="${sanitize_dir}/out"
mkdir -p $out_dir
parser="parser"
parser_in="${src_dir}/${parser}.c"
parser_out="${out_dir}/${parser}.o"
scanner="scanner"
scanner_in="${src_dir}/${scanner}.c"
scanner_out="${out_dir}/${scanner}.o"

if [ -z "$1" ]; then
  echo "Building tree-sitter..."
  pushd $ts_dir
  make clean
  make
  popd

  # Compiling with -O0 speeds up the build dramatically
  echo "Building parser..."
  $CC $CFLAGS -g -O0 -I $src_dir -c $parser_in -o $parser_out
fi

echo "Building scanner..."
$CC $CFLAGS -g -O0 -I $src_dir -c $scanner_in -o $scanner_out

echo "Building runner..."
$CXX $CXXFLAGS \
  -I $ts_dir/lib/include \
  -D TS_LANG=$ts_lang \
  $sanitize_dir/runner.cc $parser_out $scanner_out $ts_dir/libtree-sitter.a \
  -o $out_dir/parse_${lang_name}

