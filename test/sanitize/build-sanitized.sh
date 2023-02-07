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

echo "Building tree-sitter..."
dependencies_dir=test/dependencies
ts_dir=$dependencies_dir/tree-sitter
pushd $ts_dir
make clean
make
popd

sanitize_dir=test/sanitize
lang_name="tlaplus"
ts_lang="tree_sitter_${lang_name}"

objects=()

src_dir="src"
out_dir="${sanitize_dir}/out"
mkdir -p $out_dir

echo "Building scanner..."
scanner="scanner"
scanner_in="${src_dir}/${scanner}.cc"
scanner_out="${out_dir}/${scanner}.o"
$CXX $CXXFLAGS -g -O1 -I $src_dir -c $scanner_in -o $scanner_out

# Compiling with -O0 speeds up the build dramatically
echo "Building parser..."
parser="parser"
parser_in="${src_dir}/${parser}.c"
parser_out="${out_dir}/${parser}.o"
$CC $CFLAGS -g -O0 -I $src_dir -c $parser_in -o $parser_out

echo "Building runner..."
$CXX $CXXFLAGS \
  -I $ts_dir/lib/include \
  -D TS_LANG=$ts_lang \
  $sanitize_dir/runner.cc $parser_out $scanner_out $ts_dir/libtree-sitter.a \
  -o $out_dir/parse_${lang_name}

