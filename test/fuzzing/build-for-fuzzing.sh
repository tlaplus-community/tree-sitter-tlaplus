#!/bin/bash
# Adapted from https://github.com/tree-sitter/tree-sitter/blob/master/script/build-fuzzers
# MIT License Copyright (c) 2018-2021 Max Brunsfeld

set -e

if [[ "$(uname -s)" != Linux ]]; then
  echo "Fuzzing is only supported on Linux"
  exit 1
fi

CC=${CC:-clang}
CXX=${CXX:-clang++}
LINK=${LINK:-clang++}

default_fuzz_flags="-fsanitize=fuzzer,address,undefined"

CFLAGS=${CFLAGS:-"$default_fuzz_flags"}
CXXFLAGS=${CXXFLAGS:-"$default_fuzz_flags"}

export CC
export CXX
export LINK
export CFLAGS
export CXXFLAGS

echo "Building tree-sitter..."
fuzz_dir="test/fuzzing"
ts_dir="${fuzz_dir}/tree-sitter"
pushd $ts_dir
make clean
make
popd

ts_lang="tree_sitter_tlaplus"
echo "Building ${ts_lang} fuzzer..."

objects=()

src_dir="src"
out_dir="${fuzz_dir}/out"
mkdir -p $out_dir

scanner="scanner"
scanner_in="${src_dir}/${scanner}.cc"
scanner_out="${out_dir}/${scanner}.o"
$CXX $CXXFLAGS -g -O1 -I $src_dir -c $scanner_in -o $scanner_out

# Compiling with -O0 speeds up the build dramatically
parser="parser"
parser_in="${src_dir}/${parser}.c"
parser_out="${out_dir}/${parser}.o"
$CC $CFLAGS -g -O0 -I $src_dir -c $parser_in -o $parser_out

highlights_file="highlights.scm"
highlights_in="queries/${highlights_file}"
highlights_out="${out_dir}/${highlights_file}"
cp $highlights_in $highlights_out

$CXX $CXXFLAGS -std=c++11 \
  -I $ts_dir/lib/include/tree_sitter \
  -D TS_LANG=$ts_lang -D TS_LANG_QUERY_FILENAME="\"${highlights_file}\"" \
  $fuzz_dir/fuzzer.cc $parser_out $scanner_out $ts_dir/libtree-sitter.a \
  -o $out_dir/${ts_lang}_fuzzer

python "${fuzz_dir}/gen-dict.py" "${src_dir}/grammar.json" > "${out_dir}/${ts_lang}.dict"

