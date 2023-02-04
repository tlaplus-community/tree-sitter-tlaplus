#! /bin/sh

specs=$(find "test/examples" -name "*.tla")
ncpu=$(($# > 0 ? $(command -v nproc > /dev/null && nproc || echo 1) : 1))
echo "Concurrent parser count: $ncpu"
failures=$(echo "$specs" | xargs -P $ncpu -I {} ./node_modules/.bin/tree-sitter parse -q {})
if test -z "$failures"; then
  exit 0
else
  echo "$failures"
  exit 1
fi

