#! /bin/sh

specs=$(find "test/examples" -name "*.tla")
ncpu=$(command -v nproc > /dev/null && nproc || echo 1)
failures=$(echo "$specs" | xargs -P $ncpu -I {} ./node_modules/.bin/tree-sitter parse -q {})
if test -z "$failures"; then
  exit 0
else
  echo $failures
  exit 1
fi

