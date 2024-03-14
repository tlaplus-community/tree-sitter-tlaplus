#! /bin/sh
EXITCODE=0
find "test/examples" -type f -name "*.tla" | while IFS= read -r file; do
  echo "$file"
  ./test/sanitize/out/parse_tlaplus "$file" -q
  if [ $? -ne 0 ]; then
    echo "FAILURE: $?"
    EXITCODE=1
    ./test/sanitize/out/parse_tlaplus "$file"
  fi
done
exit $SUCCESS

