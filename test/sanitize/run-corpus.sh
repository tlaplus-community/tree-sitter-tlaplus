#! /bin/sh
EXITCODE=0
find "test/examples" -type f -name "*.tla" | while IFS= read -r file; do
  echo "$file"
  ./test/sanitize/out/parse_tlaplus "$file" -q
  RESULT=$?
  if [ "$RESULT" -ne 0 ]; then
    echo "FAILURE: $RESULT"
    EXITCODE=1
  fi
done
exit $EXITCODE

