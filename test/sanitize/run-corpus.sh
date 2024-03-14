#! /bin/sh
SUCCESS=1
find "test/examples" -type f -name "*.tla" | while IFS= read -r file; do
  echo "$file"
  ./test/sanitize/out/parse_tlaplus "$file" -q
  if [ $? -ne 0 ]; then
    SUCCESS=0
  fi
done
exit $SUCCESS

