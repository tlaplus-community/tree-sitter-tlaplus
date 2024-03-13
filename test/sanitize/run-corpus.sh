#! /bin/sh
find "test/examples" -type f -name "*.tla" | while IFS= read -r file; do
    echo "$file"
    ./test/sanitize/out/parse_tlaplus "$file" -q
done

