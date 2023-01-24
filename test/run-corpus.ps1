$specs = Get-ChildItem -Path .\test\examples -Filter "*.tla" -Recurse
$failures = $specs | ForEach-Object -Parallel -ThrottleLimit 2 {.\node_modules\.bin\tree-sitter parse -q $_}
$failures
exit $failures.length

