$specs = Get-ChildItem -Path .\test\examples -Filter "*.tla" -Recurse
$failures = $specs |% {.\node_modules\.bin\tree-sitter parse -q $_}
$failures
exit $failures.length

