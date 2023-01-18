$specs = Get-ChildItem -Path .\test\examples\external\specifications -Filter "*.tla" -Exclude "Reals.tla","Naturals.tla" -Recurse
$specs |% {npx tree-sitter parse -q $_}
