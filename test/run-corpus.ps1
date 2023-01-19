$specs = Get-ChildItem -Path .\test\examples -Filter "*.tla" -Recurse
$specs |% {.\node_modules\.bin\tree-sitter parse -q $_}

