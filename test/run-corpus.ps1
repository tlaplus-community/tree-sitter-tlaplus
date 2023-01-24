$specs = Get-ChildItem -Path .\test\examples -Filter "*.tla" -Recurse
$cpuCount = (Get-CimInstance -ClassName Win32_Processor).NumberOfLogicalProcessors
$failures = $specs | ForEach-Object -Parallel {.\node_modules\.bin\tree-sitter parse -q $_} -ThrottleLimit $cpuCount
$failures
exit $failures.length

