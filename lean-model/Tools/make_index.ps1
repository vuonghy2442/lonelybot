# Tools/make_index.ps1 - the house theorem index generator
#
# Regenerates THEOREM_INDEX.txt: one line per declaration,
#     path:line  NAME :: full signature (joined to one line)
# covering Orig2/, Orig/, Archive/ (retired cards stay searchable), and
# any other live roots present.  The index is a GENERATED artifact
# (gitignored); regenerate after landing rows:
#     pwsh Tools/make_index.ps1
# Then shape-search - e.g. the recipe hunt that motivated this tool:
#     Select-String THEOREM_INDEX.txt -Pattern 'SwappableIn'
#     Select-String THEOREM_INDEX.txt -Pattern 'tabToFound' |
#       Where-Object { $_.Line -match 'SwappableIn' }

$ErrorActionPreference = 'Stop'
$roots = @('Orig2', 'Orig', 'Archive', 'Klondike', 'Witnesses') | Where-Object { Test-Path $_ }
$declRegex = '^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_''!?]*)'
$out = [System.Collections.Generic.List[string]]::new()
foreach ($dir in $roots) {
  foreach ($file in Get-ChildItem $dir -Filter *.lean -Recurse) {
    $lines = Get-Content $file.FullName
    for ($i = 0; $i -lt $lines.Count; $i++) {
      if ($lines[$i] -notmatch $declRegex) { continue }
      $name = $Matches[1]
      $sig = [System.Collections.Generic.List[string]]::new()
      $j = $i
      while ($j -lt $lines.Count) {
        $l = $lines[$j]
        if ($l -match ':=') {
          if ($j -eq $i) { $sig.Add([regex]::Split($l, ':=', 2)[0]) }
          break
        }
        $sig.Add($l)
        $j++
      }
      $rel = $file.FullName.Substring((Get-Location).Path.Length + 1)
      $joined = (($sig -join ' ') -replace '\s+', ' ').Trim()
      $out.Add("$($rel):$($i + 1)  $name :: $joined")
    }
  }
}
Set-Content -Path THEOREM_INDEX.txt -Value $out -Encoding utf8
"wrote THEOREM_INDEX.txt: $($out.Count) declarations from: $($roots -join ', ')"
