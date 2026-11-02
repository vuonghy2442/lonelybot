# build_crosssuit_cert.ps1 -- build the kernel certificate for the cross-suit refutation.
#
#   ForkCertBoard  (board + 17-letter play + corridor + refutations from minimality)
#   ForkCertBase   (the 2308-entry distance table + D / certOK)
#   ForkCertPart0..7  in PARALLEL (the 274 chunk decides)
#   ForkCertMain   (assembly + induction + play_shortest + refutations)
#   ForkCertInv    (inv = 8, table size, equal-rung rows)
#
# Leaf build: the certificate is NOT imported by Orig2.lean (it costs ~400 s
# of parallel elaboration), so `lake build Orig2` stays at its normal job count.
$ErrorActionPreference = 'Stop'
Set-Location 'B:\code\lonelybot\lean-model'
$out = '.lake/build/lib/lean/Orig2'
New-Item -ItemType Directory -Force -Path $out | Out-Null
$log = 'Temp/Cert_axioms_orig2.txt'
if (Test-Path $log) { Remove-Item $log }

# 2026-11-02: the certificate cluster (ForkCert* + ForkEqualRung{Ball,Board,Min})
# was archived to Archive/Cert/ because it is deliberately outside
# `lake build Orig2`.  Restore it first, then rerun this script unchanged:
#   foreach ($f in 'ForkCertBase','ForkCertBoard','ForkCertInv','ForkCertMain',
#                  'ForkCertPart0','ForkCertPart1','ForkCertPart2','ForkCertPart3',
#                  'ForkCertPart4','ForkCertPart5','ForkCertPart6','ForkCertPart7',
#                  'ForkEqualRungBall','ForkEqualRungBoard','ForkEqualRungMin') {
#     git mv "Archive/Cert/$f.lean" "Orig2/Fork/$f.lean" }
if (-not (Test-Path 'Orig2/Fork/ForkCertBoard.lean')) {
  Write-Host 'Certificate cluster lives in Archive/Cert; restore it first (recipe above).'
  exit 1
}

function Step([string]$file, [string]$mod) {
  $t0 = Get-Date
  & lake env lean -o "$out/$mod.olean" "Orig2/Fork/$file"
  if ($LASTEXITCODE -ne 0) { throw "BUILD FAILED: $file" }
  $dt = [int]((Get-Date) - $t0).TotalSeconds
  Write-Host ("{0,-30} {1,5}s" -f $file, $dt)
}

function Check([string]$file) {
  $t0 = Get-Date
  & lake env lean "Orig2/Fork/$file" 2>&1 | Tee-Object -FilePath $log -Append
  if ($LASTEXITCODE -ne 0) { throw "CHECK FAILED: $file" }
  $dt = [int]((Get-Date) - $t0).TotalSeconds
  Write-Host ("{0,-30} {1,5}s" -f $file, $dt)
}

$t0 = Get-Date
Step 'ForkCertBoard.lean' 'ForkCertBoard'
Step 'ForkCertBase.lean'  'ForkCertBase'

$tp = Get-Date
$procs = 0..7 | ForEach-Object {
  Start-Process -PassThru -NoNewWindow -FilePath 'C:\Users\hy\.elan\bin\lake.exe' `
    -ArgumentList 'env','lean','-o',"$out/ForkCertPart$_.olean","Orig2/Fork/ForkCertPart$_.lean" `
    -RedirectStandardOutput "Temp\certpart$_.out" -RedirectStandardError "Temp\certpart$_.err"
}
$procs | Wait-Process
foreach ($i in 0..7) {
  if ((Get-Item "Temp\certpart$i.err").Length -gt 0) { throw "PART $i FAILED: $(Get-Content Temp\certpart$i.err)" }
}
Write-Host ("{0,-30} {1,5}s" -f 'ForkCertPart0..7 (parallel)', [int]((Get-Date) - $tp).TotalSeconds)

Step 'ForkCertMain.lean' 'ForkCertMain'
Check 'ForkCertInv.lean'
Write-Host ("TOTAL WALL: {0} s" -f [int]((Get-Date) - $t0).TotalSeconds)
