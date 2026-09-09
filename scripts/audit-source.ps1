# Source audit of production proofs and the independent specification.
#   * no `sorry` / `admit` / `axiom` in the production library or in Comparator/Solution.lean;
#   * Comparator/KanadeRussell.lean may contain `sorry` only in `theorem` bodies.
$ErrorActionPreference = "Stop"
$root = Split-Path -Parent $PSScriptRoot

$production = @(Get-ChildItem -Path (Join-Path $root "KanadeRussell") -Recurse -Filter *.lean -ErrorAction SilentlyContinue)
$production += @(Get-ChildItem -Path $root -Filter "KanadeRussell.lean")
$solution = Join-Path $root "Comparator/Solution.lean"
if (Test-Path $solution) { $production += @(Get-Item $solution) }

$forbidden = $production | Select-String `
  -Pattern '^\s*(axiom\b|sorry\b|admit\b)|(:=|\bby)\s+(sorry|admit)\b' -CaseSensitive
if ($null -ne $forbidden -and @($forbidden).Count -gt 0) {
  Write-Host "Forbidden proof escape or custom axiom found:"
  $forbidden | ForEach-Object { Write-Host ("  {0}:{1}: {2}" -f $_.Path, $_.LineNumber, $_.Line.Trim()) }
  exit 1
}

$spec = Join-Path $root "Comparator/KanadeRussell.lean"
$specImports = Select-String -Path $spec -Pattern '^import\s+KanadeRussell'
if ($null -ne $specImports -and @($specImports).Count -gt 0) {
  Write-Host "The trusted specification must not import the production library."
  exit 1
}

Push-Location $root
try {
  $audit = Join-Path $root "KanadeRussell/AxiomAudit.lean"
  if (Test-Path $audit) {
    & python (Join-Path $root "scripts/audit-axioms.py")
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
  }
} finally {
  Pop-Location
}
Write-Host "audit-source: OK"
