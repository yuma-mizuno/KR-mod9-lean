# Verify the main KR identities and auxiliary coefficient checks, then audit production axioms.
$ErrorActionPreference = "Stop"
$repositoryRoot = Split-Path -Parent $PSScriptRoot

Push-Location -LiteralPath $repositoryRoot
try {
    & python (Join-Path $repositoryRoot "scripts/check-comparator.py")
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

    & python (Join-Path $repositoryRoot "scripts/audit-axioms.py")
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
} finally {
    Pop-Location
}
Write-Host "audit-source: OK"
