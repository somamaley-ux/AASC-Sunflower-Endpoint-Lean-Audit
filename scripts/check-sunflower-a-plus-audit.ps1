Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$prohibitedPattern = "^\s*(axiom|unsafe)\b|\b(sorry|admit)\b"
$scanRoots = @(
    "SunflowerAASC",
    "Checks\Axiom"
)

$auditFiles = @(
    "Checks\Axiom\SunflowerAPlusAudit.lean"
)

foreach ($auditFile in $auditFiles) {
    if (-not (Test-Path -LiteralPath $auditFile -PathType Leaf)) {
        throw "Missing Sunflower A+ audit file: $auditFile"
    }
}

Write-Host "Lean toolchain:"
Get-Content -LiteralPath "lean-toolchain"

$rgArgs = @(
    "-n",
    "--glob",
    "*.lean",
    $prohibitedPattern
) + $scanRoots

$prohibitedMatches = & rg @rgArgs
if ($LASTEXITCODE -eq 0) {
    $prohibitedMatches | ForEach-Object { Write-Host $_ }
    throw "Prohibited Lean placeholder or escape found in Sunflower audit surface."
}
if ($LASTEXITCODE -ne 1) {
    throw "Prohibited-token scan failed with exit code $LASTEXITCODE."
}
Write-Host "No live prohibited declarations or placeholders found in Sunflower audit surface."

lake build SunflowerAASC
if ($LASTEXITCODE -ne 0) {
    throw "Lake build failed for SunflowerAASC."
}
foreach ($auditFile in $auditFiles) {
    lake env lean $auditFile
    if ($LASTEXITCODE -ne 0) {
        throw "Lean audit failed for $auditFile."
    }
}
