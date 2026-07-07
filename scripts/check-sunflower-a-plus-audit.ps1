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

$prohibitedMatches = @()
if (Get-Command rg -ErrorAction SilentlyContinue) {
    $rgArgs = @(
        "-n",
        "--glob",
        "*.lean",
        $prohibitedPattern
    ) + $scanRoots

    $prohibitedMatches = @(& rg @rgArgs)
    if ($LASTEXITCODE -ne 0 -and $LASTEXITCODE -ne 1) {
        throw "Prohibited-token scan failed with exit code $LASTEXITCODE."
    }
} else {
    $leanFiles = foreach ($root in $scanRoots) {
        Get-ChildItem -LiteralPath $root -Recurse -Filter "*.lean" -File
    }
    $prohibitedMatches = @(
        $leanFiles |
        Select-String -Pattern $prohibitedPattern |
        ForEach-Object {
            "$($_.Path):$($_.LineNumber):$($_.Line)"
        }
    )
}

if ($prohibitedMatches.Count -gt 0) {
    $prohibitedMatches | ForEach-Object { Write-Host $_ }
    throw "Prohibited Lean placeholder or escape found in Sunflower audit surface."
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
