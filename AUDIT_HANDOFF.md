# Audit Handoff

## Current Result

The repository is a standalone Lean A+ audit archive for the hardened Sunflower AASC endpoint-transfer manuscript. The public Lean surface builds locally and the audit script checks the theorem-spine entrypoint.

The latest light manuscript hardening was scanned against the previous repository snapshot. The theorem dependency ladder stayed stable. The Lean surface was updated only where the manuscript added named audit surfaces: the sunflower threshold definition and the AASC consequence-layer recap.

## Validation Command

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check-sunflower-a-plus-audit.ps1
```

The script performs three checks:

- verifies the selected Lean toolchain,
- scans the Lean audit surface for live `axiom`, `sorry`, `admit`, or `unsafe` declarations,
- builds `SunflowerAASC` and checks `Checks\Axiom\SunflowerAPlusAudit.lean`.

The scanner uses `rg` when available and falls back to native PowerShell scanning on GitHub Actions runners.

## Reader-Facing Interpretation

The mechanization should be described as a manuscript-faithful AASC endpoint-transfer audit. It is strong because Lean checks the structural proof objects, kernel-forced governance bridge, calibrated residual branch, local endpoint-use discharge, and 31-row obligation ledger.

It also now carries explicit anchors for the threshold framing and the fixed-domain consequence-layer recap introduced by the hardened manuscript.

It should not be described as a conventional standalone proof of the classical sunflower conjecture independent of AASC. The AASC-free reconstruction burden remains a separate route.

## Release State

The repository is prepared for the `v0.1.0` GitHub release from the verified hardened-manuscript commit. The release assets are the manuscript PDF and source ZIP under `papers/sunflower/`.
