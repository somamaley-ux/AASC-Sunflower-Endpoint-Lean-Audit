# Formalization Status

## Status

This project has reached the local A+ audit gate for the Sunflower AASC endpoint-transfer manuscript. The Lean surface is proof-class faithful: it formalizes the typed objects and dependency ladder used by the hardened manuscript, and it exposes a single public audit entrypoint.

## Controlling Source Snapshot

The mechanization follows the PDF-aligned hardened manuscript:

- `papers/sunflower/main.tex`
- `papers/sunflower/Sunflower_Endpoint_Rigidity_and_Kernel_Forced_AASC_Transfer.pdf`

The older `Sunflower_AASC_Endpoint_Transfer_Overleaf.zip` was inspected first. The PDF-adjacent source is materially stronger and is the controlling source used here because it includes the calibrated certificate language, local endpoint use, objective-vs-epistemic BMF failure, and kernel-denial cost refinements.

## Mechanized Claim

The project machine-checks the following AASC endpoint-transfer spine:

1. The sunflower endpoint is represented on a fixed core-petal residual matching carrier.
2. Exact local countercase use is not raw objecthood; it is endpoint work on the fixed carrier.
3. Target adequacy on that nondegenerate endpoint act forces the four-role kernel.
4. A calibrated certificate language splits the local countercase branch into BMF support or objective non-BMF residual status work.
5. Local residual status work yields an independent same-domain endpoint-status discriminator.
6. Kernel-forced endpoint governance excludes that discriminator.
7. Therefore the calibrated residual separator is discharged, and the local countercase route transfers to the bounded motif certificate branch.

## Explicit Boundary

This repository does **not** claim to mechanize a conventional AASC-free proof of the Erdos-Rado sunflower conjecture from first-principles extremal combinatorics.

It does claim to mechanize, without live `axiom`, `sorry`, `admit`, or `unsafe` declarations in the audit surface, the manuscript's AASC endpoint-transfer mechanism and its A+ theorem-spine ledger.

## Verification

Verified locally with:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check-sunflower-a-plus-audit.ps1
```

The gate builds `SunflowerAASC`, checks `Checks\Axiom\SunflowerAPlusAudit.lean`, and scans the Lean audit surface for prohibited placeholder or escape declarations.
