# Formalization Status

## Source Snapshot

The mechanization follows the PDF-aligned hardened manuscript:

- `papers/sunflower/main.tex`
- `papers/sunflower/Sunflower_Endpoint_Rigidity_and_Kernel_Forced_AASC_Transfer.pdf`

The older `Sunflower_AASC_Endpoint_Transfer_Overleaf.zip` was inspected first, but the PDF-adjacent source is materially stronger and contains the calibrated certificate-language/local-endpoint-use refinements used here.

## Mechanized Surface

This is an A+ endpoint-transfer mechanization, not an AASC-free classical sunflower proof. It formalizes:

- fixed core-petal residual matching carrier,
- target adequacy and four-role kernel package,
- kernel-forced governance and no independent same-domain discriminator,
- finite certificate language and completeness record,
- BMF support branch and objective non-BMF residual branch,
- exact local countercase use,
- residual status-work bridge,
- discharge of the calibrated residual separator,
- transfer from local countercase use to BMF support under the fixed branch split,
- 31-row theorem-spine obligation ledger.

## Verification

Verified locally with:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check-sunflower-a-plus-audit.ps1
```

The gate builds `SunflowerAASC`, checks `Checks\Axiom\SunflowerAPlusAudit.lean`, and scans the Lean audit surface for prohibited placeholder or escape declarations.
