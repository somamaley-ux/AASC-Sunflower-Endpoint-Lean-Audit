# AASC Sunflower Endpoint Lean Audit

This repository is a manuscript-faithful Lean A+ audit for **Sunflower Endpoint Rigidity and Kernel-Forced AASC Transfer**. It mechanizes the proof-class spine of the hardened AASC endpoint-transfer argument: the fixed core-petal carrier, the kernel-forced governance layer, the calibrated certificate split, and the local residual-separator discharge.

The strongest truthful claim is:

> Lean checks the AASC endpoint-transfer mechanism that the manuscript uses to route an exact local sunflower countercase into the bounded motif certificate branch, by excluding the calibrated residual separator under kernel-forced local endpoint use.

## What Is Mechanized

- Fixed core-petal residual matching carrier and positive/negative endpoint predicates.
- Core-petal endpoint equivalence as a typed carrier obligation.
- Four-role AASC kernel package: admissibility, standing, reference, irreversibility.
- Target-adequacy-to-kernel governance and no independent same-domain discriminator.
- Finite certificate language, completeness record, and bounded motif certificate branch.
- Objective non-BMF residual branch, separated from merely epistemic failure to find a certificate.
- Exact local countercase use and residual status-work bridge.
- No local endpoint-standing residual separator theorem.
- Kernel-forced transfer from exact local countercase use to `BMF`.
- 31-row A+ theorem-spine obligation ledger.

## Claim Boundary

This is not an AASC-free first-principles derivation of the classical Erdos-Rado sunflower conjecture. It is a machine-checked formalization of the manuscript's AASC endpoint-transfer proof class and its typed governance obligations.

The classical reconstruction burden remains exactly where the manuscript places it: an AASC-free route would need to replace the kernel-forced residual-separator exclusion with a finite certificate-extraction theorem for the bounded motif branch at a calibrated ceiling.

## Verification

Run:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check-sunflower-a-plus-audit.ps1
```

The audit gate builds `SunflowerAASC`, checks `Checks\Axiom\SunflowerAPlusAudit.lean`, and scans the Lean audit surface for prohibited placeholder or escape declarations.

## Repository Map

- `SunflowerAASC/Basic.lean`: fixed carrier, endpoint predicates, local endpoint use, discriminator object.
- `SunflowerAASC/Kernel.lean`: kernel roles, kernel package, governance, denial-cost surface.
- `SunflowerAASC/Certificates.lean`: certificate language, completeness record, BMF, objective non-BMF, residual separator.
- `SunflowerAASC/Transfer.lean`: exact countercase use, residual status work, residual discharge, transfer to BMF.
- `SunflowerAASC/APlusAudit.lean`: 31-row A+ obligation ledger and audit certificate.
- `Checks/Axiom/SunflowerAPlusAudit.lean`: public audit entrypoint.
- `papers/sunflower/`: controlling manuscript snapshot.
- `FORMALIZATION_STATUS.md`, `THEOREM_INVENTORY.md`, `AUDIT_HANDOFF.md`, `RELEASE_STATUS.md`: reader-facing claim, inventory, validation, and release state.
