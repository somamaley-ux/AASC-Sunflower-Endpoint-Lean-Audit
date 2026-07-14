# Release Notes

## v0.2.0 - Mechanized-Kernel Two-Track Closure

This release publishes the clean Lean proof spine for **Two-Track Closure for
the Three-Petal Sunflower Endpoint**.

The release now imports the standalone mechanization of **Non-Degenerate
Construction and the Kernel of Admissibility**, pinned at commit
`8b51f035f86f781e5eeb18cbaef8b46e74ed4924`. The new typed bridge translates
the Sunflower endpoint into the upstream construction regime and certifies the
kernel package, fixed-domain closure and uniqueness, no derivation below the
kernel, no faithful lower generator, and global synthesis.

Lean then checks the complete route from the manuscript's population theorem
to fixed inherited identity, the canonical support-fibre bound, the dense
high-rank source, a genuine three-petal sunflower, and the endpoint
`|F| <= 8384512^n`.

The external boundary is exactly manuscript Theorem 6.2's finite
profile/role/slot population conclusion. There is no additional Lean-only
support-fibre premise. The exact-strength equivalence proves that the imported
theorem is endpoint-strength rather than a weakened restatement.

The mathematical claim is over every non-degenerate determinate finite-family
regime. AASC identifies the necessity conditions of that domain; it is not an
optional qualifier on selected families. The Lean population proof object is
the explicit internalization boundary for manuscript Theorem 6.2.

The repository declares no project-specific Lean axioms and contains no live
`sorry`, `admit`, or `unsafe` escape. The audit completes 1,050 build jobs and
25 focused axiom checks. It does not claim an AASC-free conventional analogue
or an independent Mathlib reconstruction of the population theorem.

The Lake workspace uses the short dependency directory `p/` so the pinned
kernel modules also compile on Windows runners without path-length failure.

Release assets:

- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint.pdf`
- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint_Source.zip`

Validation:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check-sunflower-a-plus-audit.ps1
```
