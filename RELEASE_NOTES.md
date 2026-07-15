# Release Notes

## v0.3.0 - Generated Blocker-Incidence Paths

This release closes the constructive continuation gap in the earlier
Sunflower proof spine.

For every private blocker coordinate, Lean now defines the next candidates as
the points where its residual edge meets the next minimal blocker. Because the
next blocker hits every residual edge, this subtype is inhabited. Iteration
produces a dependent path for every source and a literal terminal blocker
coordinate for every path. No matching, canonical successor, or AASC
population premise is used.

The new relation-level bridge begins only after this candidate relation has
been generated. It records standing reachability as a subrelation of generated
reachability and isolates four governance obligations: standing-fibre
population, single-valuedness, same-carrier complete-type determination, and
quotient finality. Lean proves the resulting carrier is generated,
choice-independent, injective, and bounded by the traditional seed capacity
`4094`.

The synchronized manuscript removes the former undefined rank-step map,
abstract inherited-form tower, terminal seed constructor atlas, and abstract
seed-carrier assignment. Its hostile audit addresses the continuation report
point by point.

The claim boundary is explicit. Lean fully checks positive path generation and
every consequence of `KernelFaithfulStandingPathBridge`; the direct
sunflower-specific corpus-to-bridge constructor remains paper-level. The
release does not claim an AASC-free combinatorial proof or a fully
unparameterized machine proof of that bridge.

Validation:

- Lean and Mathlib `v4.28.0`;
- 1,056 successful build jobs;
- 42 focused axiom checks;
- no project `axiom`, `sorry`, `admit`, or unsafe escape;
- 34-page PDF with no LaTeX warnings and all fonts embedded;
- publication ZIP hash verification and clean extracted rebuild.

Release assets:

- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint_Generated_Incidence_Edition.pdf`
- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint_Generated_Incidence_Publication_Project.zip`

Validation command:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check-sunflower-a-plus-audit.ps1
```
