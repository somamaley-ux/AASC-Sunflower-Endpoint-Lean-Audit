# Formalization Status

## Current Result

Release `v0.3.0` adds the source-by-source combinatorial construction missing
from the earlier two-track spine. Lean now proves, without a governance or
population premise, that every initial minimal-blocker coordinate has a finite
blocker-incidence path to a literal terminal blocker coordinate.

The checked dependency is now:

```text
minimal blocker and private residual
  -> nonempty residual/next-blocker intersection
  -> nonempty dependent incidence path for every source
  -> populated terminal reachability relation
  -> relation-level governance bridge
  -> unique injective standing carrier
  -> terminal seed embedding in Fin 4094
  -> cell bound 4094.
```

The first four arrows are unconditional finite combinatorics. The governance
bridge is the explicit manuscript-to-Lean boundary. Every arrow after it is
machine-checked.

## Newly Internalized

`GeneratedIncidenceTower.lean` constructs:

- the exact next-coordinate subtype;
- its nonemptiness from the hitting property of the next blocker;
- a dependent inductive path retaining all branches;
- terminal family and terminal carrier projection;
- source-to-terminal reachability and its left-totality; and
- no-sunflower transport through the complete tower.

`GeneratedSeedCapacity.lean` constructs:

- cells of initial private-witness carriers;
- the relation-level `KernelFaithfulStandingPathBridge`;
- the unique standing terminal carrier after bridge population;
- proof that this carrier is generated and choice-independent;
- same-carrier source injectivity from quotient finality; and
- the composed `Fin 4094` seed code and cell bound.

## Exact Remaining Boundary

Lean does not yet define

```lean
standingPathBridge_of_generatedData :
  KernelFaithfulStandingPathBridge F cell
```

directly from the imported corpus machinery and a terminal no-sunflower
countercase. Its proof must instantiate standing-fibre population,
single-valuedness, same-carrier complete-type determination, and quotient
finality without assuming an injective carrier map, finite code, support-fibre
bound, or endpoint theorem.

The manuscript supplies that AASC exhaustion and impossibility argument. The
Lean structure is a modular internalization boundary, not a global axiom and
not a predicate selecting only some families.

## Legacy Endpoint Transfer

The previous `ImportedManuscriptKernelGovernedPopulationTheorem` route remains
available. It still checks the downstream conversion from the target-specific
population object to fixed identity, support-fibre closure, a genuine
three-petal sunflower, and `|F| <= 8384512^n`. Its exact-strength equivalence
continues to prevent the endpoint-strength import from being advertised as an
independently weaker lemma.

## Claim Classification

The manuscript's kernel dependency is not optional: determinate family
identity, comparison, licensed transformation, standing-bearing endpoint use,
and irreversible report finality instantiate the kernel necessities. The Lean
status is nevertheless stated separately and exactly.

This release does not claim:

- an AASC-free conventional proof;
- an unparameterized Lean constructor for the relation-level governance
  bridge; or
- an independent Mathlib reconstruction of the complete corpus proof.

## Audit State

- Lean/Mathlib `v4.28.0`;
- 1,056 successful build jobs;
- 42 focused axiom checks;
- no live `axiom`, `sorry`, `admit`, or unsafe declaration on the audit surface;
- audited dependencies limited to standard principles such as `propext`,
  `Classical.choice`, and `Quot.sound`.

The synchronized publication is a visually verified 34-page PDF with a
hash-verified, clean-rebuilding source archive.
