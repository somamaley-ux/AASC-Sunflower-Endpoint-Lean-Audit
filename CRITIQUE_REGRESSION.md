# Critique Regression

This file records the checks that prevent the continuation-generation defect
from returning.

## The Global Tower Is Now Source-by-Source

`GeneratedIncidenceTower.NextCoordinate F source` is the subtype of points in
the next minimal blocker that lie in the current source residual. The theorem
`nextCoordinate_nonempty` proves this type is inhabited because the next
blocker hits every edge of the residual family.

The proof therefore distinguishes three types:

- a source blocker coordinate;
- its residual edge; and
- a next blocker coordinate incident with that edge.

No residual edge is identified with a blocker point.

## The Rank Step Is Defined

The former described map `delta_j` is absent. `IncidencePath` is a dependent
inductive type whose constructor stores the source, literal next blocker
coordinate, incidence proof, and tail path. `incidencePath_nonempty` constructs
a path for every source by induction.

Branching is retained. A representative chosen later has no role in proving
the relation inhabited.

## Exclusion Does Not Manufacture Population

`ReachesTerminalCarrier` and `exists_reachesTerminalCarrier` are proved before
`KernelFaithfulStandingPathBridge` appears. The bridge field
`standingReach_generated` forces every governed pair to carry a proof of this
already generated reachability.

AASC can filter or identify generated candidates; it cannot add one.

## Terminal Carrier Is Literal

`IncidencePath.terminalCoordinate` is a point of the minimal blocker of
`terminalFamily`. The endpoint bridge no longer receives an abstract
provenance object and assigns it to a proposed seed carrier.

`standingCarrier_reachable` proves that the selected standing carrier is the
terminal coordinate of a generated path.

## Choice Independence Is Separate From Existence

The bridge fields separate:

- standing-fibre nonemptiness;
- standing-fibre single-valuedness; and
- same-carrier source collision closure.

`standingCarrier_choice_independent` uses single-valuedness only after
nonemptiness. `standingCarrierOf_injective` uses same-carrier type equality and
quotient finality only after the carrier has been constructed.

## Seed Capacity Is Downstream

The terminal blocker receives the traditional combinatorial seed embedding.
Only then does `KernelFaithfulStandingPathBridge.seedCode_injective` compose the
maps and `cell_card_le_4094` count the source cell.

Neither `4094` nor an injective code occurs in path generation or carrier
collision closure.

## Kernel Dependency Is Explicit

The Lake manifest pins
`non-degenerate-construction-kernel-admissibility` at commit
`8b51f035f86f781e5eeb18cbaef8b46e74ed4924`.
`MechanizedKernelImport` translates the fixed Sunflower endpoint into the
upstream regime and imports kernel necessity, fixed-domain closure, uniqueness,
no derivation below, and global synthesis.

## Exact Remaining Boundary

The release does not yet construct `KernelFaithfulStandingPathBridge F cell`
from generated data and the imported corpus alone. The manuscript proves the
four target-specific governance obligations; Lean receives them as structure
fields and checks their consequences.

That is a visible internalization boundary, not a project axiom. The audit
continues to scan for `axiom`, `sorry`, `admit`, and unsafe declarations.

## Claim Boundary

The mathematical kernel dependency is not an optional regime condition: it is
forced by determinate identity, comparison, admissible transformation,
standing-bearing endpoint use, reference, and finality. The formal claim is
still bounded exactly: positive path generation is complete in Lean; the
direct corpus-to-governance constructor is not yet internalized.
