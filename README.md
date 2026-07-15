# Three-Petal Sunflower Endpoint: Generated Incidence and Structural Closure

[![Lean audit](https://github.com/somamaley-ux/AASC-Sunflower-Endpoint-Lean-Audit/actions/workflows/lean.yml/badge.svg)](https://github.com/somamaley-ux/AASC-Sunflower-Endpoint-Lean-Audit/actions/workflows/lean.yml)

This repository is the Lean companion to **Two-Track Closure for the
Three-Petal Sunflower Endpoint: Generated Blocker-Incidence Paths and
Kernel-Governed Seed Capacity**. The finite combinatorial construction is the
foreground proof track. AASC enters only after combinatorics has populated the
terminal candidate relation.

## Proof at a Glance

1. **Finite generation.** Minimal blockers supply private edges and residual
   families. For a current blocker coordinate `x`, the next candidates are the
   points in `residual x ∩ nextMinimalBlocker`.
2. **Path population.** The next blocker hits every residual edge, so every
   successor set is nonempty. Lean iterates this relation as a dependent path
   type and proves that every initial coordinate reaches at least one literal
   terminal blocker coordinate.
3. **Structural governance.** AASC classifies only those generated reaches. In
   each fixed comparison cell, the manuscript proves standing-fibre
   population, choice independence, same-carrier complete-type equality, and
   collision impossibility.
4. **Return to finite combinatorics.** The unique standing carrier map embeds a
   cell into the terminal blocker. The traditional seed theorem embeds that
   blocker into `Fin 4094`; the existing finite-code and link machinery yields
   the base-`8384512` endpoint.

No Hall matching, canonical successor, residual-to-coordinate identification,
seed constructor atlas, or universal numerical role registry is used.

## Result and Scope

The manuscript states the endpoint

```text
NoSunflower 3 F -> |F| <= 8384512^n.
```

The kernel handoff is not an elective predicate restricting uniform families.
The fixed family, identity, comparison, licensed transformation, standing-
bearing endpoint use, and report finality instantiate the kernel necessities
of Admissibility, Standing, Reference, and Irreversibility.

That mathematical dependency claim and the Lean internalization status are
different questions. This release does not blur them: the generated path tower
is fully constructed in Lean, while the sunflower-specific corpus proof of the
relation-level governance bridge remains an explicit structure boundary.

## Generated Combinatorial Track

`V2.GeneratedIncidenceTower` formalizes the missing source-by-source step.
For `source` in the current minimal blocker it defines:

```lean
NextCoordinate F source =
  {target in minimalBlocker (residualFamily F) //
    target.val in residual F source}
```

The module proves:

- `nextCoordinate_nonempty`: the next blocker meets the current residual;
- `incidencePath_nonempty`: every source has a dependent path to cutoff;
- `ReachesTerminalCarrier`: the source-to-terminal relation;
- `exists_reachesTerminalCarrier`: every left fibre is populated;
- `terminalFamily_noSunflower`: residualization preserves the countercase; and
- `terminalCoordinate`: every path ends at a literal terminal blocker point.

All branching is retained. Classical choice is used only downstream to display
a representative of a relation already proved nonempty.

## Relation-Level Structural Handoff

`V2.GeneratedSeedCapacity.KernelFaithfulStandingPathBridge` begins after path
population. Its fields state:

- every standing pair is generated reachability;
- every source has a standing terminal reach;
- one source has at most one standing terminal carrier;
- a shared carrier determines one AASC quotient type; and
- quotient finality returns that equality to literal source identity.

Lean then proves:

- `standingCarrier_reachable`;
- `standingCarrier_choice_independent`;
- `standingCarrierOf_injective`;
- injectivity of the composed seed code; and
- `cell_card_le_4094`.

AASC supplies no path and no numeral. Combinatorics supplies no endpoint
collision theorem.

## Formalization Boundary

The current development does **not** yet construct an unparameterized
`KernelFaithfulStandingPathBridge` directly from the imported corpus machinery.
The manuscript proves its sunflower-specific fields; Lean checks their exact
typed consequences. No support-fibre bound, injective code, one-occupant-per-
token premise, or endpoint estimate is hidden in the generated path theorem.

The older endpoint-strength boundary
`ImportedManuscriptKernelGovernedPopulationTheorem` remains in the repository
for correspondence and downstream audit. The generated-incidence modules now
isolate the strictly smaller conceptual handoff that a future internalization
must construct.

The release therefore claims neither an AASC-free conventional proof nor a
fully unparameterized machine proof of the corpus-to-governance bridge.

## Main Anchors

- `V2.SelectedCoordinateReduction.family_card_le_k_mul_residualFamily`
- `V2.GeneratedIncidenceTower.nextCoordinate_nonempty`
- `V2.GeneratedIncidenceTower.incidencePath_nonempty`
- `V2.GeneratedIncidenceTower.exists_reachesTerminalCarrier`
- `V2.GeneratedIncidenceTower.terminalFamily_noSunflower`
- `V2.GeneratedSeedCapacity.KernelFaithfulStandingPathBridge.standingCarrier_reachable`
- `V2.GeneratedSeedCapacity.KernelFaithfulStandingPathBridge.standingCarrier_choice_independent`
- `V2.GeneratedSeedCapacity.KernelFaithfulStandingPathBridge.standingCarrierOf_injective`
- `V2.GeneratedSeedCapacity.KernelFaithfulStandingPathBridge.cell_card_le_4094`
- `V2.ManuscriptKernelTransfer.sunflower_of_importedManuscriptKernelGovernedClosure`
- `V2.ManuscriptKernelTransfer.nonempty_importedManuscriptPopulationTheorem_iff_endpointBound`

## Kernel Dependency

The standalone mechanized kernel repository is pinned at commit
`8b51f035f86f781e5eeb18cbaef8b46e74ed4924`.
`V2.MechanizedKernelImport` constructs its `ConstructionRegime`, kernel
package, fixed-domain closure, uniqueness, no-derivation-below result, and
global synthesis certificate for the fixed Sunflower endpoint route.

## Validation

The release uses Lean and Mathlib `v4.28.0`.

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check-sunflower-a-plus-audit.ps1
```

Verified locally:

- complete build: 1,056 jobs;
- 42 focused `#print axioms` checks;
- no live project `axiom`, `sorry`, `admit`, or unsafe declaration; and
- only standard Lean/Mathlib principles such as `propext`,
  `Classical.choice`, and `Quot.sound` on the audited anchors.

## Manuscript

The synchronized publication snapshot is under [`papers/sunflower`](papers/sunflower):

- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint_Generated_Incidence_Edition.pdf`
- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint_Generated_Incidence_Publication_Project.zip`

The 34-page manuscript and its source package use the same dependency order as
the Lean types: generated incidence first, structural endpoint governance
second, numerical readout last.
