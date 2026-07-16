# The AASC-Combinatorics Endpoint Bridge

[![Lean audit](https://github.com/somamaley-ux/AASC-Sunflower-Endpoint-Lean-Audit/actions/workflows/lean.yml/badge.svg)](https://github.com/somamaley-ux/AASC-Sunflower-Endpoint-Lean-Audit/actions/workflows/lean.yml)

This repository is the Lean companion to **The AASC-Combinatorics Endpoint
Bridge: An Integrated Hybrid Closure for the Three-Petal Sunflower Theorem**.
The finite combinatorial construction is the
foreground proof track. It generates the blockers, residual paths, collision
geometry, finite dispositions, reduction certificates, and quantitative data.
Once those generated carriers are determinate and non-degenerate, kernel
necessity already places them under AASC governance. The proof invokes the
resulting AASC exhaustion and impossibility consequences only at the terminal
closeout. AASC is invoked late, but it is not activated late. The theorem is
the composition of these two complete components.

## Proof at a Glance

1. **Finite generation.** Minimal blockers supply private edges and residual
   families. For a current blocker coordinate `x`, the next candidates are the
   points in the intersection of `residual x` and `nextMinimalBlocker`.
2. **Path population.** The next blocker hits every residual edge, so every
   successor set is nonempty. Lean iterates this relation as a dependent path
   type and proves that every initial coordinate reaches at least one literal
   terminal blocker coordinate.
3. **True comparison cells.** Lean forms the exact fibre in which canonical
   support, finite constraint profile, and forced AASC role are all fixed.
4. **Layered private-witness exhaustion.** Distinct sources have different
   complete endpoint-incidence roles. The difference is either a distinct
   rank-lowered residual parent or a distinct derived `Fin k` slot inside one
   residual fibre. Same parent and same slot already imply literal equality.
5. **Forced Venn witness.** If selected-coordinate deletion is cross-free at
   every rank, the family has size at most `k^n`. Any larger sunflower-free
   countercase therefore populates an explicit outgoing-cross tower witness.
6. **Pair-local collision reduction.** Equality of the generated rank-one seed
   makes the two concrete deletion paths meet. Lean localizes the collision to
   their first merge and exhausts it into a bounded local slot, a different
   finite residual Venn code, or unequal residual parents in one Venn cell.
7. **Local strict rank descent.** The same-Venn-parent case carries an explicit
   lower-rank candidate: an inside/outside split or a named occupied-petal
   component. This decomposes the colliding residuals; it does not by itself
   reconstruct the whole dense fibre.
8. **Rank-compatible residual reconstruction.** Every residual is injectively
   rebuilt from its disjoint component tuple, with exact additive rank. Lean
   separates unrestricted product fullness, graded fullness at the required
   total rank, and a genuinely missing same-rank tuple. With two matching
   petals, unrestricted fullness is mechanically impossible because the tuple
   taking both whole petals has twice the required rank.
9. **Graded convolution and genuine gates.** Every fixed-rank component slice
   is sunflower-free and inherits the lower-rank estimate. Each occupied rank
   profile costs one parent-rank power, while the whole graded branch has the
   explicit overhead `(r + 2)^k`. A genuine same-rank omission assigns every
   nonexceptional residual to an injective binary reconstruction whose two
   pieces are positive, strict lower rank, and add exactly to the parent rank.
   These estimates are also useful to a separately formulated autonomous
   conventional strengthening, but that stronger proof class is not
   load-bearing here.
10. **Post-exhaustion structural handoff.** The generated alternatives enter
   the finite disposition tree. Strict splits recurse; bounded and lower-rank
   cases are discharged; and AASC impossibility closes any surviving terminal
   branch. Only that quotient-stable endpoint crosses the proved equivalence.
   AASC does not turn a many-to-one residual map into an injection. Any
   autonomous conventional replacement of the terminal theorem would be a
   distinct strengthening, not completion of this proof.

No canonical successor, residual-to-coordinate identification, seed
constructor atlas, or universal numerical role registry is used. Hall's
finite theorem remains an exact independent diagnostic of generated role
occupancy. The fixed-cell composition derives Hall from a separately proved
collision law rather than taking Hall as a governance premise.

## Result and Scope

The manuscript states the endpoint

```text
NoSunflower 3 F -> |F| <= 8384512^n.
```

Kernel governance is not an elective predicate restricting uniform families.
The fixed family, identity, comparison, licensed transformation, standing-
bearing endpoint use, and report finality instantiate the kernel necessities
of Admissibility, Standing, Reference, and Irreversibility.

Kernel necessity is the source of AASC authority; kernel-faithful corpus
exhaustion is the method that derives its fixed-domain consequences. The
fixed-domain layer is therefore not a second optional hypothesis. It also does
not generate the Sunflower-specific witnesses: those remain finite
combinatorics.

The manuscript's AASC proof mode and its endpoint equivalence are closed. The
triangle regression refutes only a premature raw-Hall implementation of the
bridge. It does not refute the post-exhaustion equivalence: the triangle is
assigned to bounded charge before terminal transfer.

Lean formalizes the combinatorial and proof-theoretic component at its natural
boundary: the generated path tower, disposition recursion, and generic
terminal-closeout implication. The manuscript proves the generated five-way
collision classification and literal reduction certificates at their natural
boundary. The typed import joins these completed components. Lean then
constructs the kernel-necessity packet, removes the attempted
independent-authorizer branch, derives the four-role closeout, and obtains
fixed identity and the endpoint. Local same-parent multiplicity is
closed, a dense countercase generates an explicit outgoing-cross witness, and
every same-code collision has a concrete first merge. The triangle regression
confirms that genuine many-to-one residualization occurs and lands in the
bounded-charge branch.

`MergeDispositionClosure` proves the local bounded/separated/sunflower/local-
split ledger. `RankCompatibleProductGate` corrects the product exhaustion so a
wrong-total-rank tuple cannot masquerade as a useful compatibility failure.
`GradedProductConvolution` proves the fixed-rank slices sunflower-free and
bounds the graded branch by `(r + 2)^k * base^(r + 1)`. In the genuine
same-rank-missing branch, Lean constructs a rank-spending gate and an injective
strict binary reconstruction, with at most one full-rank exception per gate.
`RankWeightedMergeCharging` proves closure from its older, stronger
`RankUniformMissingGateChargingSource`, but that source is now recognized as a
sufficient over-approximation because it asks for charges even on wrong-rank
missing tuples. These modules are retained as support for a possible autonomous
conventional strengthening. They are not part of the dependency chain of the
integrated theorem. Standing remains downstream of complete role fulfillment
rather than a separately populated input.

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

## Forced Terminal Kernel Governance

`V2.GeneratedTerminalKernelGovernance` removes any optionality from the kernel
handoff. It packages each generated terminal incidence with its source,
literal terminal locus, and generation proof, then proves:

- every source has such an incidence;
- the source/locus identity is injective;
- the source remains indispensable through its private witness;
- the terminal three-petal carrier is nondegenerate at every base rank;
- the terminal family remains in the transported no-sunflower branch; and
- every generated terminal incidence receives all four kernel roles from the
  forced endpoint machinery.

Thus kernel governance is a proved consequence of the generated determinate
nondegenerate endpoint, not a predicate imposed on selected families.

## Complete Role Refinement

`V2.CompleteRoleRefinement` separates coarse role labels from complete
identity-bearing endpoint content. It proves:

- complete endpoint-incidence role equality implies literal source equality;
- every distinct private witness is tensor-active and cannot be endpoint skin;
- every distinction changes the residual parent or the bounded local slot;
- the pair `(residual parent, slot)` is an injective raw-identity code; and
- terminal complete-reference preservation is equivalent to the corresponding
  exclusion/injectivity statement.

Consequently the local occupancy problem is closed without an AASC-generated
population premise. Distinct residual-parent tensor profiles are genuine
generated content and enter the disposition-and-terminal-closeout architecture
rather than being counted as multiple occupants of one literal role.

## Outgoing-Cross Population

`V2.OutgoingCrossTower` supplies a global generated witness. It recursively
tracks selected-coordinate residual families and proves that a completely
cross-free tower has at most `k^n` edges. Therefore any sunflower-free family
above `base^n`, for `base >= k`, inhabits an explicit finite
`OutgoingCrossTowerWitness` locating a Venn interference at some rank.

This supplies the global obstruction independently of the newer pair-local
reduction. It also records useful data for any separately stated autonomous
conventional strengthening. Such a strengthening is outside the theorem proved
here and does not reopen the AASC endpoint closeout.

## Generated Residual-Parent Exhaustion

`V2.ResidualParentExhaustion` now performs the finite population work before
the AASC terminal closeout is invoked:

- every private-witness load is exactly a different local `Fin k` slot or a
  different residual parent;
- private residualization generates a literal rank-one terminal carrier;
- the rank-one three-petal seed has two positions;
- its product with the proved local `Fin 3` slot has six positions and embeds
  into the manuscript's 4094-slot tensor-profile reservoir; and
- equality of the generated profile forces any surviving load into the
  distinct residual-parent tensor branch.

`threePetalBoundedLoadExhaustionOfGeneratedAuthorizerRoute` then lets the
fixed-domain no-independent-authorizer theorem eliminate that final branch and
constructs the complete bounded-load object consumed by the endpoint proof.
The route premise contains no injective code, cardinal bound, Hall inequality,
or endpoint conclusion. Its rank-uniform construction is nevertheless audited
at exact strength:
`nonempty_denseThreePetalGeneratedAuthorizerRouteSource_iff_endpointBound`
proves it equivalent to the endpoint. That equivalence is the checked transfer
correspondence; it is not a refutation of the AASC solution and is not used as
a combinatorial generator. The controlling proof instead reaches the imported
AASC closeout only after the finite disposition branches have been discharged.

## Pair-Localized Reference Divergence

`V2.PairLocalizedReferenceDivergence` replaces the global residual-parent
label with a concrete first-merge analysis. It proves:

- equal generated terminal seeds force two distinct generated paths to merge;
- every such pair has an inductive `PairMergeWitness` at its first common
  deletion coordinate;
- the second-level residual-overlap code lies in `Finset (Fin 3)`, an
  eight-value finite alphabet;
- a one-step merge is exhausted by a bounded local slot, unequal Venn codes,
  or unequal residual parents with equal Venn code; and
- the equal-code unequal-parent case carries `SameVennParentRankSplit`, giving
  either a strict inside/outside split or a named occupied-petal component
  whose cardinality is strictly below the parent residual rank on both sides.

This is intentionally the local merge ledger. The global cardinal consequence
comes from the integrated disposition, terminal closeout, and endpoint
assembly.
`V2.MergeDispositionClosure` makes that qualification explicit and proves the
triangle belongs to the bounded-charge branch. `V2.RankCompatibleProductGate`
then replaces the coarse full/missing split with the exhaustive unrestricted-
full, graded-full, or same-rank-missing ledger. `V2.GradedProductConvolution`
proves that every occupied rank-profile fibre is recursively bounded and
isolates the finite `(r + 2)^k` profile overhead. These latter modules also
support a distinct autonomous conventional strengthening; they are not
load-bearing in the integrated theorem.

`V2.QuotientCoverageRigidity` audits quotienting before structural discharge.
It
proves that any terminal equivalence preserving every load-bearing edge-
incidence probe is equality on minimal-blocker source coordinates. It also
packages this deliberately premature formulation as
`UndischargedCoverageCarrierBridge` and proves that its induced source-to-
terminal coordinate map is injective. This is not the manuscript's proved
post-exhaustion equivalence. Duplicate histories over one source may still
quotient-collapse, and coverage-active collisions first enter the AASC
disposition ledger. The triangle cannot inhabit the undischarged bridge because
its two colliding roots carry different private-edge tensors; it instead enters
the already constructed bounded-charge branch before terminal transfer. The
module also
proves that any subset of the cardinality-minimal blocker which still hits
every original edge is the whole minimal blocker. Thus metric non-primitivity
may remove duplicate paths or inert presentations attached to one source, but
it cannot identify two indispensable blocker points while retaining an actual
point blocker. A non-skin source collision must still be charged, split,
sunflower-producing, or reconstructed at lower rank.
Equivalently, no source coordinate's coverage contains another's: the private
edge profiles form an antichain. Therefore a carrier-class coverage number of
one forces one underlying source after duplicate histories are removed.

`V2.ExplicitReductionPotential` now states the controlling post-exhaustion
proof mode directly. `endpoint_of_exhaustion_and_terminalCloseout` proves the
endpoint from the finite generated disposition tree once AASC exhaustion and
impossibility settle every terminal package. Raw blocker sources are not sent
through an injective terminal map. Splits reconstruct from strictly smaller
packages, bounded and lower-rank branches are discharged before transfer, and
only the surviving quotient-stable endpoint crosses the AASC/combinatorics
equivalence. The rank-profile and overlap modules below are non-load-bearing
explorations of a distinct autonomous conventional strengthening.

## Root-Authentic Scope Correspondence

`V2.RootAuthenticScopeCorrespondence` encodes the current manuscript's
root-to-seed handoff at its exact strength. `RootAuthenticScopeSeedClosure`
contains a generated root-to-seed relation, totality for every source root,
and right-uniqueness at each literal terminal seed coordinate. Lean derives
the selected `rootSeedMap`, proves it generated, and proves it injective.

The module also proves two exact-strength equivalences

- `nonempty_rootAuthenticScopeSeedClosure_iff_reachableRoleHall`; and
- `nonempty_rootAuthenticScopeSeedClosure_iff_standingPathBridge`.

Thus the root-authentic vocabulary faithfully describes the desired crossing,
but does not make it weaker than Hall occupancy or the earlier standing-path
bridge. Kernel governance of every generated determinate nondegenerate
incidence is already unconditional. Right-uniqueness of the terminal root
reference is a downstream equivalent readout, not the controlling proof
mechanism. The manuscript's completed five-way witness-and-certificate theorem
enters through the typed interface instead.

## Explicit Reduction Potential

`V2.ExplicitReductionPotential` compiles the accepted manuscript's new finite
reduction surface. It defines concrete countercase packages, the four-entry
lexicographic potential, endpoint-faithful finite splits, direct closeout
certificates, certified derivations, well-founded terminalization, and the
terminality of a reduction-minimal countercase. This closes the manuscript's
ordinary recursion bookkeeping without adding a population, Hall, code, or
endpoint premise.

## Expanded Terminal Role Occupancy

`V2.TerminalRoleOccupancyCloseout` now expands the terminal AASC closeout into
the proof components used by the manuscript:

- `CertifiedTerminalExit` separates the four semantic roles from lower-rank
  and scope-changing certificate exits;
- `CertifiedTerminalExit.impossible` proves that certificate terminality
  excludes every non-skin exit;
- `TerminalRoleOccupancyExhaustion.role_injective` derives fixed-role
  uniqueness from bivalent skin/non-skin exhaustion, skin finality, and
  terminality rather than assuming injectivity;
- `AASCFourRoleIdentityPopulation` exposes skin, bounded certificate, tensor
  split, and sunflower as the complete same-identity ledger;
- `CertifiedAASCFourRoleBranchRealization.toIdentityCloseout` turns literal
  closeout and split certificates into the impossibility half of that ledger;
  and
- `FineFiberFixedIdentitySemantics.identityFinality_of_terminal` composes the
  already proved fine-fibre merge disposition with certified bounded and
  lower-rank discharge.

`ManuscriptKernelTransfer` now imports a
`KernelNecessityAnchoredFourRoleWitnessPipeline` at each dense local
countercase. Its generated ledger permits skin, bounded certificate, tensor
split, sunflower, or an attempted independent authorizer. The mechanized
fixed-domain kernel theorem removes the fifth branch; canonical endpoint skin
supplies quotient finality; and reduction minimality excludes the three
surviving non-skin certificate branches. Lean then derives the older
fixed-identity realization, support-fibre bound, and endpoint transfer. The
typed manuscript theorem consists exactly of the target-specific five-way
witness classification and concrete reduction certificates, not an injective
finite code, four-role closure, the support-fibre inequality, or the endpoint
theorem.

## Kernel-Necessity Root

`V2.KernelNecessityRoleOccupancy` records the full upstream dependency:

- `CorpusMachinery.concreteKernelFirstCorpusMachinery` constructs the
  necessity source from nondegeneracy and constructs the concrete fixed-domain
  consequence layer by exhausting the finite strengthening-factor ledger;
- `necessityRootedEndpointGovernance` carries only endpoint nondegeneracy and
  the separately mechanized kernel dependency; endpoint adequacy, all four
  kernel roles, licensed sameness, and fixed-domain exclusion of independent
  authority are theorem projections from that root rather than parallel
  occupancy assumptions;
- `generatedTerminalIncidence_governance` attaches that packet directly to
  every combinatorially generated terminal incidence;
- `NecessityRootedEndpointGovernance.admissibilityBivalent` and
  `.fixedDomainInterfaceShape` derive the bivalent and fixed-domain consequence
  layers from that packet;
- `KernelGovernedGeneratedFourRolePopulation.toAASCFourRoleIdentityPopulation`
  turns the generated five-way ledger into the four lawful roles by eliminating
  independent authority through kernel necessity;
- `ReductionMinimalFourRoleCertificatePipeline.terminal` derives certificate
  terminality from a literal reduction-minimal countercase; and
- `KernelNecessityAnchoredFourRoleWitnessPipeline.dependencyTrace` packages the
  checked chain from determinate endpoint use through fixed identity;
- `ImportedManuscriptKernelGovernedPopulationTheorem.kernelNecessityEndpointTrace`
  extends that trace through the canonical support-fibre bound to the global
  three-petal endpoint theorem.

## Mechanized Kernel Boundary

The pinned standalone kernel now exports two separate current-locus results.
`KernelForcedCurrentLocusPopulation.currentOccupancy_nonempty` derives one
occupied generated locus from an independently established no-standing-sink
clause, source Standing, and live same-package continuation.
`CurrentReferenceClassifierSemantics.currentReference_rightUnique` proves that
two lawful primitive Current-Reference singleton classifiers at one fixed
package and locus have the same Reference, using same-domain classifier
uniqueness rather than an injective-role field.

`V2.CurrentReferenceClassifierAdapter` applies that theorem to the exact
root-to-seed surface. Right-uniqueness is now derived by the imported kernel
theorem. Its exact-strength result also proves that inhabiting the complete
classifier-governed package remains exactly equivalent to `ReachableRoleHall`.
`V2.AdversarialCurrentLocusClosure` composes the two kernel results in the
manuscript's dependency order: null exclusion gives sourcewise occupancy and
classifier uniqueness then excludes collisions. Its exact-strength theorem
proves that the complete adversarial package still has exactly Hall strength.

`V2.CurrentLocusNecessityAudit` supplies two finite regression models. The
current unary `KernelPackage` can hold while every generated locus is null;
and it can hold together with sourcewise population while two source identities
collide at one locus and no lawful Current-Reference binding exists. This
regression isolates the exact strength of that older Hall-equivalent diagnostic
route; it does not qualify the controlling post-exhaustion theorem.

`V2.ResidualMergeCounterexample` tests the actual private-residual tower rather
than an unrelated abstract relation. For the three-edge rank-two triangle,
Lean proves no three-petal sunflower, a two-element minimum blocker, one common
private residual, a terminal seed space of size at most one, failure of Hall,
noninjectivity of `cellCarrierOf`, and nonexistence of both the endpoint-role
bridge and the complete adversarial package. The two colliding generated
incidences also satisfy the paper's private-witness nondegeneracy predicate and
lie at the automatically kernel-governed endpoint. Therefore sourcewise
continuation is already generated, but collision-free Current-Reference binding
is false for the unrestricted residual tower. The required theorem must use
the dense-cell and reconstruction hypotheses to exclude or discharge such
merges.

`V2.KernelReferenceBoundary` remains as a regression check showing why the
older unary `KernelPackage` alone was insufficient; it does not apply to the
new relational classifier theorem.

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

## Exact Reachable-Role Occupancy

`V2.ReachableRoleOccupancy` defines `ReachableRoleHall F cell` directly on the
generated incidence relation and proves:

- `reachableRoleHall_iff_exists_injective_selector`;
- `nonempty_standingPathBridge_iff_reachableRoleHall`; and
- constructors in both directions, with no endpoint bound as a premise.

Thus bridge population is neither vague nor hidden in an interface. It is
exactly a finite system-of-distinct-representatives problem on literal
terminal blockers.

`V2.KernelRoleOccupancyAdapter` then uses the initial private-witness incidence
profile as a faithful fixed reference. The imported kernel theorem rules out
role collisions whenever a terminal role preserves that reference. Lean also
proves
`nonempty_generatedRoleReferenceTransport_iff_reachableRoleHall`, showing
that target-specific reference transport has exactly the same strength as
Hall occupancy and cannot be used to smuggle the missing combinatorics into
the kernel premise.

## Fixed-Cell Role-Locus Closure

`V2.FixedCellStandingClosure` constructs the literal manuscript fibre
`fixedComparisonCell`, whose members share canonical support, constraint
profile, and forced role. `V2.FixedCellRoleLocusExclusion` then records the
correct exclusion law:

```text
same complete role + same terminal locus -> same determinate source.
```

`CompleteRoleLocusExclusion` is collision-only. It contains no source
population, selector, finite code, Hall inequality, or endpoint bound. The
combinatorial theorem `exists_reachesTerminalCarrier` independently populates
the raw reach relation. Lean composes these two facts to prove
`reachableRoleHall_of_completeRoleLocusExclusion`.

An inhabited `PrivateWitnessConstraintPopulation` package instantiates this
law on each fixed support/profile/role cell: its complete-signature exhaustion
proves the stronger fact that the cell is subsingleton. Direct construction of
that Hall-shaped package belongs to an alternative diagnostic architecture and
is not required by the post-exhaustion theorem. Standing is not treated as a
separately generated or graded resource; it is downstream of complete
kernel-faithful role fulfillment.

## Formalization Boundary

The current Lean development checks the generic post-exhaustion implication:
finite generated disposition plus AASC terminal closeout proves the endpoint,
without raw source Hall. The terminal handoff is decomposed into bivalent
skin/non-skin exhaustion, the explicit four-role ledger, certified branch
realization, certificate terminality, and fixed-identity finality. The
manuscript proves the generated five-way classification and concrete reduction
certificates at their natural boundary; the named typed import joins that
completed terminal theorem to the completed Lean component. Kernel necessity,
fifth-branch exclusion, canonical skin finality, four-role closure, fixed
identity, and endpoint transfer are derived in Lean.

The graded-product and rank-weighted modules are retained as exploratory
support for a distinct autonomous conventional strengthening. Their theorem
surface does not alter the dependency chain above. The triangle regression
continues to rule out any attempt to replace collision disposition by raw
injection. No support-fibre bound, injective selector, finite code,
one-occupant-per-token premise, Hall inequality, or endpoint estimate is hidden
in the generated path theorem.

The imported kernel validates meaningful bivalent identity and excludes an
independent same-domain authorizer. It does not by itself turn a shared locus
into a singleton fibre. Occupant finality is derived only after the generated
five-way collision exhaustion, canonical endpoint-skin finality, and literal
reduction-minimal branch certificates have also been supplied.

At the level of mathematical dependency, those AASC consequences are forced
by kernel necessity through kernel-faithful fixed-domain exhaustion. At the
level of the present Lean packaging, `KernelFirstCorpusMachinery` records the
necessity source and `FixedDomainAPlusClosureSource` as two explicit stages.
That type-level separation audits the derivation and does not make the second
stage an optional regime assumption.

## Autonomous Conventional Strengthening

The rank-compatible product, graded convolution, and weighted charging files
study a possible replacement of the terminal AASC theorem by a wholly
conventional single-language argument. They establish exact component
reconstruction, recursive full-product control, and honest lower-rank gate
sections. Those modules are non-load-bearing for the integrated theorem and
are not presented as an unfinished portion of it.

The endpoint-strength interface
`ImportedManuscriptKernelGovernedPopulationTheorem` remains in the repository
for correspondence and downstream audit. It gives the typed join between the
manuscript's completed Sunflower-specific witness-and-certificate theorem and
Lean's completed necessity-rooted closeout and endpoint downstream.

The release therefore claims the complete integrated combinatorial--AASC
closure and its checked post-exhaustion transfer spine. It does not recast that
theorem as a different autonomous conventional theorem, because no such
replacement is required by the statement or proof architecture.

## Main Anchors

- `V2.SelectedCoordinateReduction.family_card_le_k_mul_residualFamily`
- `V2.GeneratedIncidenceTower.nextCoordinate_nonempty`
- `V2.GeneratedIncidenceTower.incidencePath_nonempty`
- `V2.GeneratedIncidenceTower.exists_reachesTerminalCarrier`
- `V2.GeneratedIncidenceTower.terminalFamily_noSunflower`
- `V2.ReachableRoleOccupancy.reachableRoleHall_iff_exists_injective_selector`
- `V2.ReachableRoleOccupancy.nonempty_standingPathBridge_iff_reachableRoleHall`
- `V2.KernelRoleOccupancyAdapter.sourceReference_injective`
- `V2.KernelRoleOccupancyAdapter.nonempty_generatedRoleReferenceTransport_iff_reachableRoleHall`
- `V2.KernelRoleOccupancyAdapter.GeneratedRoleReferenceTransport.toImportedKernelBridge`
- `V2.FixedCellStandingClosure.mem_own_fixedComparisonCell`
- `V2.FixedCellStandingClosure.fixedCellSource_fields_eq`
- `V2.FixedCellStandingClosure.standingAdmissibleRedescription_sharedCarrier`
- `V2.FixedCellStandingClosure.reachableRoleHall_of_standingFiberPopulation`
- `V2.FixedCellStandingClosure.fixedCell_reachableRoleHall_of_standingFiberPopulation`
- `V2.FixedCellRoleLocusExclusion.generatedCarrier_injective_of_completeRoleLocusExclusion`
- `V2.FixedCellRoleLocusExclusion.reachableRoleHall_of_completeRoleLocusExclusion`
- `V2.FixedCellRoleLocusExclusion.completeRoleLocusExclusion_of_constraintPopulation`
- `V2.FixedCellRoleLocusExclusion.fixedCell_reachableRoleHall_of_constraintPopulation`
- `V2.GeneratedTerminalKernelGovernance.generatedTerminalIncidence_identity_injective`
- `V2.GeneratedTerminalKernelGovernance.GeneratedTerminalIncidence.privateWitnessNondegenerate_holds`
- `V2.GeneratedTerminalKernelGovernance.terminalFamily_at_noSunflowerEndpoint`
- `V2.GeneratedTerminalKernelGovernance.GeneratedTerminalIncidence.kernelRolesHold`
- `V2.GeneratedSeedCapacity.KernelFaithfulStandingPathBridge.standingCarrier_reachable`
- `V2.GeneratedSeedCapacity.KernelFaithfulStandingPathBridge.standingCarrier_choice_independent`
- `V2.GeneratedSeedCapacity.KernelFaithfulStandingPathBridge.standingCarrierOf_injective`
- `V2.GeneratedSeedCapacity.KernelFaithfulStandingPathBridge.cell_card_le_4094`
- `V2.PairLocalizedReferenceDivergence.generatedResidualParentCollision_hasPairMergeWitness`
- `V2.PairLocalizedReferenceDivergence.sameCell_distinct_has_rankSplit`
- `V2.PairLocalizedReferenceDivergence.generatedResidualParentCollision_pairLocalExhaustion`
- `V2.RootAuthenticScopeCorrespondence.RootAuthenticScopeSeedClosure.rootSeedMap_injective`
- `V2.RootAuthenticScopeCorrespondence.nonempty_rootAuthenticScopeSeedClosure_iff_reachableRoleHall`
- `V2.RootAuthenticScopeCorrespondence.nonempty_rootAuthenticScopeSeedClosure_iff_standingPathBridge`
- `V2.CurrentReferenceClassifierAdapter.ClassifierGovernedRootSeedClosure.rootSeed_rightUnique`
- `V2.CurrentReferenceClassifierAdapter.nonempty_classifierGovernedRootSeedClosure_iff_reachableRoleHall`
- `V2.ResidualMergeCounterexample.triangleFamily_no_threeSunflower`
- `V2.ResidualMergeCounterexample.triangle_cellCarrierOf_not_injective`
- `V2.ResidualMergeCounterexample.triangle_not_reachableRoleHall`
- `V2.ResidualMergeCounterexample.triangle_no_adversarialCurrentLocusPackage`
- `V2.ExplicitReductionPotential.reductionPotential_wellFounded`
- `V2.ExplicitReductionPotential.certified_terminalization`
- `V2.ExplicitReductionPotential.reductionMinimal_countercase_terminal`
- `V2.TerminalRoleOccupancyCloseout.CertifiedTerminalExit.impossible`
- `V2.TerminalRoleOccupancyCloseout.TerminalRoleOccupancyExhaustion.role_injective`
- `V2.TerminalRoleOccupancyCloseout.AASCFourRoleIdentityPopulation.collision`
- `V2.TerminalRoleOccupancyCloseout.CertifiedAASCFourRoleBranchRealization.toFixedIdentityRealization`
- `V2.TerminalRoleOccupancyCloseout.FineFiberFixedIdentitySemantics.identityFinality_of_terminal`
- `V2.KernelReferenceBoundary.kernelPackage_alone_does_not_force_role_injective`
- `V2.ManuscriptKernelTransfer.KernelImportRoute.admissibilityBivalent`
- `V2.ManuscriptKernelTransfer.ThreePetalLocalManuscriptPopulation.fourRoleIdentityClosure`
- `V2.ManuscriptKernelTransfer.sunflower_of_importedManuscriptKernelGovernedClosure`
- `V2.ManuscriptKernelTransfer.nonempty_importedManuscriptPopulationTheorem_iff_endpointBound`

## Kernel Dependency

The standalone mechanized kernel repository is pinned at commit
`96978f41a08347f36650d3757cfe0ef79bf864f8`.
`V2.MechanizedKernelImport` constructs its `ConstructionRegime`, kernel
package, fixed-domain closure, uniqueness, no-derivation-below result, and
global synthesis certificate for the fixed Sunflower endpoint route. The
pinned kernel additionally exports the axiom-clean generic
`FixedRoleReferenceSemantics.role_injective` theorem used by the concrete
Sunflower adapter.

The four labels of a bare `KernelPackage` are not treated as a combinatorial
generator or as a singleton-fibre theorem. The fixed-domain AASC consequences
come from the kernel-first corpus exhaustion attached to the necessarily
governed endpoint.

## Validation

The release uses Lean and Mathlib `v4.28.0`.

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check-sunflower-a-plus-audit.ps1
```

Verified locally:

- public entrypoint build: 1,143 jobs;
- combined entrypoint-and-audit build: 1,146 jobs;
- 250 focused `#print axioms` checks;
- no live project `axiom`, `sorry`, `admit`, or unsafe declaration; and
- only standard Lean/Mathlib principles such as `propext`,
  `Classical.choice`, and `Quot.sound` on the audited anchors.

## Manuscript

The synchronized publication snapshot is under [`papers/sunflower`](papers/sunflower):

- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint_Integrated_Hybrid_Closure_Edition.pdf`
- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint_Integrated_Hybrid_Closure_Publication_Project.zip`

The 48-page manuscript and its 109-file source package use the same dependency
order as the Lean types: generated incidence first, structural endpoint
governance second, numerical readout last. The package includes all 63 project
Lean source files with a verified source-hash manifest.
