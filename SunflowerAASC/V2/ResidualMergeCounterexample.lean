import SunflowerAASC.V2.AdversarialCurrentLocusClosure
import SunflowerAASC.V2.MergeDispositionClosure
import SunflowerAASC.V2.QuotientCoverageRigidity

namespace SunflowerAASC
namespace V2
namespace ResidualMergeCounterexample

open GeneratedIncidenceTower
open GeneratedSeedCapacity
open ReachableRoleOccupancy
open RootAuthenticScopeCorrespondence
open AdversarialCurrentLocusClosure
open GeneratedTerminalKernelGovernance
open MergeDispositionClosure
open PairLocalizedReferenceDivergence
open CompleteRoleRefinement
open CompleteRoleRefinement
open QuotientCoverageRigidity

/-- The three edges of the rank-two triangle on `Fin 3`. -/
def triangleFamily : Concrete.UniformSetFamily (Fin 3) 2 where
  edges := Finset.univ.powersetCard 2
  uniform := by
    intro edge edge_mem
    exact (Finset.mem_powersetCard.mp edge_mem).2

def edge01 : Finset (Fin 3) := {0, 1}

def edge02 : Finset (Fin 3) := {0, 2}

def edge12 : Finset (Fin 3) := {1, 2}

theorem edge01_mem : edge01 ∈ triangleFamily.edges := by
  decide

theorem edge02_mem : edge02 ∈ triangleFamily.edges := by
  decide

theorem edge12_mem : edge12 ∈ triangleFamily.edges := by
  decide

theorem triangle_edge_type_card :
    Fintype.card {edge // edge ∈ triangleFamily.edges} = 3 := by
  decide

theorem triangleFamily_no_threeSunflower :
    Not (Concrete.HasSunflower 3 triangleFamily) := by
  rintro ⟨core, ⟨witness⟩⟩
  let petalMap : Fin 3 → {edge // edge ∈ triangleFamily.edges} :=
    fun index => ⟨witness.petals index, witness.petals_mem index⟩
  have petalMap_injective : Function.Injective petalMap := by
    intro left right same
    exact witness.petals_injective (Subtype.ext_iff.mp same)
  have petalMap_surjective : Function.Surjective petalMap :=
    ((Fintype.bijective_iff_injective_and_card petalMap).mpr
      ⟨petalMap_injective, by
        rw [Fintype.card_fin, Fintype.card_coe]
        exact triangle_edge_type_card.symm⟩).2
  obtain ⟨i01, hi01⟩ := petalMap_surjective ⟨edge01, edge01_mem⟩
  obtain ⟨i02, hi02⟩ := petalMap_surjective ⟨edge02, edge02_mem⟩
  obtain ⟨i12, hi12⟩ := petalMap_surjective ⟨edge12, edge12_mem⟩
  have hi01_value : witness.petals i01 = edge01 := by
    exact congrArg Subtype.val hi01
  have hi02_value : witness.petals i02 = edge02 := by
    exact congrArg Subtype.val hi02
  have hi12_value : witness.petals i12 = edge12 := by
    exact congrArg Subtype.val hi12
  have i01_ne_i02 : i01 ≠ i02 := by
    intro same
    have : edge01 = edge02 := by
      exact hi01_value.symm.trans ((same ▸ hi02_value))
    exact (by decide : edge01 ≠ edge02) this
  have i01_ne_i12 : i01 ≠ i12 := by
    intro same
    have : edge01 = edge12 := by
      exact hi01_value.symm.trans ((same ▸ hi12_value))
    exact (by decide : edge01 ≠ edge12) this
  have firstCore : edge01 ∩ edge02 = core := by
    rw [← hi01_value, ← hi02_value]
    exact witness.pairwise_intersection i01 i02 i01_ne_i02
  have secondCore : edge01 ∩ edge12 = core := by
    rw [← hi01_value, ← hi12_value]
    exact witness.pairwise_intersection i01 i12 i01_ne_i12
  have impossible : edge01 ∩ edge02 = edge01 ∩ edge12 :=
    firstCore.trans secondCore.symm
  exact (by decide : edge01 ∩ edge02 ≠ edge01 ∩ edge12) impossible

theorem triangle_edges_not_disjoint
    {left right : Finset (Fin 3)}
    (left_mem : left ∈ triangleFamily.edges)
    (right_mem : right ∈ triangleFamily.edges) :
    Not (Disjoint left right) := by
  intro disjoint
  have left_card : left.card = 2 := triangleFamily.uniform left left_mem
  have right_card : right.card = 2 := triangleFamily.uniform right right_mem
  have union_card : (left ∪ right).card = 4 := by
    rw [Finset.card_union_of_disjoint disjoint, left_card, right_card]
  have union_le : (left ∪ right).card ≤ (Finset.univ : Finset (Fin 3)).card :=
    Finset.card_le_card (by simp)
  simp at union_le
  omega

theorem emptyCoreMatching_card_le_one :
    (EffectiveBlocker.emptyCoreMaximalMatching triangleFamily).matching.petals.card ≤ 1 := by
  let matching :=
    (EffectiveBlocker.emptyCoreMaximalMatching triangleFamily).matching
  change matching.petals.card ≤ 1
  by_contra tooLarge
  have two_le : 2 ≤ matching.petals.card := by omega
  let twoMatching := matching.restrictToArity two_le
  have disjoint := twoMatching.residuals_disjoint 0 1 (by decide)
  have rawDisjoint :
      Disjoint (twoMatching.petals 0) (twoMatching.petals 1) := by
    simpa using disjoint
  exact triangle_edges_not_disjoint
    (twoMatching.petals_mem 0) (twoMatching.petals_mem 1) rawDisjoint

theorem canonicalRawBlocker_card_le_two :
    (EffectiveBlocker.canonicalRawBlocker triangleFamily).card ≤ 2 := by
  let matching :=
    (EffectiveBlocker.emptyCoreMaximalMatching triangleFamily).matching
  change matching.rawBlocker.card ≤ 2
  calc
    matching.rawBlocker.card ≤ matching.petals.card * 2 :=
      matching.rawBlocker_card_le
    _ ≤ 1 * 2 := Nat.mul_le_mul_right 2 emptyCoreMatching_card_le_one
    _ = 2 := by omega

theorem triangleMinimalBlocker_card_le_two :
    (MinimalBlocker.minimalBlocker triangleFamily).card ≤ 2 :=
  Nat.le_trans
    (MinimalBlocker.minimalBlocker_card_le triangleFamily
      (MinimalBlocker.canonicalRawBlocker_mem_rawHittingBlockers triangleFamily))
    canonicalRawBlocker_card_le_two

theorem triangleMinimalBlocker_card_ge_two :
    2 ≤ (MinimalBlocker.minimalBlocker triangleFamily).card := by
  let blocker := MinimalBlocker.minimalBlocker triangleFamily
  change 2 ≤ blocker.card
  by_contra tooSmall
  have blocker_card_le_one : blocker.card ≤ 1 := by omega
  have blocker_subset_univ : blocker ⊆ (Finset.univ : Finset (Fin 3)) := by
    simp
  have complement_card :
      ((Finset.univ : Finset (Fin 3)) \ blocker).card = 3 - blocker.card := by
    rw [Finset.card_sdiff_of_subset blocker_subset_univ]
    simp
  have two_le_complement :
      2 ≤ ((Finset.univ : Finset (Fin 3)) \ blocker).card := by
    rw [complement_card]
    omega
  obtain ⟨edge, edge_subset, edge_card⟩ :=
    Finset.exists_subset_card_eq two_le_complement
  have edge_mem : edge ∈ triangleFamily.edges := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨by simp, edge_card⟩
  have edge_disjoint : Disjoint edge blocker := by
    apply Finset.disjoint_left.mpr
    intro point point_edge point_blocker
    have point_complement := edge_subset point_edge
    exact (Finset.mem_sdiff.mp point_complement).2 point_blocker
  exact MinimalBlocker.minimalBlocker_hitsEveryEdge
    triangleFamily edge edge_mem edge_disjoint

theorem triangleMinimalBlocker_card :
    (MinimalBlocker.minimalBlocker triangleFamily).card = 2 :=
  Nat.le_antisymm triangleMinimalBlocker_card_le_two
    triangleMinimalBlocker_card_ge_two

noncomputable abbrev triangleBlocker : Finset (Fin 3) :=
  MinimalBlocker.minimalBlocker triangleFamily

noncomputable def triangleComplement : Finset (Fin 3) :=
  Finset.univ \ triangleBlocker

theorem triangleComplement_card : triangleComplement.card = 1 := by
  rw [triangleComplement, Finset.card_sdiff_of_subset (by simp)]
  simp [triangleMinimalBlocker_card]

/-- Every private witness deletion in the triangle leaves the same third point. -/
theorem privateResidual_eq_triangleComplement
    (source : {x // x ∈ triangleBlocker}) :
    PrivateWitnessReduction.residual triangleFamily source = triangleComplement := by
  apply Finset.eq_of_subset_of_card_le
  · intro point point_residual
    have point_edge :
        point ∈ MinimalBlocker.privateEdge triangleFamily source :=
      Finset.mem_of_mem_erase point_residual
    have point_ne_source : point ≠ source.val :=
      (Finset.mem_erase.mp point_residual).1
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ point, ?_⟩
    intro point_blocker
    have point_intersection :
        point ∈ MinimalBlocker.privateEdge triangleFamily source ∩
          triangleBlocker :=
      Finset.mem_inter.mpr ⟨point_edge, point_blocker⟩
    rw [MinimalBlocker.privateEdge_inter_minimalBlocker] at point_intersection
    exact point_ne_source (Finset.mem_singleton.mp point_intersection)
  · rw [PrivateWitnessReduction.residual_card triangleFamily source,
      triangleComplement_card]

theorem triangleResidualFamily_edges :
    (PrivateWitnessReduction.residualFamily triangleFamily).edges =
      {triangleComplement} := by
  apply Finset.ext
  intro edge
  rw [PrivateWitnessReduction.mem_residualFamily_iff]
  constructor
  · rintro ⟨source, rfl⟩
    exact Finset.mem_singleton.mpr
      (privateResidual_eq_triangleComplement source)
  · intro edge_mem
    have edge_eq : edge = triangleComplement := Finset.mem_singleton.mp edge_mem
    subst edge
    have blocker_nonempty : triangleBlocker.Nonempty :=
      Finset.card_pos.mp (by rw [triangleMinimalBlocker_card]; omega)
    obtain ⟨point, point_mem⟩ := blocker_nonempty
    exact ⟨⟨point, point_mem⟩,
      privateResidual_eq_triangleComplement ⟨point, point_mem⟩⟩

theorem residualCanonicalRawBlocker_subset_triangleComplement :
    EffectiveBlocker.canonicalRawBlocker
        (PrivateWitnessReduction.residualFamily triangleFamily) ⊆
      triangleComplement := by
  intro point point_raw
  let matching := EffectiveBlocker.emptyCoreMaximalMatching
    (PrivateWitnessReduction.residualFamily triangleFamily)
  change point ∈ matching.matching.rawBlocker at point_raw
  rcases Finset.mem_biUnion.mp point_raw with
    ⟨edge, edge_selected, point_edge⟩
  have edge_family := matching.matching.petals_subset edge_selected
  rw [triangleResidualFamily_edges] at edge_family
  have edge_eq : edge = triangleComplement :=
    Finset.mem_singleton.mp edge_family
  subst edge
  simpa using point_edge

theorem residualMinimalBlocker_subset_triangleComplement :
    MinimalBlocker.minimalBlocker
        (PrivateWitnessReduction.residualFamily triangleFamily) ⊆
      triangleComplement :=
  fun _point point_mem =>
    residualCanonicalRawBlocker_subset_triangleComplement
      (MinimalBlocker.minimalBlocker_subset_raw
        (PrivateWitnessReduction.residualFamily triangleFamily) point_mem)

theorem residualMinimalBlocker_card_le_one :
    (MinimalBlocker.minimalBlocker
      (PrivateWitnessReduction.residualFamily triangleFamily)).card ≤ 1 := by
  calc
    (MinimalBlocker.minimalBlocker
      (PrivateWitnessReduction.residualFamily triangleFamily)).card
        ≤ triangleComplement.card :=
      Finset.card_le_card residualMinimalBlocker_subset_triangleComplement
    _ = 1 := triangleComplement_card

noncomputable def triangleCell :
    Finset (InitialCarrier (baseRank := 0) (steps := 1) triangleFamily) :=
  Finset.univ

theorem triangleCellSource_card :
    Fintype.card (CellSource triangleCell) = 2 := by
  simp [triangleCell, CellSource, InitialCarrier, triangleMinimalBlocker_card]

theorem triangleSeedCoordinate_card_le_one :
    Fintype.card (SeedCoordinate (baseRank := 0) (steps := 1) triangleFamily) ≤ 1 := by
  simpa [SeedCoordinate, terminalFamily] using residualMinimalBlocker_card_le_one

/-- The concrete generated terminal-carrier map necessarily merges two roots. -/
theorem triangle_cellCarrierOf_not_injective :
    Not (Function.Injective
      (cellCarrierOf (baseRank := 0) (steps := 1)
        triangleFamily triangleCell)) := by
  intro injective
  have cardinal_le := Fintype.card_le_of_injective
    (cellCarrierOf (baseRank := 0) (steps := 1)
      triangleFamily triangleCell) injective
  change Fintype.card (CellSource triangleCell) ≤
    Fintype.card (SeedCoordinate (baseRank := 0) (steps := 1)
      triangleFamily) at cardinal_le
  rw [triangleCellSource_card] at cardinal_le
  have target_le := triangleSeedCoordinate_card_le_one
  omega

theorem triangle_no_endpointRoleBridge :
    Not (Nonempty (KernelFaithfulEndpointRoleBridge
      (baseRank := 0) (steps := 1) triangleFamily triangleCell)) := by
  rw [nonempty_endpointRoleBridge_iff_cellCarrierOf_injective]
  exact triangle_cellCarrierOf_not_injective

theorem exists_distinct_triangle_sources_same_generated_locus :
    ∃ left right : CellSource triangleCell,
      left ≠ right ∧
        cellCarrierOf (baseRank := 0) (steps := 1)
            triangleFamily triangleCell left =
          cellCarrierOf (baseRank := 0) (steps := 1)
            triangleFamily triangleCell right := by
  by_contra noCollision
  apply triangle_cellCarrierOf_not_injective
  intro left right sameLocus
  by_contra distinct
  exact noCollision ⟨left, right, distinct, sameLocus⟩

/-- Two distinct roots really do reach one literal generated terminal locus. -/
theorem triangle_generated_collision :
    ∃ (left right : CellSource triangleCell)
        (locus : SeedCoordinate (baseRank := 0) (steps := 1) triangleFamily),
      left ≠ right ∧
        ReachesTerminalCarrier (baseRank := 0) (steps := 1)
            (F := triangleFamily) left.coordinate locus ∧
        ReachesTerminalCarrier (baseRank := 0) (steps := 1)
            (F := triangleFamily) right.coordinate locus := by
  obtain ⟨left, right, distinct, sameLocus⟩ :=
    exists_distinct_triangle_sources_same_generated_locus
  refine ⟨left, right,
    cellCarrierOf (baseRank := 0) (steps := 1)
      triangleFamily triangleCell left,
    distinct, cellCarrierOf_reachable (baseRank := 0) (steps := 1)
      triangleFamily triangleCell left, ?_⟩
  rw [sameLocus]
  exact cellCarrierOf_reachable (baseRank := 0) (steps := 1)
    triangleFamily triangleCell right

/-- The concrete triangle collision occurs at its only deletion step. -/
theorem triangle_oneStepPairMerge :
    ∃ left right : {x // x ∈ triangleBlocker},
      Nonempty (OneStepPairMerge triangleFamily left right) := by
  have sourceCard :
      Fintype.card {x // x ∈ triangleBlocker} = 2 := by
    simpa using triangleMinimalBlocker_card
  obtain ⟨left, right, distinct⟩ :=
    Fintype.one_lt_card_iff.mp (by rw [sourceCard]; omega)
  obtain ⟨leftTarget, leftIncident⟩ := exists_nextRel triangleFamily left
  obtain ⟨rightTarget, rightIncident⟩ := exists_nextRel triangleFamily right
  have targetEq : leftTarget = rightTarget :=
    Fintype.card_le_one_iff.mp triangleSeedCoordinate_card_le_one
      leftTarget rightTarget
  subst rightTarget
  exact ⟨left, right, ⟨{
    target := leftTarget
    leftIncident := leftIncident
    rightIncident := rightIncident
    sourceDistinct := distinct }⟩⟩

/--
The triangle regression lands in the bounded-charge branch.  It witnesses a
real merge, but the complete charge class has cardinality below three.
-/
theorem triangle_merge_has_boundedResidualCharge :
    ∃ left right : {x // x ∈ triangleBlocker},
      Nonempty (BoundedResidualCharge triangleFamily
        triangleFamily_no_threeSunflower left right) := by
  obtain ⟨left, right, ⟨merge⟩⟩ := triangle_oneStepPairMerge
  have sameResidual :
      PrivateWitnessReduction.residual triangleFamily left =
        PrivateWitnessReduction.residual triangleFamily right := by
    rw [privateResidual_eq_triangleComplement,
      privateResidual_eq_triangleComplement]
  have bounded : BoundedFiberSlotDistinction triangleFamily
      triangleFamily_no_threeSunflower left right :=
    ⟨sameResidual,
      PrivateWitnessReduction.residualFiberSlot_ne_of_sameResidual_of_nonSkin
        triangleFamily triangleFamily_no_threeSunflower left right
        sameResidual
        (MinimalBlocker.distinct_privateWitness_not_endpointSkin
          triangleFamily left right merge.sourceDistinct)⟩
  exact ⟨left, right, ⟨boundedResidualChargeOfDistinction
    triangleFamily triangleFamily_no_threeSunflower left right
    merge.sourceDistinct bounded⟩⟩

/--
The colliding triangle roots are not quotientable when original blocker
coverage is retained: their private edges make the distinction tensor-active.
The merge must therefore be charged or reconstructed, not renamed as skin.
-/
theorem triangle_merge_is_coverageTensorActive :
    ∃ left right : {x // x ∈ triangleBlocker},
      Nonempty (OneStepPairMerge triangleFamily left right) ∧
        EndpointTensorActive triangleFamily left right := by
  obtain ⟨left, right, merge⟩ := triangle_oneStepPairMerge
  refine ⟨left, right, merge, ?_⟩
  exact (endpointTensorActive_iff_distinct triangleFamily left right).mpr
    merge.some.sourceDistinct

/--
The triangle excludes an undischarged source-level quotient bridge when that
bridge preserves the coverage tensor needed by the ordinary blocker
recurrence. Its two roots are distinct coverage-bearing sources, not merely
two path histories attached to one source. This does not test the bridge after
the bounded-charge disposition has been discharged.
-/
theorem triangle_no_undischargedCoverageCarrierBridge :
    Not (Nonempty (UndischargedCoverageCarrierBridge triangleFamily
      (SeedCoordinate (baseRank := 0) (steps := 1) triangleFamily))) := by
  rintro ⟨bridge⟩
  have sourceLe := bridge.source_card_le_coordinate
  change Fintype.card {x // x ∈ triangleBlocker} <=
    Fintype.card (SeedCoordinate (baseRank := 0) (steps := 1)
      triangleFamily) at sourceLe
  rw [show Fintype.card {x // x ∈ triangleBlocker} = 2 by
    simpa using triangleMinimalBlocker_card] at sourceLe
  have targetLe := triangleSeedCoordinate_card_le_one
  omega

/--
The colliding source/locus incidences retain faithful typed identity, satisfy
the paper's private-witness nondegeneracy predicate, and lie at the
automatically kernel-governed endpoint.
-/
theorem triangle_collision_is_nondegenerate_and_kernelGoverned :
    ∃ (leftIncidence rightIncidence :
        GeneratedTerminalIncidence (baseRank := 0) (steps := 1)
          triangleFamily triangleCell),
      leftIncidence.source ≠ rightIncidence.source ∧
        leftIncidence.locus = rightIncidence.locus ∧
        leftIncidence.PrivateWitnessNondegenerate ∧
        rightIncidence.PrivateWitnessNondegenerate ∧
        ((terminalKernelFirstCorpusMachinery (Fin 3) 0).kernelAtEndpointUse
          (terminalNoSunflowerEndpointUse (Fin 3) 0)).allRolesHold := by
  obtain ⟨left, right, locus, distinct, leftGenerated, rightGenerated⟩ :=
    triangle_generated_collision
  let leftIncidence : GeneratedTerminalIncidence
      (baseRank := 0) (steps := 1) triangleFamily triangleCell :=
    ⟨left, locus, leftGenerated⟩
  let rightIncidence : GeneratedTerminalIncidence
      (baseRank := 0) (steps := 1) triangleFamily triangleCell :=
    ⟨right, locus, rightGenerated⟩
  exact ⟨leftIncidence, rightIncidence, distinct, rfl,
    leftIncidence.privateWitnessNondegenerate_holds,
    rightIncidence.privateWitnessNondegenerate_holds,
    leftIncidence.kernelRolesHold⟩

/-- The generated one-step incidence has too few terminal carriers for Hall. -/
theorem triangle_not_reachableRoleHall :
    Not (ReachableRoleHall (baseRank := 0) (steps := 1)
      triangleFamily triangleCell) := by
  intro hall
  obtain ⟨seedOf, seedOf_injective, _seedOf_generated⟩ :=
    reachableRoleHall_iff_exists_injective_selector.mp hall
  have cardinal_le := Fintype.card_le_of_injective seedOf seedOf_injective
  change Fintype.card (CellSource triangleCell) ≤
    Fintype.card (SeedCoordinate (baseRank := 0) (steps := 1)
      triangleFamily) at cardinal_le
  rw [triangleCellSource_card] at cardinal_le
  have target_le := triangleSeedCoordinate_card_le_one
  omega

/-- Hence the complete adversarial current-locus package cannot be inhabited. -/
theorem triangle_no_adversarialCurrentLocusPackage :
    Not (Nonempty (AdversarialCurrentLocusPackage
      (baseRank := 0) (steps := 1)
      triangleFamily triangleFamily_no_threeSunflower triangleCell)) := by
  intro package
  exact triangle_not_reachableRoleHall package.some.reachableRoleHall

end ResidualMergeCounterexample
end V2
end SunflowerAASC
