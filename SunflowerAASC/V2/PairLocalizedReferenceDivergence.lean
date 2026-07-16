import SunflowerAASC.V2.ResidualParentExhaustion
import SunflowerAASC.V2.WitnessCompression

namespace SunflowerAASC
namespace V2
namespace PairLocalizedReferenceDivergence

open CompleteRoleRefinement
open GeneratedIncidenceTower
open ResidualParentExhaustion

/--
Two distinct coordinates merge in one generated deletion step when one next
minimal-blocker coordinate lies in both private residual parents.
-/
structure OneStepPairMerge
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) where
  target : {x // x ∈ MinimalBlocker.minimalBlocker
    (PrivateWitnessReduction.residualFamily F)}
  leftIncident : NextRel F left target
  rightIncident : NextRel F right target
  sourceDistinct : left ≠ right

theorem OneStepPairMerge.target_mem_parentIntersection
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (merge : OneStepPairMerge F left right) :
    merge.target.val ∈
      PrivateWitnessReduction.residual F left ∩
        PrivateWitnessReduction.residual F right := by
  exact Finset.mem_inter.mpr ⟨merge.leftIncident, merge.rightIncident⟩

theorem OneStepPairMerge.parentIntersection_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (merge : OneStepPairMerge F left right) :
    (PrivateWitnessReduction.residual F left ∩
      PrivateWitnessReduction.residual F right).Nonempty :=
  ⟨merge.target.val, merge.target_mem_parentIntersection⟩

/-- A one-step merge whose two private residual parents are genuinely distinct. -/
structure ResidualParentVennMerge
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) where
  merge : OneStepPairMerge F left right
  parentDistinct : ResidualParentTensorDistinction F left right

/-- The second canonical matching inside the private-residual family. -/
noncomputable def residualMatching
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    Concrete.MaximalFiniteCoreLinkMatching
      (PrivateWitnessReduction.residualFamily F) (∅ : Finset alpha) :=
  EffectiveBlocker.emptyCoreMaximalMatching
    (PrivateWitnessReduction.residualFamily F)

/-- The matching petals met by one private residual parent. -/
noncomputable def residualOverlapCell
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    Finset {edge // edge ∈ (residualMatching F).matching.petals} := by
  classical
  exact Finset.univ.filter fun edge =>
    Not (Disjoint (PrivateWitnessReduction.residual F source) edge.val)

theorem residualOverlapCell_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (residualOverlapCell F source).Nonempty := by
  classical
  let edge := PrivateWitnessReduction.residual F source
  have edge_mem : edge ∈
      (PrivateWitnessReduction.residualFamily F).edges :=
    PrivateWitnessReduction.mem_residualFamily_iff.mpr ⟨source, rfl⟩
  have edge_nonempty : edge.Nonempty := by
    apply Finset.card_pos.mp
    rw [show edge.card = r + 1 from
      PrivateWitnessReduction.residual_card F source]
    exact Nat.zero_lt_succ r
  rcases (residualMatching F).maximal edge edge_mem
      (Finset.empty_subset edge) with selected | conflict
  · let chosen : {edge // edge ∈ (residualMatching F).matching.petals} :=
      ⟨edge, selected⟩
    refine ⟨chosen, Finset.mem_filter.mpr ⟨Finset.mem_univ chosen, ?_⟩⟩
    rcases edge_nonempty with ⟨point, point_mem⟩
    exact Finset.not_disjoint_iff.mpr ⟨point, point_mem, point_mem⟩
  · rcases conflict with ⟨chosenEdge, chosen_mem, not_disjoint⟩
    let chosen : {edge // edge ∈ (residualMatching F).matching.petals} :=
      ⟨chosenEdge, chosen_mem⟩
    refine ⟨chosen, Finset.mem_filter.mpr ⟨Finset.mem_univ chosen, ?_⟩⟩
    simpa [edge] using not_disjoint

theorem residualOverlapCell_card_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (residualOverlapCell F source).card < k := by
  classical
  calc
    (residualOverlapCell F source).card ≤
        (Finset.univ : Finset
          {edge // edge ∈ (residualMatching F).matching.petals}).card :=
      Finset.card_filter_le _ _
    _ = (residualMatching F).matching.petals.card := by simp
    _ < k :=
      Concrete.finiteCoreLinkMatching_card_lt_of_noSunflower
        (PrivateWitnessReduction.residualFamily_noSunflower noSunflower)
        (residualMatching F).matching

/-- A rank-independent finite Venn signature for the residual parent. -/
noncomputable def residualOverlapCode
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    Finset (Fin k) :=
  (residualOverlapCell F source).map
    (WitnessCompression.matchingPetalEmbedding
      (residualMatching F).matching
      (Nat.le_of_lt <|
        Concrete.finiteCoreLinkMatching_card_lt_of_noSunflower
          (PrivateWitnessReduction.residualFamily_noSunflower noSunflower)
          (residualMatching F).matching))

theorem residualOverlapCode_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (residualOverlapCode F noSunflower source).Nonempty := by
  apply Finset.card_pos.mp
  rw [residualOverlapCode, Finset.card_map]
  exact Finset.card_pos.mpr (residualOverlapCell_nonempty F source)

theorem residualOverlapCode_card_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (residualOverlapCode F noSunflower source).card < k := by
  rw [residualOverlapCode, Finset.card_map]
  exact residualOverlapCell_card_lt F noSunflower source

/-- At three petals the pair-local residual Venn alphabet has exactly eight values. -/
theorem threePetal_residualOverlapCode_card_eq_eight :
    Fintype.card (Finset (Fin 3)) = 8 := by
  simp

theorem threePetal_residualOverlapCode_card_le_eight :
    Fintype.card (Finset (Fin 3)) ≤ 8 := by
  rw [threePetal_residualOverlapCode_card_eq_eight]

/-- Equality of the embedded finite Venn codes reflects equality of cells. -/
theorem residualOverlapCell_eq_of_code_eq
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameCode : residualOverlapCode F noSunflower left =
      residualOverlapCode F noSunflower right) :
    residualOverlapCell F left = residualOverlapCell F right := by
  unfold residualOverlapCode at sameCode
  exact Finset.map_injective _ sameCode

/-- The disjoint union of the selected residual-matching petals. -/
noncomputable def residualSupport
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) : Finset alpha :=
  (residualMatching F).matching.petals.biUnion id

/-- The part of a private residual inside one selected matching petal. -/
noncomputable def residualPetalComponent
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    Finset alpha :=
  PrivateWitnessReduction.residual F source ∩ petal.val

/-- The part of a private residual outside every selected matching petal. -/
noncomputable def residualOutside
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Finset alpha :=
  PrivateWitnessReduction.residual F source \ residualSupport F

theorem petal_mem_residualOverlapCell_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    petal ∈ residualOverlapCell F source ↔
      (residualPetalComponent F source petal).Nonempty := by
  simp [residualOverlapCell, residualPetalComponent,
    Finset.not_disjoint_iff_nonempty_inter]

theorem sameCell_component_occupancy_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameCell : residualOverlapCell F left = residualOverlapCell F right)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    (residualPetalComponent F left petal).Nonempty ↔
      (residualPetalComponent F right petal).Nonempty := by
  rw [← petal_mem_residualOverlapCell_iff,
    ← petal_mem_residualOverlapCell_iff, sameCell]

/-- Inside-support and outside-support ranks account for the whole residual. -/
theorem residual_support_rank_accounting
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (PrivateWitnessReduction.residual F source ∩ residualSupport F).card +
        (residualOutside F source).card = r + 1 := by
  rw [residualOutside, Finset.card_inter_add_card_sdiff]
  exact PrivateWitnessReduction.residual_card F source

/-- The outside remainder and all selected-petal components determine a residual. -/
theorem residual_eq_of_outside_eq_of_components_eq
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (outsideEq : residualOutside F left = residualOutside F right)
    (componentsEq :
      ∀ petal : {edge // edge ∈ (residualMatching F).matching.petals},
        residualPetalComponent F left petal =
          residualPetalComponent F right petal) :
    PrivateWitnessReduction.residual F left =
      PrivateWitnessReduction.residual F right := by
  classical
  apply Finset.ext
  intro point
  by_cases inSupport : point ∈ residualSupport F
  · rcases Finset.mem_biUnion.mp inSupport with
      ⟨petal, petal_mem, point_mem_petal⟩
    let selected : {edge // edge ∈ (residualMatching F).matching.petals} :=
      ⟨petal, petal_mem⟩
    have sameComponent := congrArg (fun edge : Finset alpha => point ∈ edge)
      (componentsEq selected)
    have reduced : point ∈ petal →
        (point ∈ PrivateWitnessReduction.residual F left ↔
          point ∈ PrivateWitnessReduction.residual F right) := by
      simpa [residualPetalComponent, selected] using sameComponent
    exact reduced point_mem_petal
  · have sameOutside :=
      congrArg (fun edge : Finset alpha => point ∈ edge) outsideEq
    simpa [residualOutside, inSupport] using sameOutside

/-- Every unequal residual localizes to the outside or one named petal. -/
theorem distinctResidual_outside_or_petalComponent
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (different : PrivateWitnessReduction.residual F left ≠
      PrivateWitnessReduction.residual F right) :
    residualOutside F left ≠ residualOutside F right ∨
      ∃ petal : {edge // edge ∈ (residualMatching F).matching.petals},
        residualPetalComponent F left petal ≠
          residualPetalComponent F right petal := by
  by_cases outsideDifferent : residualOutside F left ≠ residualOutside F right
  · exact Or.inl outsideDifferent
  · apply Or.inr
    push_neg at outsideDifferent
    by_contra noComponent
    push_neg at noComponent
    exact different <|
      residual_eq_of_outside_eq_of_components_eq
        F left right outsideDifferent noComponent

/-- A same-cell component distinction preserves occupation on both sides. -/
structure OccupiedPetalDistinction
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) where
  petal : {edge // edge ∈ (residualMatching F).matching.petals}
  leftOccupied : (residualPetalComponent F left petal).Nonempty
  rightOccupied : (residualPetalComponent F right petal).Nonempty
  contentDifferent : residualPetalComponent F left petal ≠
    residualPetalComponent F right petal

/--
Inside one Venn cell, unequal residual parents differ outside the selected
support or inside a petal occupied by both parents.
-/
theorem sameCell_distinct_outside_or_occupiedPetal
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameCell : residualOverlapCell F left = residualOverlapCell F right)
    (different : PrivateWitnessReduction.residual F left ≠
      PrivateWitnessReduction.residual F right) :
    residualOutside F left ≠ residualOutside F right ∨
      Nonempty (OccupiedPetalDistinction F left right) := by
  rcases distinctResidual_outside_or_petalComponent
      F left right different with outsideDifferent | ⟨petal, componentDifferent⟩
  · exact Or.inl outsideDifferent
  · apply Or.inr
    have occupancy := sameCell_component_occupancy_iff
      F left right sameCell petal
    have leftOccupied : (residualPetalComponent F left petal).Nonempty := by
      by_contra leftNotOccupied
      have leftEmpty := Finset.not_nonempty_iff_eq_empty.mp leftNotOccupied
      have rightNotOccupied :
          Not (residualPetalComponent F right petal).Nonempty :=
        fun rightOccupied => leftNotOccupied (occupancy.mpr rightOccupied)
      have rightEmpty := Finset.not_nonempty_iff_eq_empty.mp rightNotOccupied
      exact componentDifferent (leftEmpty.trans rightEmpty.symm)
    exact ⟨{
      petal := petal
      leftOccupied := leftOccupied
      rightOccupied := occupancy.mp leftOccupied
      contentDifferent := componentDifferent }⟩

/-- A singleton-cell residual with empty outside part is the selected petal. -/
theorem residual_eq_petal_of_singletonCell_of_outside_empty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (singletonCell : residualOverlapCell F source = {petal})
    (outsideEmpty : residualOutside F source = ∅) :
    PrivateWitnessReduction.residual F source = petal.val := by
  classical
  have residual_subset : PrivateWitnessReduction.residual F source ⊆ petal.val := by
    intro point point_mem
    have point_support : point ∈ residualSupport F := by
      by_contra point_not_support
      have point_outside : point ∈ residualOutside F source := by
        exact Finset.mem_sdiff.mpr ⟨point_mem, point_not_support⟩
      rw [outsideEmpty] at point_outside
      exact Finset.notMem_empty point point_outside
    rcases Finset.mem_biUnion.mp point_support with
      ⟨chosen, chosen_mem, point_chosen⟩
    let selected : {edge // edge ∈ (residualMatching F).matching.petals} :=
      ⟨chosen, chosen_mem⟩
    have selected_mem : selected ∈ residualOverlapCell F source := by
      apply (petal_mem_residualOverlapCell_iff F source selected).mpr
      exact ⟨point, Finset.mem_inter.mpr ⟨point_mem, point_chosen⟩⟩
    rw [singletonCell, Finset.mem_singleton] at selected_mem
    have chosen_eq : chosen = petal.val := congrArg Subtype.val selected_mem
    simpa [chosen_eq] using point_chosen
  apply Finset.eq_of_subset_of_card_le residual_subset
  rw [PrivateWitnessReduction.residual_card F source]
  exact Nat.le_of_eq <|
    (PrivateWitnessReduction.residualFamily F).uniform petal.val
      ((residualMatching F).matching.petals_subset petal.property)

/--
Distinct same-cell parents force a nontrivial split: outside content survives
on one side, or the common Venn cell occupies at least two disjoint petals.
-/
theorem sameCell_distinct_forces_nontrivialSplit
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameCell : residualOverlapCell F left = residualOverlapCell F right)
    (different : PrivateWitnessReduction.residual F left ≠
      PrivateWitnessReduction.residual F right) :
    (residualOutside F left).Nonempty ∨
      (residualOutside F right).Nonempty ∨
      2 ≤ (residualOverlapCell F left).card := by
  classical
  by_cases leftOutside : (residualOutside F left).Nonempty
  · exact Or.inl leftOutside
  · apply Or.inr
    by_cases rightOutside : (residualOutside F right).Nonempty
    · exact Or.inl rightOutside
    · apply Or.inr
      by_contra cellSmall
      have cellCardOne : (residualOverlapCell F left).card = 1 := by
        have one_le : 1 ≤ (residualOverlapCell F left).card :=
          Finset.one_le_card.mpr (residualOverlapCell_nonempty F left)
        omega
      rcases Finset.card_eq_one.mp cellCardOne with ⟨petal, leftCell⟩
      have rightCell : residualOverlapCell F right = {petal} := by
        rw [← leftCell, ← sameCell]
      have leftOutsideEmpty : residualOutside F left = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp leftOutside
      have rightOutsideEmpty : residualOutside F right = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp rightOutside
      exact different <|
        (residual_eq_petal_of_singletonCell_of_outside_empty
          F left petal leftCell leftOutsideEmpty).trans
        (residual_eq_petal_of_singletonCell_of_outside_empty
          F right petal rightCell rightOutsideEmpty).symm

/-- Nonempty outside content splits a residual into two strict lower-rank parts. -/
theorem outside_nonempty_gives_proper_rank_split
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (outsideNonempty : (residualOutside F source).Nonempty) :
    (PrivateWitnessReduction.residual F source ∩ residualSupport F).Nonempty ∧
      (PrivateWitnessReduction.residual F source ∩ residualSupport F).card < r + 1 ∧
      (residualOutside F source).card < r + 1 := by
  classical
  have insideNonempty :
      (PrivateWitnessReduction.residual F source ∩ residualSupport F).Nonempty := by
    rcases residualOverlapCell_nonempty F source with ⟨petal, petal_mem⟩
    rcases (petal_mem_residualOverlapCell_iff F source petal).mp petal_mem with
      ⟨point, point_component⟩
    rcases Finset.mem_inter.mp point_component with
      ⟨point_residual, point_petal⟩
    have point_support : point ∈ residualSupport F :=
      Finset.mem_biUnion.mpr ⟨petal.val, petal.property, point_petal⟩
    exact ⟨point, Finset.mem_inter.mpr ⟨point_residual, point_support⟩⟩
  have accounting := residual_support_rank_accounting F source
  have insidePositive :
      0 < (PrivateWitnessReduction.residual F source ∩ residualSupport F).card :=
    Finset.card_pos.mpr insideNonempty
  have outsidePositive : 0 < (residualOutside F source).card :=
    Finset.card_pos.mpr outsideNonempty
  exact ⟨insideNonempty, by omega, by omega⟩

/-- An occupied component has strict lower rank when its cell uses two petals. -/
theorem occupiedPetal_card_lt_of_two_le_cell
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (_petal_mem : petal ∈ residualOverlapCell F source)
    (two_le : 2 ≤ (residualOverlapCell F source).card) :
    (residualPetalComponent F source petal).card < r + 1 := by
  classical
  obtain ⟨other, other_mem, other_ne⟩ :=
    Finset.exists_mem_ne (by omega : 1 < (residualOverlapCell F source).card) petal
  rcases (petal_mem_residualOverlapCell_iff F source other).mp other_mem with
    ⟨point, point_component⟩
  rcases Finset.mem_inter.mp point_component with
    ⟨point_residual, point_other⟩
  have petals_disjoint : Disjoint other.val petal.val := by
    simpa using
      (residualMatching F).matching.residuals_disjoint
        other.val petal.val other.property petal.property
        (fun same => other_ne (Subtype.ext same))
  have point_not_petal : point ∉ petal.val := fun point_petal =>
    Finset.disjoint_left.mp petals_disjoint point_other point_petal
  have component_subset : residualPetalComponent F source petal ⊆
      PrivateWitnessReduction.residual F source :=
    Finset.inter_subset_left
  have component_strict : residualPetalComponent F source petal ⊂
      PrivateWitnessReduction.residual F source :=
    (Finset.ssubset_iff_of_subset component_subset).mpr
      ⟨point, point_residual, fun point_component =>
        point_not_petal (Finset.mem_inter.mp point_component).2⟩
  rw [← PrivateWitnessReduction.residual_card F source]
  exact Finset.card_lt_card component_strict

/--
The rank-decreasing content forced by unequal parents in one Venn cell.
Outside content gives a two-part strict split; otherwise a specifically
different occupied petal component has strict lower rank on both sides.
-/
inductive SameVennParentRankSplit
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Type
  | leftOutside
      (outsideNonempty : (residualOutside F left).Nonempty)
      (insideLower :
        (PrivateWitnessReduction.residual F left ∩ residualSupport F).card < r + 1)
      (outsideLower : (residualOutside F left).card < r + 1) :
      SameVennParentRankSplit F left right
  | rightOutside
      (outsideNonempty : (residualOutside F right).Nonempty)
      (insideLower :
        (PrivateWitnessReduction.residual F right ∩ residualSupport F).card < r + 1)
      (outsideLower : (residualOutside F right).card < r + 1) :
      SameVennParentRankSplit F left right
  | occupiedPetal
      (distinction : OccupiedPetalDistinction F left right)
      (leftLower :
        (residualPetalComponent F left distinction.petal).card < r + 1)
      (rightLower :
        (residualPetalComponent F right distinction.petal).card < r + 1) :
      SameVennParentRankSplit F left right

/-- Same-cell unequal parents always provide explicit strict rank descent. -/
theorem sameCell_distinct_has_rankSplit
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameCell : residualOverlapCell F left = residualOverlapCell F right)
    (different : PrivateWitnessReduction.residual F left ≠
      PrivateWitnessReduction.residual F right) :
    Nonempty (SameVennParentRankSplit F left right) := by
  classical
  by_cases leftOutside : (residualOutside F left).Nonempty
  · have proper := outside_nonempty_gives_proper_rank_split F left leftOutside
    exact ⟨SameVennParentRankSplit.leftOutside
      leftOutside proper.2.1 proper.2.2⟩
  · by_cases rightOutside : (residualOutside F right).Nonempty
    · have proper := outside_nonempty_gives_proper_rank_split F right rightOutside
      exact ⟨SameVennParentRankSplit.rightOutside
        rightOutside proper.2.1 proper.2.2⟩
    · have two_le : 2 ≤ (residualOverlapCell F left).card := by
        rcases sameCell_distinct_forces_nontrivialSplit
            F left right sameCell different with leftNonempty | rightNonempty | split
        · exact False.elim (leftOutside leftNonempty)
        · exact False.elim (rightOutside rightNonempty)
        · exact split
      rcases sameCell_distinct_outside_or_occupiedPetal
          F left right sameCell different with outsideDifferent | occupied
      · have leftEmpty := Finset.not_nonempty_iff_eq_empty.mp leftOutside
        have rightEmpty := Finset.not_nonempty_iff_eq_empty.mp rightOutside
        exact False.elim (outsideDifferent (leftEmpty.trans rightEmpty.symm))
      · rcases occupied with ⟨distinction⟩
        have leftPetalMem :
            distinction.petal ∈ residualOverlapCell F left :=
          (petal_mem_residualOverlapCell_iff F left distinction.petal).mpr
            distinction.leftOccupied
        have rightPetalMem :
            distinction.petal ∈ residualOverlapCell F right := by
          rw [← sameCell]
          exact leftPetalMem
        have rightTwo : 2 ≤ (residualOverlapCell F right).card := by
          rw [← sameCell]
          exact two_le
        exact ⟨SameVennParentRankSplit.occupiedPetal distinction
          (occupiedPetal_card_lt_of_two_le_cell
            F left distinction.petal leftPetalMem two_le)
          (occupiedPetal_card_lt_of_two_le_cell
            F right distinction.petal rightPetalMem rightTwo)⟩

/-- The surviving one-step same-code parent branch carries strict rank descent. -/
theorem residualParentVennMerge_has_rankSplit
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameCode : residualOverlapCode F noSunflower left =
      residualOverlapCode F noSunflower right)
    (parentMerge : ResidualParentVennMerge F left right) :
    Nonempty (SameVennParentRankSplit F left right) :=
  sameCell_distinct_has_rankSplit F left right
    (residualOverlapCell_eq_of_code_eq F noSunflower left right sameCode)
    parentMerge.parentDistinct

/--
The exact one-step pincer. A merge is resolved by the local `Fin k` residual
slot, separated by the finite second-level Venn code, or left as a distinct
residual parent inside one finite Venn cell.
-/
theorem OneStepPairMerge.exhausts_boundedSlot_or_vennCode_or_sameVennParent
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (merge : OneStepPairMerge F left right)
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    BoundedFiberSlotDistinction F noSunflower left right ∨
      residualOverlapCode F noSunflower left ≠
        residualOverlapCode F noSunflower right ∨
      (residualOverlapCode F noSunflower left =
          residualOverlapCode F noSunflower right ∧
        Nonempty (ResidualParentVennMerge F left right)) := by
  by_cases sameParent :
      PrivateWitnessReduction.residual F left =
        PrivateWitnessReduction.residual F right
  · apply Or.inl
    exact ⟨sameParent,
      PrivateWitnessReduction.residualFiberSlot_ne_of_sameResidual_of_nonSkin
        F noSunflower left right sameParent
        (MinimalBlocker.distinct_privateWitness_not_endpointSkin
          F left right merge.sourceDistinct)⟩
  · by_cases sameCode : residualOverlapCode F noSunflower left =
        residualOverlapCode F noSunflower right
    · exact Or.inr <| Or.inr ⟨sameCode, ⟨⟨merge, sameParent⟩⟩⟩
    · exact Or.inr <| Or.inl sameCode

/-- Generated reachability specialized to the literal rank-one endpoint. -/
inductive RankOneReach
    {alpha : Type}
    [DecidableEq alpha] :
    (r : Nat) →
    (F : Concrete.UniformSetFamily alpha (r + 1)) →
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) →
    {x // x ∈ MinimalBlocker.minimalBlocker (rankOneTerminalFamily r F)} → Prop
  | stop
      (F : Concrete.UniformSetFamily alpha 1)
      (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
      RankOneReach 0 F source source
  | next
      {r : Nat}
      (F : Concrete.UniformSetFamily alpha (r + 2))
      (source : {x // x ∈ MinimalBlocker.minimalBlocker F})
      (target : {x // x ∈ MinimalBlocker.minimalBlocker
        (PrivateWitnessReduction.residualFamily F)})
      {carrier : {x // x ∈ MinimalBlocker.minimalBlocker
        (rankOneTerminalFamily r
          (PrivateWitnessReduction.residualFamily F))}}
      (incident : NextRel F source target)
      (tail : RankOneReach r
        (PrivateWitnessReduction.residualFamily F) target carrier) :
      RankOneReach (r + 1) F source carrier

/--
A collision occurs at the current deletion step or after two distinct next
coordinates continue to one rank-one carrier.
-/
inductive PairMergeWitness
    {alpha : Type}
    [DecidableEq alpha] :
    (r : Nat) →
    (F : Concrete.UniformSetFamily alpha (r + 1)) →
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) → Type
  | here
      {r : Nat}
      {F : Concrete.UniformSetFamily alpha (r + 2)}
      {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
      (merge : OneStepPairMerge F left right) :
      PairMergeWitness (r + 1) F left right
  | later
      {r : Nat}
      {F : Concrete.UniformSetFamily alpha (r + 2)}
      {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
      (leftTarget rightTarget : {x // x ∈ MinimalBlocker.minimalBlocker
        (PrivateWitnessReduction.residualFamily F)})
      (leftIncident : NextRel F left leftTarget)
      (rightIncident : NextRel F right rightTarget)
      (tail : PairMergeWitness r
        (PrivateWitnessReduction.residualFamily F) leftTarget rightTarget) :
      PairMergeWitness (r + 1) F left right

/-- The recursively selected rank-one carrier is genuinely reachable. -/
theorem rankOneGeneratedCarrier_reachable
    {alpha : Type}
    [DecidableEq alpha]
    (r : Nat)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    RankOneReach r F source (rankOneGeneratedCarrier r F source) := by
  induction r with
  | zero =>
      exact RankOneReach.stop F source
  | succ r ih =>
      let target := Classical.choice (nextCoordinate_nonempty F source)
      exact RankOneReach.next F source target.val target.property
        (ih (PrivateWitnessReduction.residualFamily F) target.val)

/-- Two distinct sources reaching one rank-one carrier force a local merge. -/
theorem pairMergeWitness_of_sharedRankOneCarrier
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    {carrier : {x // x ∈ MinimalBlocker.minimalBlocker
      (rankOneTerminalFamily r F)}}
    (distinct : left ≠ right)
    (leftReach : RankOneReach r F left carrier)
    (rightReach : RankOneReach r F right carrier) :
    Nonempty (PairMergeWitness r F left right) := by
  induction r with
  | zero =>
      cases leftReach
      cases rightReach
      exact False.elim (distinct rfl)
  | succ r ih =>
      cases leftReach with
      | next F left leftTarget leftIncident leftTail =>
          cases rightReach with
          | next _ right rightTarget rightIncident rightTail =>
              by_cases sameTarget : leftTarget = rightTarget
              · subst rightTarget
                exact ⟨PairMergeWitness.here
                  ⟨leftTarget, leftIncident, rightIncident, distinct⟩⟩
              · rcases ih sameTarget leftTail rightTail with ⟨tailWitness⟩
                exact ⟨PairMergeWitness.later
                  leftTarget rightTarget leftIncident rightIncident tailWitness⟩

/--
The complete pair-local outcome ledger. The third constructor names the exact
branch left after the bounded slot and finite Venn code have both failed.
-/
inductive PairMergeOutcome
    {alpha : Type}
    [DecidableEq alpha] :
    (r : Nat) →
    (F : Concrete.UniformSetFamily alpha (r + 1)) →
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) → Type
  | boundedHere
      {r : Nat}
      {F : Concrete.UniformSetFamily alpha (r + 2)}
      {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
      (merge : OneStepPairMerge F left right)
      (noSunflower : Not (Concrete.HasSunflower 3 F))
      (bounded : BoundedFiberSlotDistinction F noSunflower left right) :
      PairMergeOutcome (r + 1) F left right
  | vennSeparatedHere
      {r : Nat}
      {F : Concrete.UniformSetFamily alpha (r + 2)}
      {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
      (merge : OneStepPairMerge F left right)
      (noSunflower : Not (Concrete.HasSunflower 3 F))
      (codeDifferent : residualOverlapCode F noSunflower left ≠
        residualOverlapCode F noSunflower right) :
      PairMergeOutcome (r + 1) F left right
  | sameVennParentHere
      {r : Nat}
      {F : Concrete.UniformSetFamily alpha (r + 2)}
      {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
      (merge : OneStepPairMerge F left right)
      (noSunflower : Not (Concrete.HasSunflower 3 F))
      (sameCode : residualOverlapCode F noSunflower left =
        residualOverlapCode F noSunflower right)
      (parentMerge : Nonempty (ResidualParentVennMerge F left right))
      (rankSplit : Nonempty (SameVennParentRankSplit F left right)) :
      PairMergeOutcome (r + 1) F left right
  | later
      {r : Nat}
      {F : Concrete.UniformSetFamily alpha (r + 2)}
      {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
      (leftTarget rightTarget : {x // x ∈ MinimalBlocker.minimalBlocker
        (PrivateWitnessReduction.residualFamily F)})
      (leftIncident : NextRel F left leftTarget)
      (rightIncident : NextRel F right rightTarget)
      (tail : PairMergeOutcome r
        (PrivateWitnessReduction.residualFamily F) leftTarget rightTarget) :
      PairMergeOutcome (r + 1) F left right

/-- Every actual pair merge inhabits the finite/local outcome ledger. -/
theorem PairMergeWitness.outcome_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (witness : PairMergeWitness r F left right)
    (noSunflower : Not (Concrete.HasSunflower 3 F)) :
    Nonempty (PairMergeOutcome r F left right) := by
  induction witness with
  | here merge =>
      rcases merge.exhausts_boundedSlot_or_vennCode_or_sameVennParent
          noSunflower with bounded | codeDifferent | sameVennParent
      · exact ⟨PairMergeOutcome.boundedHere merge noSunflower bounded⟩
      · exact ⟨PairMergeOutcome.vennSeparatedHere
          merge noSunflower codeDifferent⟩
      · rcases sameVennParent.2 with ⟨parentMerge⟩
        exact ⟨PairMergeOutcome.sameVennParentHere
          merge noSunflower sameVennParent.1 ⟨parentMerge⟩
          (residualParentVennMerge_has_rankSplit
            _ noSunflower _ _ sameVennParent.1 parentMerge)⟩
  | later leftTarget rightTarget leftIncident rightIncident tail ih =>
      rcases ih
          (PrivateWitnessReduction.residualFamily_noSunflower noSunflower) with
        ⟨tailOutcome⟩
      exact ⟨PairMergeOutcome.later
        leftTarget rightTarget leftIncident rightIncident tailOutcome⟩

/-- Equality of the injective rank-one seed slot is equality of its carrier. -/
theorem rankOneGeneratedCarrier_eq_of_terminalSeedSlot_eq
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower 3 F))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameSlot : rankOneTerminalSeedSlot F noSunflower left =
      rankOneTerminalSeedSlot F noSunflower right) :
    rankOneGeneratedCarrier r F left = rankOneGeneratedCarrier r F right := by
  apply (PopulationInheritance.traditionalSeedProfileEmbedding
    (r := 0) (k := 3) (cutoff := 1)
    (by decide)
    (rankOneTerminalFamily r F)
    (rankOneTerminalFamily_noSunflower r F noSunflower)).injective
  simpa only [rankOneTerminalSeedSlot] using sameSlot

/--
The former global residual-parent collision is now localized: its two concrete
generated paths necessarily merge at some deletion rank.
-/
theorem generatedResidualParentCollision_hasPairMergeWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {classifiers : ResidualParentClassifiers F}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (collision : GeneratedResidualParentTensorCollision
      F noSunflower classifiers left right) :
    Nonempty (PairMergeWitness r F left right) := by
  have distinct : left ≠ right := by
    intro same
    subst right
    exact collision.2.2.2.2 rfl
  have sameSeedSlot : rankOneTerminalSeedSlot F noSunflower left =
      rankOneTerminalSeedSlot F noSunflower right :=
    rankOneTerminalSeedSlot_eq_of_generatedResidualProfileSlot_eq
      F noSunflower left right collision.2.2.2.1
  have sameCarrier : rankOneGeneratedCarrier r F left =
      rankOneGeneratedCarrier r F right :=
    rankOneGeneratedCarrier_eq_of_terminalSeedSlot_eq
      F noSunflower left right sameSeedSlot
  exact pairMergeWitness_of_sharedRankOneCarrier distinct
    (rankOneGeneratedCarrier_reachable r F left)
    (sameCarrier ▸ rankOneGeneratedCarrier_reachable r F right)

/--
The exact pair-local form of the remaining generated-code collision. The
former global residual-parent branch is either consumed by finite local data,
or it survives only as a same-Venn-cell parent distinction at one merge rank.
-/
theorem generatedResidualParentCollision_pairLocalExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {classifiers : ResidualParentClassifiers F}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (collision : GeneratedResidualParentTensorCollision
      F noSunflower classifiers left right) :
    Nonempty (PairMergeOutcome r F left right) := by
  rcases generatedResidualParentCollision_hasPairMergeWitness collision with
    ⟨witness⟩
  exact witness.outcome_nonempty noSunflower

end PairLocalizedReferenceDivergence
end V2
end SunflowerAASC
