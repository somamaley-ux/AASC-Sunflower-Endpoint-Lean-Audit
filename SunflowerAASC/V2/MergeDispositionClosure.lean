import SunflowerAASC.V2.PairLocalizedReferenceDivergence

namespace SunflowerAASC
namespace V2
namespace MergeDispositionClosure

open CompleteRoleRefinement
open PairLocalizedReferenceDivergence

/--
A literal charge class for two roots with one private-residual parent.  Its
multiplicity bound is the elementary sunflower bound on that residual fibre.
-/
structure BoundedResidualCharge
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) where
  parent : Finset alpha
  left_mem : left ∈ PrivateWitnessReduction.residualFiber F parent
  right_mem : right ∈ PrivateWitnessReduction.residualFiber F parent
  sourceDistinct : left ≠ right
  multiplicity_lt :
    (PrivateWitnessReduction.residualFiber F parent).card < k

/-- A same-parent bounded-slot distinction supplies a concrete charge class. -/
noncomputable def boundedResidualChargeOfDistinction
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (distinct : left ≠ right)
    (bounded : BoundedFiberSlotDistinction F noSunflower left right) :
    BoundedResidualCharge F noSunflower left right where
  parent := PrivateWitnessReduction.residual F left
  left_mem := PrivateWitnessReduction.mem_residualFiber_iff.mpr rfl
  right_mem :=
    PrivateWitnessReduction.mem_residualFiber_iff.mpr bounded.1.symm
  sourceDistinct := distinct
  multiplicity_lt :=
    PrivateWitnessReduction.residualFiber_card_lt F noSunflower _

/--
An explicit two-piece reconstruction of one private residual.  Both pieces
have rank strictly below the residual rank, and their union is the parent.
-/
structure ProperResidualDecomposition
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) where
  first : Finset alpha
  second : Finset alpha
  disjoint : Disjoint first second
  reconstruct : first ∪ second = PrivateWitnessReduction.residual F source
  first_card_lt : first.card < r + 1
  second_card_lt : second.card < r + 1

/-- Nonempty outside content gives the literal inside/outside reconstruction. -/
noncomputable def outsideProperResidualDecomposition
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (outsideNonempty :
      (PairLocalizedReferenceDivergence.residualOutside F source).Nonempty) :
    ProperResidualDecomposition F source := by
  let inside :=
    PrivateWitnessReduction.residual F source ∩
      PairLocalizedReferenceDivergence.residualSupport F
  let outside := PairLocalizedReferenceDivergence.residualOutside F source
  have proper :=
    PairLocalizedReferenceDivergence.outside_nonempty_gives_proper_rank_split
      F source outsideNonempty
  refine
    { first := inside
      second := outside
      disjoint := ?_
      reconstruct := ?_
      first_card_lt := proper.2.1
      second_card_lt := proper.2.2 }
  · unfold inside outside PairLocalizedReferenceDivergence.residualOutside
    exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      Finset.disjoint_sdiff
  · unfold inside outside PairLocalizedReferenceDivergence.residualOutside
    rw [Finset.union_comm, Finset.sdiff_union_inter]

/--
One occupied matching-petal component and its complement reconstruct the
residual, with both pieces of strictly lower rank.
-/
noncomputable def occupiedPetalProperResidualDecomposition
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (petal : {edge // edge ∈
      (PairLocalizedReferenceDivergence.residualMatching F).matching.petals})
    (occupied :
      (PairLocalizedReferenceDivergence.residualPetalComponent
        F source petal).Nonempty)
    (componentLower :
      (PairLocalizedReferenceDivergence.residualPetalComponent
        F source petal).card < r + 1) :
    ProperResidualDecomposition F source := by
  let component :=
    PairLocalizedReferenceDivergence.residualPetalComponent F source petal
  let remainder := PrivateWitnessReduction.residual F source \ component
  have component_subset :
      component ⊆ PrivateWitnessReduction.residual F source := by
    exact Finset.inter_subset_left
  have componentPositive : 0 < component.card :=
    Finset.card_pos.mpr occupied
  have remainderLower : remainder.card < r + 1 := by
    unfold remainder
    rw [Finset.card_sdiff_of_subset component_subset,
      PrivateWitnessReduction.residual_card F source]
    omega
  refine
    { first := component
      second := remainder
      disjoint := ?_
      reconstruct := ?_
      first_card_lt := componentLower
      second_card_lt := remainderLower }
  · unfold remainder
    exact Finset.disjoint_sdiff
  · unfold remainder
    exact Finset.union_sdiff_of_subset component_subset

/--
The concrete strict reconstruction carried by a same-Venn parent split.

This is deliberately local: it decomposes one or both residual parents.  It
does not yet assert a bounded-overlap cover of the entire dense fibre.  That
globalization is represented separately by rank-weighted charging.
-/
inductive StrictLowerRankReconstruction
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Type
  | left
      (decomposition : ProperResidualDecomposition F left) :
      StrictLowerRankReconstruction F left right
  | right
      (decomposition : ProperResidualDecomposition F right) :
      StrictLowerRankReconstruction F left right
  | both
      (leftDecomposition : ProperResidualDecomposition F left)
      (rightDecomposition : ProperResidualDecomposition F right) :
      StrictLowerRankReconstruction F left right

/-- Every previously extracted same-Venn rank split reconstructs lower-rank data. -/
noncomputable def strictLowerRankReconstructionOfSameVennSplit
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (split : SameVennParentRankSplit F left right) :
    StrictLowerRankReconstruction F left right := by
  cases split with
  | leftOutside outsideNonempty _insideLower _outsideLower =>
      exact StrictLowerRankReconstruction.left
        (outsideProperResidualDecomposition F left outsideNonempty)
  | rightOutside outsideNonempty _insideLower _outsideLower =>
      exact StrictLowerRankReconstruction.right
        (outsideProperResidualDecomposition F right outsideNonempty)
  | occupiedPetal distinction leftLower rightLower =>
      exact StrictLowerRankReconstruction.both
        (occupiedPetalProperResidualDecomposition
          F left distinction.petal distinction.leftOccupied leftLower)
        (occupiedPetalProperResidualDecomposition
          F right distinction.petal distinction.rightOccupied rightLower)

/--
The unconditional local collision ledger.  A real merge either already
contains a three-petal sunflower, is separated by finite Venn profile, belongs
to a residual fibre of size below three, or reconstructs through strict
lower-rank pieces.
-/
inductive ThreePetalOneStepMergeDisposition
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Type
  | sunflower
      (witness : Concrete.HasSunflower 3 F) :
      ThreePetalOneStepMergeDisposition F left right
  | profileSeparated
      (noSunflower : Not (Concrete.HasSunflower 3 F))
      (different :
        PairLocalizedReferenceDivergence.residualOverlapCode
            F noSunflower left ≠
          PairLocalizedReferenceDivergence.residualOverlapCode
            F noSunflower right) :
      ThreePetalOneStepMergeDisposition F left right
  | boundedCharge
      (noSunflower : Not (Concrete.HasSunflower 3 F))
      (charge : BoundedResidualCharge F noSunflower left right) :
      ThreePetalOneStepMergeDisposition F left right
  | rankSplit
      (noSunflower : Not (Concrete.HasSunflower 3 F))
      (sameProfile :
        PairLocalizedReferenceDivergence.residualOverlapCode
            F noSunflower left =
          PairLocalizedReferenceDivergence.residualOverlapCode
            F noSunflower right)
      (reconstruction : StrictLowerRankReconstruction F left right) :
      ThreePetalOneStepMergeDisposition F left right

/--
Every generated one-step merge has a concrete disposition.  No Hall law,
injective selector, Current-Reference binding, or endpoint bound is assumed.
-/
theorem oneStepPairMerge_disposition
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (merge : OneStepPairMerge F left right) :
    Nonempty (ThreePetalOneStepMergeDisposition F left right) := by
  by_cases noSunflower : Not (Concrete.HasSunflower 3 F)
  · rcases merge.exhausts_boundedSlot_or_vennCode_or_sameVennParent
        noSunflower with bounded | separated | sameVenn
    · exact ⟨ThreePetalOneStepMergeDisposition.boundedCharge noSunflower
        (boundedResidualChargeOfDistinction
          F noSunflower left right merge.sourceDistinct bounded)⟩
    · exact ⟨ThreePetalOneStepMergeDisposition.profileSeparated
        noSunflower separated⟩
    · rcases sameVenn.2 with ⟨parentMerge⟩
      rcases PairLocalizedReferenceDivergence.residualParentVennMerge_has_rankSplit
          F noSunflower left right sameVenn.1 parentMerge with ⟨split⟩
      exact ⟨ThreePetalOneStepMergeDisposition.rankSplit
        noSunflower sameVenn.1
          (strictLowerRankReconstructionOfSameVennSplit split)⟩
  · exact ⟨ThreePetalOneStepMergeDisposition.sunflower
      (Classical.not_not.mp noSunflower)⟩

/--
Agreement on support, finite constraint profile, forced AASC role, and the
second-level residual Venn profile is the genuine fine fibre used at a merge.
-/
structure FineFiberAgreement
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower 3 F))
    (classifiers : ResidualParentExhaustion.ResidualParentClassifiers F)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Prop where
  sameSupport :
    BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
        ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
        ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩
  sameConstraintProfile :
    classifiers.constraintProfile left = classifiers.constraintProfile right
  sameRole : classifiers.forcedRole left = classifiers.forcedRole right
  sameResidualVennProfile :
    PairLocalizedReferenceDivergence.residualOverlapCode
        F noSunflower left =
      PairLocalizedReferenceDivergence.residualOverlapCode
        F noSunflower right

/-- The two surviving dispositions inside one genuine fine fibre. -/
inductive FineFiberMergeDisposition
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower 3 F))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Type
  | boundedCharge
      (charge : BoundedResidualCharge F noSunflower left right) :
      FineFiberMergeDisposition F noSunflower left right
  | rankSplit
      (reconstruction : StrictLowerRankReconstruction F left right) :
      FineFiberMergeDisposition F noSunflower left right

/--
Inside the genuine support/profile/role/Venn fibre, a merge is bounded or has
a local strict-rank reconstruction candidate.  The finite-profile separation
branch is impossible by the fibre definition, and the sunflower branch is the
fixed countercase.  This theorem does not promote the local candidate to a
global bounded-overlap reconstruction.
-/
theorem fineFiberMerge_disposition
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {classifiers : ResidualParentExhaustion.ResidualParentClassifiers F}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (agreement : FineFiberAgreement
      F noSunflower classifiers left right)
    (merge : OneStepPairMerge F left right) :
    Nonempty (FineFiberMergeDisposition F noSunflower left right) := by
  rcases merge.exhausts_boundedSlot_or_vennCode_or_sameVennParent
      noSunflower with bounded | separated | sameVenn
  · exact ⟨FineFiberMergeDisposition.boundedCharge
      (boundedResidualChargeOfDistinction
        F noSunflower left right merge.sourceDistinct bounded)⟩
  · exact False.elim (separated agreement.sameResidualVennProfile)
  · rcases sameVenn.2 with ⟨parentMerge⟩
    rcases PairLocalizedReferenceDivergence.residualParentVennMerge_has_rankSplit
        F noSunflower left right sameVenn.1 parentMerge with ⟨split⟩
    exact ⟨FineFiberMergeDisposition.rankSplit
      (strictLowerRankReconstructionOfSameVennSplit split)⟩

end MergeDispositionClosure
end V2
end SunflowerAASC
