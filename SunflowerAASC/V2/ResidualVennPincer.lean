import Mathlib.Combinatorics.SetFamily.Shadow
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.SymmDiff
import SunflowerAASC.V2.PrivateWitnessReduction
import SunflowerAASC.V2.CorpusMachinery
import SunflowerAASC.V2.WitnessCompression

namespace SunflowerAASC
namespace V2
namespace ResidualVennPincer

open scoped FinsetFamily symmDiff

/-- A private residual is a distinguished one-step shadow of its private edge. -/
theorem residual_mem_privateWitnessShadow
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    PrivateWitnessReduction.residual F x ∈
      ∂ (MinimalBlocker.privateWitnessFamily F).edges := by
  apply Finset.erase_mem_shadow
  · simp [MinimalBlocker.privateWitnessFamily]
  · exact MinimalBlocker.privateEdge_contains F x

/-- The whole residual family lies in the Mathlib shadow of the private witnesses. -/
theorem residualFamily_subset_privateWitnessShadow
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    (PrivateWitnessReduction.residualFamily F).edges ⊆
      ∂ (MinimalBlocker.privateWitnessFamily F).edges := by
  intro edge edge_mem
  rcases PrivateWitnessReduction.mem_residualFamily_iff.mp edge_mem with
    ⟨x, rfl⟩
  exact residual_mem_privateWitnessShadow F x

/-- The second canonical matching is taken inside the rank-lowered residual family. -/
noncomputable def residualMatching
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    Concrete.MaximalFiniteCoreLinkMatching
      (PrivateWitnessReduction.residualFamily F) (∅ : Finset alpha) :=
  EffectiveBlocker.emptyCoreMaximalMatching
    (PrivateWitnessReduction.residualFamily F)

/--
The overlapping Venn cell of a private residual: all second-level matching
petals met by that residual.  Unlike the first support layer, this cell can
contain several petals.
-/
noncomputable def residualOverlapCell
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    Finset {edge // edge ∈ (residualMatching F).matching.petals} := by
  classical
  exact Finset.univ.filter fun edge =>
    Not (Disjoint (PrivateWitnessReduction.residual F x) edge.val)

theorem residual_mem_residualFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    PrivateWitnessReduction.residual F x ∈
      (PrivateWitnessReduction.residualFamily F).edges := by
  exact PrivateWitnessReduction.mem_residualFamily_iff.mpr ⟨x, rfl⟩

theorem residualOverlapCell_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (residualOverlapCell F x).Nonempty := by
  classical
  let edge := PrivateWitnessReduction.residual F x
  have edge_mem : edge ∈
      (PrivateWitnessReduction.residualFamily F).edges :=
    residual_mem_residualFamily F x
  have edge_nonempty : edge.Nonempty := by
    apply Finset.card_pos.mp
    rw [show edge.card = r + 1 from
      PrivateWitnessReduction.residual_card F x]
    exact Nat.zero_lt_succ r
  rcases (residualMatching F).maximal edge edge_mem
      (Finset.empty_subset edge) with selected | conflict
  · let chosen : {edge // edge ∈ (residualMatching F).matching.petals} :=
      ⟨edge, selected⟩
    refine ⟨chosen, Finset.mem_filter.mpr ⟨Finset.mem_univ chosen, ?_⟩⟩
    rcases edge_nonempty with ⟨y, y_mem⟩
    exact Finset.not_disjoint_iff.mpr ⟨y, y_mem, y_mem⟩
  · rcases conflict with ⟨chosenEdge, chosen_mem, not_disjoint⟩
    let chosen : {edge // edge ∈ (residualMatching F).matching.petals} :=
      ⟨chosenEdge, chosen_mem⟩
    refine ⟨chosen, Finset.mem_filter.mpr ⟨Finset.mem_univ chosen, ?_⟩⟩
    simpa [edge] using not_disjoint

/-- No residual Venn cell can occupy `k` second-level matching petals. -/
theorem residualOverlapCell_card_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (residualOverlapCell F x).card < k := by
  classical
  calc
    (residualOverlapCell F x).card ≤
        (Finset.univ : Finset
          {edge // edge ∈ (residualMatching F).matching.petals}).card :=
      Finset.card_filter_le _ _
    _ = (residualMatching F).matching.petals.card := by simp
    _ < k :=
      Concrete.finiteCoreLinkMatching_card_lt_of_noSunflower
        (PrivateWitnessReduction.residualFamily_noSunflower noSunflower)
        (residualMatching F).matching

/-- Encode the second overlapping matching layer in the fixed alphabet `Fin k`. -/
noncomputable def residualOverlapCode
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    Finset (Fin k) :=
  (residualOverlapCell F x).map
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
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (residualOverlapCode F noSunflower x).Nonempty := by
  apply Finset.card_pos.mp
  rw [residualOverlapCode, Finset.card_map]
  exact Finset.card_pos.mpr (residualOverlapCell_nonempty F x)

theorem residualOverlapCode_card_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (residualOverlapCode F noSunflower x).card < k := by
  rw [residualOverlapCode, Finset.card_map]
  exact residualOverlapCell_card_lt F noSunflower x

/-- All overlap codes actually occupied by private blocker coordinates. -/
noncomputable def occupiedResidualOverlapCodes
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Finset (Finset (Fin k)) :=
  (MinimalBlocker.minimalBlocker F).attach.image
    (residualOverlapCode F noSunflower)

/-- The second Venn layer has at most the full `2^k` overlap alphabet. -/
theorem occupiedResidualOverlapCodes_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    (occupiedResidualOverlapCodes F noSunflower).card ≤ 2 ^ k := by
  classical
  have codes_subset : occupiedResidualOverlapCodes F noSunflower ⊆
      (Finset.univ : Finset (Fin k)).powerset := by
    intro code code_mem
    exact Finset.mem_powerset.mpr (Finset.subset_univ code)
  calc
    (occupiedResidualOverlapCodes F noSunflower).card ≤
        ((Finset.univ : Finset (Fin k)).powerset).card :=
      Finset.card_le_card codes_subset
    _ = 2 ^ k := by simp

/-- The disjoint union of the second-level matching petals. -/
noncomputable def residualSupport
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) : Finset alpha :=
  (residualMatching F).matching.petals.biUnion id

/-- The part of a residual visible inside one selected matching petal. -/
noncomputable def residualPetalComponent
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    Finset alpha :=
  PrivateWitnessReduction.residual F x ∩ petal.val

/-- The part of a residual outside all selected matching petals. -/
noncomputable def residualOutside
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Finset alpha :=
  PrivateWitnessReduction.residual F x \ residualSupport F

/--
The complete component code over the second matching.  Every selected petal
is charged only for the component actually used, and the remaining content is
stored once in the outside part.
-/
@[ext]
structure ResidualComponentCode
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) where
  petalPart :
    {petal // petal ∈ (residualMatching F).matching.petals} -> Finset alpha
  outsidePart : Finset alpha

noncomputable def componentCodeOfEdge
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (edge : Finset alpha) : ResidualComponentCode F where
  petalPart := fun petal => edge ∩ petal.val
  outsidePart := edge \ residualSupport F

noncomputable def assembleComponentCode
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (code : ResidualComponentCode F) : Finset alpha :=
  (Finset.univ.biUnion code.petalPart) ∪ code.outsidePart

/-- The selected component union is exactly the part of an edge in matching support. -/
theorem componentUnion_eq_inter_support
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (edge : Finset alpha) :
    (Finset.univ.biUnion fun
      petal : {petal // petal ∈ (residualMatching F).matching.petals} =>
        edge ∩ petal.val) = edge ∩ residualSupport F := by
  classical
  ext y
  simp [residualSupport]

/-- Assembly reconstructs every edge exactly. -/
theorem assemble_componentCodeOfEdge
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (edge : Finset alpha) :
    assembleComponentCode F (componentCodeOfEdge F edge) = edge := by
  classical
  rw [assembleComponentCode, componentCodeOfEdge,
    componentUnion_eq_inter_support]
  ext y
  by_cases y_edge : y ∈ edge <;>
    by_cases y_support : y ∈ residualSupport F <;>
      simp [y_edge, y_support]

/-- The global component encoding is injective before any entropy estimate. -/
theorem componentCodeOfEdge_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    Function.Injective (componentCodeOfEdge F) := by
  intro left right sameCode
  calc
    left = assembleComponentCode F (componentCodeOfEdge F left) :=
      (assemble_componentCodeOfEdge F left).symm
    _ = assembleComponentCode F (componentCodeOfEdge F right) :=
      congrArg (assembleComponentCode F) sameCode
    _ = right := assemble_componentCodeOfEdge F right

/-- The rank charged by a component code. -/
noncomputable def ResidualComponentCode.rank
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    (code : ResidualComponentCode F) : Nat :=
  (Finset.univ.sum fun petal => (code.petalPart petal).card) +
    code.outsidePart.card

/-- Pairwise disjoint matching petals make the component rank sum exact. -/
theorem componentCodeOfEdge_rank
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (edge : Finset alpha) :
    (componentCodeOfEdge F edge).rank = edge.card := by
  classical
  have componentsDisjoint :
      ((Finset.univ : Finset
        {petal // petal ∈ (residualMatching F).matching.petals}) :
          Set {petal // petal ∈ (residualMatching F).matching.petals}).PairwiseDisjoint
        (fun petal => edge ∩ petal.val) := by
    intro left _ right _ distinct
    have petalsDisjoint : Disjoint left.val right.val := by
      simpa using
        (residualMatching F).matching.residuals_disjoint
          left.val right.val left.property right.property
          (fun same => distinct (Subtype.ext same))
    exact petalsDisjoint.mono Finset.inter_subset_right Finset.inter_subset_right
  rw [ResidualComponentCode.rank, componentCodeOfEdge,
    ← Finset.card_biUnion componentsDisjoint,
    componentUnion_eq_inter_support]
  exact Finset.card_inter_add_card_sdiff edge (residualSupport F)

/-- Private residual codes are globally injective up to the already bounded exact-residual fiber. -/
noncomputable def privateResidualComponentCode
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    ResidualComponentCode F :=
  componentCodeOfEdge F (PrivateWitnessReduction.residual F x)

theorem privateResidualComponentCode_rank
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (privateResidualComponentCode F x).rank = r + 1 := by
  rw [privateResidualComponentCode, componentCodeOfEdge_rank,
    PrivateWitnessReduction.residual_card F x]

/-- The finite language actually used inside one selected matching petal. -/
noncomputable def petalComponentFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    Finset (Finset alpha) :=
  (PrivateWitnessReduction.residualFamily F).edges.image
    (fun edge => edge ∩ petal.val)

/-- The finite language actually used outside the second matching support. -/
noncomputable def outsideComponentFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    Finset (Finset alpha) :=
  (PrivateWitnessReduction.residualFamily F).edges.image
    (fun edge => edge \ residualSupport F)

/-- The product of all actually occupied component languages. -/
abbrev ResidualComponentProduct
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :=
  ((petal : {edge // edge ∈ (residualMatching F).matching.petals}) ->
      {part // part ∈ petalComponentFamily F petal}) ×
    {outside // outside ∈ outsideComponentFamily F}

/-- The global finite product code for each distinct residual edge. -/
noncomputable def residualProductCode
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    {edge // edge ∈ (PrivateWitnessReduction.residualFamily F).edges} ->
      ResidualComponentProduct F :=
  fun edge =>
    (fun petal =>
      ⟨edge.val ∩ petal.val,
        Finset.mem_image.mpr ⟨edge.val, edge.property, rfl⟩⟩,
    ⟨edge.val \ residualSupport F,
      Finset.mem_image.mpr ⟨edge.val, edge.property, rfl⟩⟩)

/-- The entire residual family embeds into its actually occupied component product. -/
theorem residualProductCode_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    Function.Injective (residualProductCode F) := by
  intro left right sameProduct
  apply Subtype.ext
  apply componentCodeOfEdge_injective F
  apply ResidualComponentCode.ext
  · funext petal
    exact congrArg (fun code => ((code.1 petal).val : Finset alpha)) sameProduct
  · exact congrArg (fun code => ((code.2).val : Finset alpha)) sameProduct

/--
The exact global cardinal-product inequality.  No ambient matching-petal rank
is charged here: only component languages that are actually occupied occur.
-/
theorem residualFamily_card_le_componentProduct
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤
      (∏ petal : {edge // edge ∈ (residualMatching F).matching.petals},
        (petalComponentFamily F petal).card) *
      (outsideComponentFamily F).card := by
  classical
  have bound := Fintype.card_le_of_injective
    (residualProductCode F)
    (residualProductCode_injective F)
  simpa [ResidualComponentProduct] using bound

/-- The component combinations actually realized by residual edges. -/
noncomputable def occupiedResidualProducts
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    Finset (ResidualComponentProduct F) :=
  Finset.univ.image (residualProductCode F)

/-- Fullness means that all independently available component choices recombine. -/
def ComponentProductFull
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) : Prop :=
  occupiedResidualProducts F = Finset.univ

/-- A finite compatibility witness: an available component tuple that does not recombine. -/
structure MissingComponentCombination
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) where
  code : ResidualComponentProduct F
  notOccupied : code ∉ occupiedResidualProducts F

/-- A gate has one coordinate for every matching petal and one outside coordinate. -/
abbrev GateSlot
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :=
  Option {edge // edge ∈ (residualMatching F).matching.petals}

/-- The missing-combination witness has one slot per matching petal plus one outside slot. -/
noncomputable def componentSlotCount
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) : Nat :=
  (residualMatching F).matching.petals.card + 1

theorem gateSlot_card
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    Fintype.card (GateSlot F) = componentSlotCount F := by
  simp [GateSlot, componentSlotCount]

theorem componentSlotCount_le
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    componentSlotCount F ≤ k := by
  have matching_lt : (residualMatching F).matching.petals.card < k :=
    Concrete.finiteCoreLinkMatching_card_lt_of_noSunflower
      (PrivateWitnessReduction.residualFamily_noSunflower noSunflower)
      (residualMatching F).matching
  simp only [componentSlotCount]
  omega

theorem gateSlot_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Fintype.card (GateSlot F) ≤ k := by
  rw [gateSlot_card]
  exact componentSlotCount_le F noSunflower

/-- Read the component stored at one gate coordinate. -/
noncomputable def productComponentAt
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (code : ResidualComponentProduct F) : GateSlot F → Finset alpha
  | none => code.2.val
  | some petal => (code.1 petal).val

/-- A missing recombination is a finite same-domain compatibility gate. -/
def missingCombinationAttempt : CorpusMachinery.FixedBaseStrengtheningAttempt where
  locus := .auxiliaryData
  auxiliaryFactor := .gateEquivalent

theorem missingCombinationAttempt_disposition :
    CorpusMachinery.strengtheningDisposition missingCombinationAttempt =
      SameScopeFactorDisposition.gateEquivalent := by
  rfl

theorem missingCombinationAttempt_not_independent :
    Not (CorpusMachinery.strengtheningDisposition missingCombinationAttempt =
      SameScopeFactorDisposition.independentAuthorizer) :=
  CorpusMachinery.strengtheningDisposition_ne_independentAuthorizer _

theorem residualProductCode_mem_occupied
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    residualProductCode F edge ∈ occupiedResidualProducts F := by
  classical
  exact Finset.mem_image.mpr ⟨edge, Finset.mem_univ edge, rfl⟩

/-- A realized product code cannot equal a missing component combination. -/
theorem realizedCode_ne_missing
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    residualProductCode F edge ≠ missing.code := by
  intro sameCode
  apply missing.notOccupied
  rw [← sameCode]
  exact residualProductCode_mem_occupied F edge

/-- Every realized residual disagrees with a missing tuple at a named gate slot. -/
theorem realizedCode_has_gateDisagreement
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    ∃ slot : GateSlot F,
      productComponentAt F (residualProductCode F edge) slot ≠
        productComponentAt F missing.code slot := by
  by_contra noSlot
  push_neg at noSlot
  apply realizedCode_ne_missing F missing edge
  apply Prod.ext
  · funext petal
    apply Subtype.ext
    simpa [productComponentAt] using noSlot (some petal)
  · apply Subtype.ext
    simpa [productComponentAt] using noSlot none

/-- Choose one concrete coordinate witnessing the forbidden-tuple disagreement. -/
noncomputable def gateDisagreementSlot
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) : GateSlot F :=
  Classical.choose (realizedCode_has_gateDisagreement F missing edge)

theorem gateDisagreementSlot_spec
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    productComponentAt F (residualProductCode F edge)
        (gateDisagreementSlot F missing edge) ≠
      productComponentAt F missing.code
        (gateDisagreementSlot F missing edge) :=
  Classical.choose_spec (realizedCode_has_gateDisagreement F missing edge)

/-- The residuals assigned to one selected disagreement coordinate. -/
noncomputable def gateDisagreementFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F) :
    Finset {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges} :=
  Finset.univ.filter fun edge => gateDisagreementSlot F missing edge = slot

theorem mem_gateDisagreementFiber_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    edge ∈ gateDisagreementFiber F missing slot ↔
      gateDisagreementSlot F missing edge = slot := by
  simp [gateDisagreementFiber]

/--
An oversized non-full component relation has an oversized branch at one of its
boundedly many gate slots.  This is the finite pigeonhole part of gate coercivity.
-/
theorem exists_large_gateDisagreementFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r k t : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (oversized : k * t <
      (PrivateWitnessReduction.residualFamily F).edges.card) :
    ∃ slot : GateSlot F,
      t < (gateDisagreementFiber F missing slot).card := by
  classical
  have slotBound : Fintype.card (GateSlot F) ≤ k :=
    gateSlot_card_le F noSunflower
  have product_lt : Fintype.card (GateSlot F) * t <
      Fintype.card {edge // edge ∈
        (PrivateWitnessReduction.residualFamily F).edges} := by
    rw [Fintype.card_coe]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right t slotBound) oversized
  rcases Fintype.exists_lt_card_fiber_of_mul_lt_card
      (gateDisagreementSlot F missing) product_lt with ⟨slot, large⟩
  refine ⟨slot, ?_⟩
  simpa [gateDisagreementFiber] using large

/-- The component image is either a full tensor product or has an explicit missing tuple. -/
theorem componentProductFull_or_missing
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    ComponentProductFull F ∨ Nonempty (MissingComponentCombination F) := by
  classical
  by_cases full : ComponentProductFull F
  · exact Or.inl full
  · apply Or.inr
    have notEqual : occupiedResidualProducts F ≠
        (Finset.univ : Finset (ResidualComponentProduct F)) := full
    have strict : occupiedResidualProducts F ⊂
        (Finset.univ : Finset (ResidualComponentProduct F)) :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ _, notEqual⟩
    rcases (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).mp strict with
      ⟨code, _, code_not_occupied⟩
    exact ⟨⟨code, code_not_occupied⟩⟩

theorem residualProductCode_surjective_of_full
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F) :
    Function.Surjective (residualProductCode F) := by
  classical
  intro code
  have code_mem : code ∈ occupiedResidualProducts F := by
    rw [full]
    exact Finset.mem_univ code
  rcases Finset.mem_image.mp code_mem with ⟨edge, _, sameCode⟩
  exact ⟨edge, sameCode⟩

/-- In the full branch the residual family has exactly the tensor-product cardinality. -/
theorem residualFamily_card_eq_componentProduct_of_full
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F) :
    (PrivateWitnessReduction.residualFamily F).edges.card =
      (∏ petal : {edge // edge ∈ (residualMatching F).matching.petals},
        (petalComponentFamily F petal).card) *
      (outsideComponentFamily F).card := by
  classical
  let equivalence :
      {edge // edge ∈ (PrivateWitnessReduction.residualFamily F).edges} ≃
        ResidualComponentProduct F :=
    Equiv.ofBijective (residualProductCode F)
      ⟨residualProductCode_injective F,
        residualProductCode_surjective_of_full F full⟩
  have sameCard := Fintype.card_congr equivalence
  simpa [ResidualComponentProduct] using sameCard

/-- Forget component-family membership while retaining the complete product tuple. -/
noncomputable def componentCodeOfProduct
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F) : ResidualComponentCode F where
  petalPart := fun petal => (product.1 petal).val
  outsidePart := product.2.val

theorem componentCodeOfProduct_residualProductCode
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    componentCodeOfProduct F (residualProductCode F edge) =
      componentCodeOfEdge F edge.val := by
  rfl

theorem petalComponent_subset_petal
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (part : {part // part ∈ petalComponentFamily F petal}) :
    part.val ⊆ petal.val := by
  rcases Finset.mem_image.mp part.property with ⟨edge, _, samePart⟩
  rw [← samePart]
  exact Finset.inter_subset_right

theorem outsideComponent_disjoint_support
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (outside : {outside // outside ∈ outsideComponentFamily F}) :
    Disjoint outside.val (residualSupport F) := by
  rcases Finset.mem_image.mp outside.property with ⟨edge, _, sameOutside⟩
  rw [← sameOutside]
  exact Finset.sdiff_disjoint

theorem componentCodeOfProduct_rank_eq_assembled_card
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F) :
    (componentCodeOfProduct F product).rank =
      (assembleComponentCode F (componentCodeOfProduct F product)).card := by
  classical
  have componentsDisjoint :
      ((Finset.univ : Finset
        {petal // petal ∈ (residualMatching F).matching.petals}) :
          Set {petal // petal ∈ (residualMatching F).matching.petals}).PairwiseDisjoint
        (fun petal => (product.1 petal).val) := by
    intro left _ right _ distinct
    have petalsDisjoint : Disjoint left.val right.val := by
      simpa using
        (residualMatching F).matching.residuals_disjoint
          left.val right.val left.property right.property
          (fun same => distinct (Subtype.ext same))
    exact petalsDisjoint.mono
      (petalComponent_subset_petal F left (product.1 left))
      (petalComponent_subset_petal F right (product.1 right))
  have componentUnion_subset_support :
      (Finset.univ.biUnion fun petal => (product.1 petal).val) ⊆
        residualSupport F := by
    apply Finset.biUnion_subset.mpr
    intro petal _ y y_part
    exact Finset.mem_biUnion.mpr
      ⟨petal.val, petal.property,
        petalComponent_subset_petal F petal (product.1 petal) y_part⟩
  have unionDisjointOutside :
      Disjoint (Finset.univ.biUnion fun petal => (product.1 petal).val)
        product.2.val :=
    (outsideComponent_disjoint_support F product.2).symm.mono_left
      componentUnion_subset_support
  rw [ResidualComponentCode.rank, componentCodeOfProduct,
    assembleComponentCode, Finset.card_union_of_disjoint unionDisjointOutside,
    Finset.card_biUnion componentsDisjoint]

/-- In the full branch every available tuple assembles to an actual residual edge. -/
theorem assembledProduct_mem_residualFamily_of_full
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F) :
    assembleComponentCode F (componentCodeOfProduct F product) ∈
      (PrivateWitnessReduction.residualFamily F).edges := by
  rcases residualProductCode_surjective_of_full F full product with
    ⟨edge, sameProduct⟩
  have sameComponentCode := congrArg (componentCodeOfProduct F) sameProduct
  rw [componentCodeOfProduct_residualProductCode] at sameComponentCode
  rw [← sameComponentCode, assemble_componentCodeOfEdge]
  exact edge.property

/-- Full tensor recombination preserves the residual rank for every tuple. -/
theorem componentProduct_rank_eq_of_full
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F) :
    (componentCodeOfProduct F product).rank = r + 1 := by
  rw [componentCodeOfProduct_rank_eq_assembled_card]
  exact (PrivateWitnessReduction.residualFamily F).uniform
    (assembleComponentCode F (componentCodeOfProduct F product))
    (assembledProduct_mem_residualFamily_of_full F full product)

theorem petalComponentFamily_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (familyNonempty :
      (PrivateWitnessReduction.residualFamily F).edges.Nonempty)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    (petalComponentFamily F petal).Nonempty := by
  rcases familyNonempty with ⟨edge, edge_mem⟩
  exact ⟨edge ∩ petal.val,
    Finset.mem_image.mpr ⟨edge, edge_mem, rfl⟩⟩

theorem outsideComponentFamily_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (familyNonempty :
      (PrivateWitnessReduction.residualFamily F).edges.Nonempty) :
    (outsideComponentFamily F).Nonempty := by
  rcases familyNonempty with ⟨edge, edge_mem⟩
  exact ⟨edge \ residualSupport F,
    Finset.mem_image.mpr ⟨edge, edge_mem, rfl⟩⟩

/-- In a full tensor product, every available component in one petal has the same rank. -/
theorem petalComponentFamily_uniform_of_full
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (familyNonempty :
      (PrivateWitnessReduction.residualFamily F).edges.Nonempty)
    (full : ComponentProductFull F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (left right : Finset alpha)
    (left_mem : left ∈ petalComponentFamily F petal)
    (right_mem : right ∈ petalComponentFamily F petal) :
    left.card = right.card := by
  classical
  rcases familyNonempty with ⟨baseEdge, baseEdge_mem⟩
  let base : ResidualComponentProduct F :=
    residualProductCode F ⟨baseEdge, baseEdge_mem⟩
  let leftPart : {part // part ∈ petalComponentFamily F petal} :=
    ⟨left, left_mem⟩
  let rightPart : {part // part ∈ petalComponentFamily F petal} :=
    ⟨right, right_mem⟩
  let leftProduct : ResidualComponentProduct F :=
    (Function.update base.1 petal leftPart, base.2)
  let rightProduct : ResidualComponentProduct F :=
    (Function.update base.1 petal rightPart, base.2)
  have sameTotal :
      (componentCodeOfProduct F leftProduct).rank =
        (componentCodeOfProduct F rightProduct).rank :=
    (componentProduct_rank_eq_of_full F full leftProduct).trans
      (componentProduct_rank_eq_of_full F full rightProduct).symm
  have samePetalSums :
      (∑ slot : {edge // edge ∈ (residualMatching F).matching.petals},
        ((Function.update base.1 petal leftPart slot).val).card) =
      (∑ slot : {edge // edge ∈ (residualMatching F).matching.petals},
        ((Function.update base.1 petal rightPart slot).val).card) := by
    simpa [leftProduct, rightProduct, componentCodeOfProduct,
      ResidualComponentCode.rank] using sameTotal
  let unchanged : Nat :=
    ∑ slot ∈ (Finset.univ.erase petal), (base.1 slot).val.card
  have leftSum :
      (∑ slot : {edge // edge ∈ (residualMatching F).matching.petals},
        ((Function.update base.1 petal leftPart slot).val).card) =
        left.card + unchanged := by
    calc
      _ = ((Function.update base.1 petal leftPart petal).val).card +
          ∑ slot ∈ (Finset.univ.erase petal),
            ((Function.update base.1 petal leftPart slot).val).card :=
        (Finset.add_sum_erase Finset.univ
          (fun slot => ((Function.update base.1 petal leftPart slot).val).card)
          (Finset.mem_univ petal)).symm
      _ = left.card + unchanged := by
        apply congrArg₂ (· + ·)
        · simp [leftPart]
        · apply Finset.sum_congr rfl
          intro slot slot_mem
          have slot_ne : slot ≠ petal := Finset.ne_of_mem_erase slot_mem
          simp [Function.update, slot_ne]
  have rightSum :
      (∑ slot : {edge // edge ∈ (residualMatching F).matching.petals},
        ((Function.update base.1 petal rightPart slot).val).card) =
        right.card + unchanged := by
    calc
      _ = ((Function.update base.1 petal rightPart petal).val).card +
          ∑ slot ∈ (Finset.univ.erase petal),
            ((Function.update base.1 petal rightPart slot).val).card :=
        (Finset.add_sum_erase Finset.univ
          (fun slot => ((Function.update base.1 petal rightPart slot).val).card)
          (Finset.mem_univ petal)).symm
      _ = right.card + unchanged := by
        apply congrArg₂ (· + ·)
        · simp [rightPart]
        · apply Finset.sum_congr rfl
          intro slot slot_mem
          have slot_ne : slot ≠ petal := Finset.ne_of_mem_erase slot_mem
          simp [Function.update, slot_ne]
  omega

/-- In a full tensor product, every available outside component has the same rank. -/
theorem outsideComponentFamily_uniform_of_full
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (familyNonempty :
      (PrivateWitnessReduction.residualFamily F).edges.Nonempty)
    (full : ComponentProductFull F)
    (left right : Finset alpha)
    (left_mem : left ∈ outsideComponentFamily F)
    (right_mem : right ∈ outsideComponentFamily F) :
    left.card = right.card := by
  classical
  rcases familyNonempty with ⟨baseEdge, baseEdge_mem⟩
  let base : ResidualComponentProduct F :=
    residualProductCode F ⟨baseEdge, baseEdge_mem⟩
  let leftPart : {part // part ∈ outsideComponentFamily F} :=
    ⟨left, left_mem⟩
  let rightPart : {part // part ∈ outsideComponentFamily F} :=
    ⟨right, right_mem⟩
  let leftProduct : ResidualComponentProduct F := (base.1, leftPart)
  let rightProduct : ResidualComponentProduct F := (base.1, rightPart)
  have sameTotal :
      (componentCodeOfProduct F leftProduct).rank =
        (componentCodeOfProduct F rightProduct).rank :=
    (componentProduct_rank_eq_of_full F full leftProduct).trans
      (componentProduct_rank_eq_of_full F full rightProduct).symm
  simpa [leftProduct, rightProduct, leftPart, rightPart,
    componentCodeOfProduct, ResidualComponentCode.rank] using sameTotal

/-- One honest uniform factor carried by a selected matching petal. -/
noncomputable def petalUniformFactor
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    Concrete.UniformSetFamily alpha ((product.1 petal).val.card) where
  edges := petalComponentFamily F petal
  uniform := by
    intro part part_mem
    have familyNonempty :
        (PrivateWitnessReduction.residualFamily F).edges.Nonempty :=
      ⟨assembleComponentCode F (componentCodeOfProduct F product),
        assembledProduct_mem_residualFamily_of_full F full product⟩
    exact petalComponentFamily_uniform_of_full
      F familyNonempty full petal part (product.1 petal).val
      part_mem (product.1 petal).property

/-- The honest uniform factor carried outside the matching support. -/
noncomputable def outsideUniformFactor
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F) :
    Concrete.UniformSetFamily alpha product.2.val.card where
  edges := outsideComponentFamily F
  uniform := by
    intro part part_mem
    have familyNonempty :
        (PrivateWitnessReduction.residualFamily F).edges.Nonempty :=
      ⟨assembleComponentCode F (componentCodeOfProduct F product),
        assembledProduct_mem_residualFamily_of_full F full product⟩
    exact outsideComponentFamily_uniform_of_full
      F familyNonempty full part product.2.val
      part_mem product.2.property

/-- The ranks of all full-product factors add to the residual rank exactly once. -/
theorem uniformFactor_rank_sum
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F) :
    (∑ petal : {edge // edge ∈ (residualMatching F).matching.petals},
      (product.1 petal).val.card) + product.2.val.card = r + 1 := by
  simpa [componentCodeOfProduct, ResidualComponentCode.rank] using
    componentProduct_rank_eq_of_full F full product

noncomputable def replacePetalProduct
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (part : {part // part ∈ petalComponentFamily F petal}) :
    ResidualComponentProduct F :=
  (Function.update product.1 petal part, product.2)

/-- All fixed sibling content when one petal component is varied. -/
noncomputable def fixedPetalContext
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    Finset alpha :=
  ((Finset.univ.erase petal).biUnion fun slot => (product.1 slot).val) ∪
    product.2.val

theorem assemble_replacePetalProduct
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (part : {part // part ∈ petalComponentFamily F petal}) :
    assembleComponentCode F
        (componentCodeOfProduct F (replacePetalProduct F product petal part)) =
      part.val ∪ fixedPetalContext F product petal := by
  classical
  rw [assembleComponentCode, componentCodeOfProduct, replacePetalProduct,
    fixedPetalContext]
  rw [show (Finset.univ : Finset
      {edge // edge ∈ (residualMatching F).matching.petals}) =
        insert petal (Finset.univ.erase petal) by
      exact (Finset.insert_erase (Finset.mem_univ petal)).symm]
  rw [Finset.biUnion_insert]
  simp only [Function.update_self]
  have unchanged :
      (Finset.univ.erase petal).biUnion
          (fun slot => (Function.update product.1 petal part slot).val) =
        (Finset.univ.erase petal).biUnion
          (fun slot => (product.1 slot).val) := by
    apply Finset.biUnion_congr rfl
    intro slot slot_mem
    have slot_ne : slot ≠ petal := Finset.ne_of_mem_erase slot_mem
    simp [Function.update, slot_ne]
  rw [unchanged]
  simp [Finset.union_assoc]

theorem fixedPetalContext_disjoint
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    Disjoint petal.val (fixedPetalContext F product petal) := by
  classical
  apply Finset.disjoint_left.mpr
  intro y y_petal y_context
  rcases Finset.mem_union.mp y_context with y_sibling | y_outside
  · rcases Finset.mem_biUnion.mp y_sibling with
      ⟨sibling, sibling_mem, y_component⟩
    have sibling_ne : sibling ≠ petal := Finset.ne_of_mem_erase sibling_mem
    have y_sibling_petal : y ∈ sibling.val :=
      petalComponent_subset_petal F sibling (product.1 sibling) y_component
    have petalsDisjoint : Disjoint sibling.val petal.val := by
      simpa using
        (residualMatching F).matching.residuals_disjoint
          sibling.val petal.val sibling.property petal.property
          (fun same => sibling_ne (Subtype.ext same))
    exact Finset.disjoint_left.mp petalsDisjoint y_sibling_petal y_petal
  · have y_support : y ∈ residualSupport F :=
      Finset.mem_biUnion.mpr ⟨petal.val, petal.property, y_petal⟩
    exact Finset.disjoint_left.mp
      (outsideComponent_disjoint_support F product.2)
      y_outside y_support

theorem assemble_replacePetalProduct_inter_petal
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (part : {part // part ∈ petalComponentFamily F petal}) :
    assembleComponentCode F
        (componentCodeOfProduct F (replacePetalProduct F product petal part)) ∩
      petal.val = part.val := by
  rw [assemble_replacePetalProduct]
  apply Finset.ext
  intro y
  have part_subset := petalComponent_subset_petal F petal part
  have context_disjoint := fixedPetalContext_disjoint F product petal
  constructor
  · intro y_mem
    rcases Finset.mem_inter.mp y_mem with ⟨y_union, y_petal⟩
    rcases Finset.mem_union.mp y_union with y_part | y_context
    · exact y_part
    · exact False.elim <|
        Finset.disjoint_left.mp context_disjoint y_petal y_context
  · intro y_part
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_union.mpr (Or.inl y_part), part_subset y_part⟩

theorem union_fixed_inter_union_fixed
    {alpha : Type}
    [DecidableEq alpha]
    (left right fixed : Finset alpha)
    (leftDisjoint : Disjoint left fixed)
    (_rightDisjoint : Disjoint right fixed) :
    (left ∪ fixed) ∩ (right ∪ fixed) = (left ∩ right) ∪ fixed := by
  apply Finset.ext
  intro y
  constructor
  · intro y_mem
    rcases Finset.mem_inter.mp y_mem with ⟨y_left, y_right⟩
    rcases Finset.mem_union.mp y_left with y_left | y_fixed
    · rcases Finset.mem_union.mp y_right with y_right | y_fixed
      · exact Finset.mem_union.mpr <|
          Or.inl (Finset.mem_inter.mpr ⟨y_left, y_right⟩)
      · exact False.elim <|
          Finset.disjoint_left.mp leftDisjoint y_left y_fixed
    · exact Finset.mem_union.mpr (Or.inr y_fixed)
  · intro y_mem
    rcases Finset.mem_union.mp y_mem with y_both | y_fixed
    · rcases Finset.mem_inter.mp y_both with ⟨y_left, y_right⟩
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union.mpr (Or.inl y_left),
          Finset.mem_union.mpr (Or.inl y_right)⟩
    · exact Finset.mem_inter.mpr
        ⟨Finset.mem_union.mpr (Or.inr y_fixed),
          Finset.mem_union.mpr (Or.inr y_fixed)⟩

/-- A sunflower in one full-product petal factor lifts to the residual family. -/
theorem hasResidualSunflower_of_petalFactor
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (factorSunflower :
      Concrete.HasSunflower k (petalUniformFactor F full product petal)) :
    Concrete.HasSunflower k (PrivateWitnessReduction.residualFamily F) := by
  classical
  rcases factorSunflower with ⟨core, ⟨W⟩⟩
  let part : Fin k -> {part // part ∈ petalComponentFamily F petal} :=
    fun i => ⟨W.petals i, W.petals_mem i⟩
  let productAt : Fin k -> ResidualComponentProduct F :=
    fun i => replacePetalProduct F product petal (part i)
  let liftedEdge : Fin k -> Finset alpha :=
    fun i => assembleComponentCode F (componentCodeOfProduct F (productAt i))
  let fixed := fixedPetalContext F product petal
  refine ⟨core ∪ fixed, ⟨{
    petals := liftedEdge
    petals_mem := ?_
    petals_injective := ?_
    pairwise_intersection := ?_ }⟩⟩
  · intro i
    exact assembledProduct_mem_residualFamily_of_full F full (productAt i)
  · intro i j sameEdge
    apply W.petals_injective
    have sameIntersection := congrArg (fun edge : Finset alpha => edge ∩ petal.val) sameEdge
    simp only [liftedEdge, productAt] at sameIntersection
    rw [assemble_replacePetalProduct_inter_petal F product petal (part i),
      assemble_replacePetalProduct_inter_petal F product petal (part j)] at sameIntersection
    exact sameIntersection
  · intro i j distinct
    have leftSubset : W.petals i ⊆ petal.val :=
      petalComponent_subset_petal F petal (part i)
    have rightSubset : W.petals j ⊆ petal.val :=
      petalComponent_subset_petal F petal (part j)
    have contextDisjoint := fixedPetalContext_disjoint F product petal
    have leftDisjoint : Disjoint (W.petals i) fixed :=
      contextDisjoint.mono_left leftSubset
    have rightDisjoint : Disjoint (W.petals j) fixed :=
      contextDisjoint.mono_left rightSubset
    rw [show liftedEdge i = W.petals i ∪ fixed by
          exact assemble_replacePetalProduct F product petal (part i),
      show liftedEdge j = W.petals j ∪ fixed by
          exact assemble_replacePetalProduct F product petal (part j),
      union_fixed_inter_union_fixed
        (W.petals i) (W.petals j) fixed leftDisjoint rightDisjoint,
      W.pairwise_intersection i j distinct]

theorem petalUniformFactor_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    Not (Concrete.HasSunflower k (petalUniformFactor F full product petal)) :=
  fun factorSunflower =>
    PrivateWitnessReduction.residualFamily_noSunflower noSunflower <|
      hasResidualSunflower_of_petalFactor
        F full product petal factorSunflower

noncomputable def replaceOutsideProduct
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (outside : {outside // outside ∈ outsideComponentFamily F}) :
    ResidualComponentProduct F :=
  (product.1, outside)

noncomputable def fixedOutsideContext
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F) : Finset alpha :=
  Finset.univ.biUnion fun petal => (product.1 petal).val

theorem fixedOutsideContext_subset_support
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F) :
    fixedOutsideContext F product ⊆ residualSupport F := by
  intro y y_mem
  rcases Finset.mem_biUnion.mp y_mem with ⟨petal, _, y_part⟩
  exact Finset.mem_biUnion.mpr
    ⟨petal.val, petal.property,
      petalComponent_subset_petal F petal (product.1 petal) y_part⟩

theorem assemble_replaceOutsideProduct
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (outside : {outside // outside ∈ outsideComponentFamily F}) :
    assembleComponentCode F
        (componentCodeOfProduct F (replaceOutsideProduct F product outside)) =
      outside.val ∪ fixedOutsideContext F product := by
  simp [assembleComponentCode, componentCodeOfProduct,
    replaceOutsideProduct, fixedOutsideContext, Finset.union_comm]

theorem outside_disjoint_fixedOutsideContext
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (outside : {outside // outside ∈ outsideComponentFamily F}) :
    Disjoint outside.val (fixedOutsideContext F product) :=
  (outsideComponent_disjoint_support F outside).mono_right
    (fixedOutsideContext_subset_support F product)

theorem assemble_replaceOutsideProduct_sdiff_support
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (outside : {outside // outside ∈ outsideComponentFamily F}) :
    assembleComponentCode F
        (componentCodeOfProduct F (replaceOutsideProduct F product outside)) \
      residualSupport F = outside.val := by
  rw [assemble_replaceOutsideProduct]
  apply Finset.ext
  intro y
  have outside_disjoint := outsideComponent_disjoint_support F outside
  have fixed_subset := fixedOutsideContext_subset_support F product
  constructor
  · intro y_mem
    rcases Finset.mem_sdiff.mp y_mem with ⟨y_union, y_not_support⟩
    rcases Finset.mem_union.mp y_union with y_outside | y_fixed
    · exact y_outside
    · exact False.elim (y_not_support (fixed_subset y_fixed))
  · intro y_outside
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_union.mpr (Or.inl y_outside),
        fun y_support =>
          Finset.disjoint_left.mp outside_disjoint y_outside y_support⟩

/-- A sunflower in the full-product outside factor lifts to the residual family. -/
theorem hasResidualSunflower_of_outsideFactor
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F)
    (factorSunflower :
      Concrete.HasSunflower k (outsideUniformFactor F full product)) :
    Concrete.HasSunflower k (PrivateWitnessReduction.residualFamily F) := by
  classical
  rcases factorSunflower with ⟨core, ⟨W⟩⟩
  let outside : Fin k -> {outside // outside ∈ outsideComponentFamily F} :=
    fun i => ⟨W.petals i, W.petals_mem i⟩
  let productAt : Fin k -> ResidualComponentProduct F :=
    fun i => replaceOutsideProduct F product (outside i)
  let liftedEdge : Fin k -> Finset alpha :=
    fun i => assembleComponentCode F (componentCodeOfProduct F (productAt i))
  let fixed := fixedOutsideContext F product
  refine ⟨core ∪ fixed, ⟨{
    petals := liftedEdge
    petals_mem := ?_
    petals_injective := ?_
    pairwise_intersection := ?_ }⟩⟩
  · intro i
    exact assembledProduct_mem_residualFamily_of_full F full (productAt i)
  · intro i j sameEdge
    apply W.petals_injective
    have sameOutside := congrArg
      (fun edge : Finset alpha => edge \ residualSupport F) sameEdge
    simp only [liftedEdge, productAt] at sameOutside
    rw [assemble_replaceOutsideProduct_sdiff_support F product (outside i),
      assemble_replaceOutsideProduct_sdiff_support F product (outside j)] at sameOutside
    exact sameOutside
  · intro i j distinct
    have leftDisjoint : Disjoint (W.petals i) fixed :=
      outside_disjoint_fixedOutsideContext F product (outside i)
    have rightDisjoint : Disjoint (W.petals j) fixed :=
      outside_disjoint_fixedOutsideContext F product (outside j)
    rw [show liftedEdge i = W.petals i ∪ fixed by
          exact assemble_replaceOutsideProduct F product (outside i),
      show liftedEdge j = W.petals j ∪ fixed by
          exact assemble_replaceOutsideProduct F product (outside j),
      union_fixed_inter_union_fixed
        (W.petals i) (W.petals j) fixed leftDisjoint rightDisjoint,
      W.pairwise_intersection i j distinct]

theorem outsideUniformFactor_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F) :
    Not (Concrete.HasSunflower k (outsideUniformFactor F full product)) :=
  fun factorSunflower =>
    PrivateWitnessReduction.residualFamily_noSunflower noSunflower <|
      hasResidualSunflower_of_outsideFactor
        F full product factorSunflower

/-- A petal factor using the entire parent rank is a singleton language. -/
theorem petalUniformFactor_card_le_one_of_full_rank
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (fullRank : (product.1 petal).val.card = r + 1) :
    (petalUniformFactor F full product petal).edges.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro left left_mem right right_mem
  have petal_mem_residual : petal.val ∈
      (PrivateWitnessReduction.residualFamily F).edges :=
    (residualMatching F).matching.petals_subset petal.property
  have petal_card : petal.val.card = r + 1 :=
    (PrivateWitnessReduction.residualFamily F).uniform
      petal.val petal_mem_residual
  have left_card : left.card = r + 1 := by
    rw [(petalUniformFactor F full product petal).uniform left left_mem,
      fullRank]
  have right_card : right.card = r + 1 := by
    rw [(petalUniformFactor F full product petal).uniform right right_mem,
      fullRank]
  have left_eq_petal : left = petal.val := by
    apply Finset.eq_of_subset_of_card_le
      (petalComponent_subset_petal F petal ⟨left, left_mem⟩)
    rw [petal_card, left_card]
  have right_eq_petal : right = petal.val := by
    apply Finset.eq_of_subset_of_card_le
      (petalComponent_subset_petal F petal ⟨right, right_mem⟩)
    rw [petal_card, right_card]
  exact left_eq_petal.trans right_eq_petal.symm

/-- Every petal factor with genuine multiplicity has strictly lower rank. -/
theorem petalUniformFactor_rank_lt_of_one_lt_card
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (branches : 1 < (petalUniformFactor F full product petal).edges.card) :
    (product.1 petal).val.card < r + 1 := by
  have component_le_sum : (product.1 petal).val.card ≤
      ∑ slot : {edge // edge ∈ (residualMatching F).matching.petals},
        (product.1 slot).val.card :=
    Finset.single_le_sum
      (f := fun slot => (product.1 slot).val.card)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ petal)
  have rankSum := uniformFactor_rank_sum F full product
  have component_le : (product.1 petal).val.card ≤ r + 1 := by omega
  exact Nat.lt_of_le_of_ne component_le fun sameRank =>
    Nat.not_lt_of_ge
      (petalUniformFactor_card_le_one_of_full_rank
        F full product petal sameRank)
      branches

theorem assembledProduct_hits_support_of_full
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F) :
    Not (Disjoint
      (assembleComponentCode F (componentCodeOfProduct F product))
      (residualSupport F)) := by
  let edge := assembleComponentCode F (componentCodeOfProduct F product)
  have edge_mem : edge ∈ (PrivateWitnessReduction.residualFamily F).edges :=
    assembledProduct_mem_residualFamily_of_full F full product
  have edge_live : (edge \ (∅ : Finset alpha)).Nonempty := by
    simp only [Finset.sdiff_empty]
    apply Finset.card_pos.mp
    rw [(PrivateWitnessReduction.residualFamily F).uniform edge edge_mem]
    exact Nat.zero_lt_succ r
  simpa [edge, residualSupport, Concrete.FiniteCoreLinkMatching.rawBlocker] using
    (residualMatching F).hits_link_petals
      edge_mem (Finset.empty_subset edge) edge_live

/-- The outside factor always has strictly lower rank. -/
theorem outsideUniformFactor_rank_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F) :
    product.2.val.card < r + 1 := by
  classical
  have rankSum := uniformFactor_rank_sum F full product
  have outside_le : product.2.val.card ≤ r + 1 := by omega
  apply Nat.lt_of_le_of_ne outside_le
  intro outside_full_rank
  have petalSumZero :
      (∑ petal : {edge // edge ∈ (residualMatching F).matching.petals},
        (product.1 petal).val.card) = 0 := by
    omega
  rcases Finset.not_disjoint_iff.mp
      (assembledProduct_hits_support_of_full F full product) with
    ⟨y, y_edge, y_support⟩
  rw [assembleComponentCode, componentCodeOfProduct] at y_edge
  rcases Finset.mem_union.mp y_edge with y_component | y_outside
  · rcases Finset.mem_biUnion.mp y_component with
      ⟨petal, _, y_part⟩
    have part_positive : 0 < (product.1 petal).val.card :=
      Finset.card_pos.mpr ⟨y, y_part⟩
    have part_le_sum : (product.1 petal).val.card ≤
        ∑ slot : {edge // edge ∈ (residualMatching F).matching.petals},
          (product.1 slot).val.card :=
      Finset.single_le_sum
        (f := fun slot => (product.1 slot).val.card)
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ petal)
    omega
  · exact Finset.disjoint_left.mp
      (outsideComponent_disjoint_support F product.2)
      y_outside y_support

/-- Every petal factor rank is bounded by the full residual rank. -/
theorem petalUniformFactor_rank_le
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    (product.1 petal).val.card ≤ r + 1 := by
  have component_le_sum : (product.1 petal).val.card ≤
      ∑ slot : {edge // edge ∈ (residualMatching F).matching.petals},
        (product.1 slot).val.card :=
    Finset.single_le_sum
      (f := fun slot => (product.1 slot).val.card)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ petal)
  have rankSum := uniformFactor_rank_sum F full product
  omega

/--
Rank-weighted tensor assembly: power bounds for all occupied factors multiply
to the same power at the exact sum of their ranks.
-/
theorem residualFamily_card_le_pow_of_full_factorBounds
    {alpha : Type}
    [DecidableEq alpha]
    {r base : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F)
    (petalBound :
      ∀ petal : {edge // edge ∈ (residualMatching F).matching.petals},
        (petalUniformFactor F full product petal).edges.card ≤
          base ^ (product.1 petal).val.card)
    (outsideBound :
      (outsideUniformFactor F full product).edges.card ≤
        base ^ product.2.val.card) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤
      base ^ (r + 1) := by
  classical
  rw [residualFamily_card_eq_componentProduct_of_full F full]
  have petalProductBound :
      (∏ petal : {edge // edge ∈ (residualMatching F).matching.petals},
        (petalComponentFamily F petal).card) ≤
      ∏ petal : {edge // edge ∈ (residualMatching F).matching.petals},
        base ^ (product.1 petal).val.card := by
    apply Finset.prod_le_prod
    · intro petal _
      exact Nat.zero_le _
    · intro petal _
      simpa [petalUniformFactor] using petalBound petal
  calc
    (∏ petal : {edge // edge ∈ (residualMatching F).matching.petals},
        (petalComponentFamily F petal).card) *
          (outsideComponentFamily F).card ≤
        (∏ petal : {edge // edge ∈ (residualMatching F).matching.petals},
          base ^ (product.1 petal).val.card) *
            base ^ product.2.val.card := by
      exact Nat.mul_le_mul petalProductBound <|
        by simpa [outsideUniformFactor] using outsideBound
    _ = base ^
          (∑ petal : {edge // edge ∈
            (residualMatching F).matching.petals},
              (product.1 petal).val.card) *
            base ^ product.2.val.card := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = base ^
          ((∑ petal : {edge // edge ∈
            (residualMatching F).matching.petals},
              (product.1 petal).val.card) + product.2.val.card) := by
      rw [Nat.pow_add]
    _ = base ^ (r + 1) := by
      rw [uniformFactor_rank_sum F full product]

/--
The full-product branch is completely recursive: lower-rank sunflower-free
power bounds control every nontrivial factor, while a full-rank petal factor is
a singleton.
-/
theorem residualFamily_card_le_pow_of_full_lowerRankBounds
    {alpha : Type}
    [DecidableEq alpha]
    {r k base : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F)
    (base_positive : 0 < base)
    (lowerRankBound :
      ∀ s : Nat, s < r + 1 ->
        ∀ G : Concrete.UniformSetFamily alpha s,
          Not (Concrete.HasSunflower k G) ->
          G.edges.card ≤ base ^ s) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤
      base ^ (r + 1) := by
  apply residualFamily_card_le_pow_of_full_factorBounds
    F full product
  · intro petal
    by_cases lowerRank : (product.1 petal).val.card < r + 1
    · exact lowerRankBound (product.1 petal).val.card lowerRank
        (petalUniformFactor F full product petal)
        (petalUniformFactor_noSunflower F noSunflower full product petal)
    · have fullRank : (product.1 petal).val.card = r + 1 := by
        have rankAtMost := petalUniformFactor_rank_le F full product petal
        omega
      exact (petalUniformFactor_card_le_one_of_full_rank
        F full product petal fullRank).trans
          (Nat.one_le_pow (product.1 petal).val.card base base_positive)
  · exact lowerRankBound product.2.val.card
      (outsideUniformFactor_rank_lt F full product)
      (outsideUniformFactor F full product)
      (outsideUniformFactor_noSunflower F noSunflower full product)

/-- The honest uniform factor at one full-product gate coordinate. -/
noncomputable def fullComponentFactorAt
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F)
    (slot : GateSlot F) :
    Concrete.UniformSetFamily alpha
      (productComponentAt F product slot).card := by
  cases slot with
  | none => exact outsideUniformFactor F full product
  | some petal => exact petalUniformFactor F full product petal

@[simp] theorem fullComponentFactorAt_none
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F) :
    fullComponentFactorAt F full product none =
      outsideUniformFactor F full product := by
  rfl

@[simp] theorem fullComponentFactorAt_some
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    fullComponentFactorAt F full product (some petal) =
      petalUniformFactor F full product petal := by
  rfl

theorem fullComponentFactorAt_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F)
    (slot : GateSlot F) :
    Not (Concrete.HasSunflower k
      (fullComponentFactorAt F full product slot)) := by
  cases slot with
  | none =>
      exact outsideUniformFactor_noSunflower F noSunflower full product
  | some petal =>
      exact petalUniformFactor_noSunflower F noSunflower full product petal

theorem fullComponentFactorAt_rank_lt_of_one_lt_card
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F)
    (slot : GateSlot F)
    (branches : 1 < (fullComponentFactorAt F full product slot).edges.card) :
    (productComponentAt F product slot).card < r + 1 := by
  cases slot with
  | none =>
      exact outsideUniformFactor_rank_lt F full product
  | some petal =>
      exact petalUniformFactor_rank_lt_of_one_lt_card
        F full product petal branches

/--
A concrete full-product tensor split: fullness permits independent
recombination, and two different component coordinates both carry genuine
multiplicity.
-/
structure FullComponentTensorSplit
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F) where
  left : GateSlot F
  right : GateSlot F
  left_ne_right : left ≠ right
  leftBranches : 1 < (fullComponentFactorAt F full product left).edges.card
  rightBranches : 1 < (fullComponentFactorAt F full product right).edges.card

/-- Without a full tensor split, every factor other than one active factor is a singleton. -/
theorem fullComponentFactorAt_card_le_one_of_noTensorSplit
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {full : ComponentProductFull F}
    {product : ResidualComponentProduct F}
    (noSplit : Not (Nonempty (FullComponentTensorSplit F full product)))
    (active : GateSlot F)
    (activeBranches :
      1 < (fullComponentFactorAt F full product active).edges.card)
    (other : GateSlot F)
    (other_ne_active : other ≠ active) :
    (fullComponentFactorAt F full product other).edges.card ≤ 1 := by
  apply Nat.le_of_not_gt
  intro otherBranches
  exact noSplit ⟨{
    left := other
    right := active
    left_ne_right := other_ne_active
    leftBranches := otherBranches
    rightBranches := activeBranches }⟩

/-- Full recombination identifies the residual cardinality with the product over all gate factors. -/
theorem residualFamily_card_eq_fullComponentFactors
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F) :
    (PrivateWitnessReduction.residualFamily F).edges.card =
      ∏ slot : GateSlot F,
        (fullComponentFactorAt F full product slot).edges.card := by
  rw [residualFamily_card_eq_componentProduct_of_full F full,
    Fintype.prod_option]
  simp [fullComponentFactorAt, outsideUniformFactor,
    petalUniformFactor, Nat.mul_comm]

/-- If no full tensor split survives, one active factor controls the whole product. -/
theorem residualFamily_card_le_activeFactor_of_noTensorSplit
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {full : ComponentProductFull F}
    {product : ResidualComponentProduct F}
    (noSplit : Not (Nonempty (FullComponentTensorSplit F full product)))
    (active : GateSlot F)
    (activeBranches :
      1 < (fullComponentFactorAt F full product active).edges.card) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤
      (fullComponentFactorAt F full product active).edges.card := by
  classical
  rw [residualFamily_card_eq_fullComponentFactors F full product]
  let factorCard : GateSlot F -> Nat := fun slot =>
    (fullComponentFactorAt F full product slot).edges.card
  change (Finset.univ.prod factorCard) ≤ factorCard active
  have otherProductBound :
      (Finset.univ.erase active).prod factorCard ≤ 1 := by
    calc
      (Finset.univ.erase active).prod factorCard ≤
          (Finset.univ.erase active).prod (fun _ => 1) := by
        apply Finset.prod_le_prod
        · intro slot _
          exact Nat.zero_le _
        · intro slot slot_mem
          exact fullComponentFactorAt_card_le_one_of_noTensorSplit
            noSplit active activeBranches slot
              (Finset.ne_of_mem_erase slot_mem)
      _ = 1 := by simp
  calc
    Finset.univ.prod factorCard =
        factorCard active * (Finset.univ.erase active).prod factorCard :=
      (Finset.mul_prod_erase Finset.univ factorCard
        (Finset.mem_univ active)).symm
    _ ≤ factorCard active * 1 :=
      Nat.mul_le_mul_left (factorCard active) otherProductBound
    _ = factorCard active := by simp

/-- If every full-product factor is a singleton, so is the residual relation. -/
theorem residualFamily_card_le_one_of_full_factorSingletons
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {full : ComponentProductFull F}
    {product : ResidualComponentProduct F}
    (factorSingleton : ∀ slot : GateSlot F,
      (fullComponentFactorAt F full product slot).edges.card ≤ 1) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤ 1 := by
  classical
  rw [residualFamily_card_eq_fullComponentFactors F full product]
  calc
    (∏ slot : GateSlot F,
        (fullComponentFactorAt F full product slot).edges.card) ≤
        ∏ _slot : GateSlot F, 1 := by
      apply Finset.prod_le_prod
      · intro slot _
        exact Nat.zero_le _
      · intro slot _
        exact factorSingleton slot
    _ = 1 := by simp

/--
Complete full-product exhaustion: either two independent factors give a tensor
split, the relation is a singleton, or one strictly lower-rank sunflower-free
factor carries every surviving branch.
-/
theorem fullComponentProduct_tensorSplit_or_singleton_or_lowerRankFactor
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F) :
    Nonempty (FullComponentTensorSplit F full product) ∨
      (PrivateWitnessReduction.residualFamily F).edges.card ≤ 1 ∨
      ∃ slot : GateSlot F,
        1 < (fullComponentFactorAt F full product slot).edges.card ∧
        (productComponentAt F product slot).card < r + 1 ∧
        Not (Concrete.HasSunflower k
          (fullComponentFactorAt F full product slot)) ∧
        (PrivateWitnessReduction.residualFamily F).edges.card ≤
          (fullComponentFactorAt F full product slot).edges.card := by
  by_cases split : Nonempty (FullComponentTensorSplit F full product)
  · exact Or.inl split
  · by_cases active : ∃ slot : GateSlot F,
        1 < (fullComponentFactorAt F full product slot).edges.card
    · rcases active with ⟨slot, branches⟩
      exact Or.inr <| Or.inr ⟨slot, branches,
        fullComponentFactorAt_rank_lt_of_one_lt_card
          F full product slot branches,
        fullComponentFactorAt_noSunflower
          F noSunflower full product slot,
        residualFamily_card_le_activeFactor_of_noTensorSplit
          split slot branches⟩
    · apply Or.inr
      apply Or.inl
      apply residualFamily_card_le_one_of_full_factorSingletons
      intro slot
      apply Nat.le_of_not_gt
      intro branches
      exact active ⟨slot, branches⟩

/-- Operational terminal primeness for genuine full-recombination tensor splits. -/
structure TerminalPrimeFullComponentTensorSplitExclusion
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) where
  excludes :
    ∀ (full : ComponentProductFull F)
      (product : ResidualComponentProduct F),
      FullComponentTensorSplit F full product -> False

/-- Terminal-prime impossibility removes the tensor branch from full-product exhaustion. -/
theorem fullComponentProduct_singleton_or_lowerRankFactor_of_terminalPrime
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (Prime : TerminalPrimeFullComponentTensorSplitExclusion F)
    (full : ComponentProductFull F)
    (product : ResidualComponentProduct F) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤ 1 ∨
      ∃ slot : GateSlot F,
        1 < (fullComponentFactorAt F full product slot).edges.card ∧
        (productComponentAt F product slot).card < r + 1 ∧
        Not (Concrete.HasSunflower k
          (fullComponentFactorAt F full product slot)) ∧
        (PrivateWitnessReduction.residualFamily F).edges.card ≤
          (fullComponentFactorAt F full product slot).edges.card := by
  rcases fullComponentProduct_tensorSplit_or_singleton_or_lowerRankFactor
      F noSunflower full product with split | singletonOrFactor
  · rcases split with ⟨split⟩
    exact False.elim (Prime.excludes full product split)
  · exact singletonOrFactor

/--
Terminal-prime component exhaustion in its final concrete form: singleton,
one inherited lower-rank factor, or one explicit missing compatibility tuple.
-/
theorem terminalPrimeComponentProductExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (Prime : TerminalPrimeFullComponentTensorSplitExclusion F) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤ 1 ∨
      (∃ (full : ComponentProductFull F)
        (product : ResidualComponentProduct F)
        (slot : GateSlot F),
          1 < (fullComponentFactorAt F full product slot).edges.card ∧
          (productComponentAt F product slot).card < r + 1 ∧
          Not (Concrete.HasSunflower k
            (fullComponentFactorAt F full product slot)) ∧
          (PrivateWitnessReduction.residualFamily F).edges.card ≤
            (fullComponentFactorAt F full product slot).edges.card) ∨
      Nonempty (MissingComponentCombination F) := by
  classical
  rcases componentProductFull_or_missing F with full | missing
  · by_cases residualEmpty :
        (PrivateWitnessReduction.residualFamily F).edges = ∅
    · exact Or.inl (by simp [residualEmpty])
    · have residualNonempty :
          (PrivateWitnessReduction.residualFamily F).edges.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr residualEmpty
      rcases residualNonempty with ⟨edge, edge_mem⟩
      let product := residualProductCode F ⟨edge, edge_mem⟩
      rcases fullComponentProduct_singleton_or_lowerRankFactor_of_terminalPrime
          F noSunflower Prime full product with singleton | factor
      · exact Or.inl singleton
      · exact Or.inr <| Or.inl ⟨full, product, factor⟩
  · exact Or.inr <| Or.inr missing

theorem petal_mem_residualOverlapCell_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    petal ∈ residualOverlapCell F x ↔
      (residualPetalComponent F x petal).Nonempty := by
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

/-- Inside-support and outside-support ranks account for the whole residual rank. -/
theorem residual_support_rank_accounting
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (PrivateWitnessReduction.residual F x ∩ residualSupport F).card +
        (residualOutside F x).card = r + 1 := by
  rw [residualOutside, Finset.card_inter_add_card_sdiff]
  exact PrivateWitnessReduction.residual_card F x

/-- The outside remainder and all petal components determine a residual exactly. -/
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
  intro y
  by_cases inSupport : y ∈ residualSupport F
  · rcases Finset.mem_biUnion.mp inSupport with
      ⟨petal, petal_mem, y_mem_petal⟩
    let selected : {edge // edge ∈ (residualMatching F).matching.petals} :=
      ⟨petal, petal_mem⟩
    have sameComponent := congrArg (fun edge : Finset alpha => y ∈ edge)
      (componentsEq selected)
    have reduced : y ∈ petal →
        (y ∈ PrivateWitnessReduction.residual F left ↔
          y ∈ PrivateWitnessReduction.residual F right) := by
      simpa [residualPetalComponent, selected] using sameComponent
    exact reduced y_mem_petal
  · have sameOutside := congrArg (fun edge : Finset alpha => y ∈ edge) outsideEq
    simpa [residualOutside, inSupport] using sameOutside

/--
Every genuine residual distinction localizes either to the outside remainder
or to one named matching-petal component.  This is the concrete tensor-split
witness supplied by the pincer construction.
-/
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
Within one Venn cell, a distinct residual either changes the outside remainder
or changes content inside a petal occupied by both residuals.
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

/-- A singleton-cell residual with no outside remainder is the selected petal itself. -/
theorem residual_eq_petal_of_singletonCell_of_outside_empty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (singletonCell : residualOverlapCell F x = {petal})
    (outsideEmpty : residualOutside F x = ∅) :
    PrivateWitnessReduction.residual F x = petal.val := by
  classical
  have residual_subset : PrivateWitnessReduction.residual F x ⊆ petal.val := by
    intro y y_mem
    have y_support : y ∈ residualSupport F := by
      by_contra y_not_support
      have y_outside : y ∈ residualOutside F x := by
        exact Finset.mem_sdiff.mpr ⟨y_mem, y_not_support⟩
      rw [outsideEmpty] at y_outside
      exact Finset.notMem_empty y y_outside
    rcases Finset.mem_biUnion.mp y_support with
      ⟨chosen, chosen_mem, y_chosen⟩
    let selected : {edge // edge ∈ (residualMatching F).matching.petals} :=
      ⟨chosen, chosen_mem⟩
    have selected_mem : selected ∈ residualOverlapCell F x := by
      apply (petal_mem_residualOverlapCell_iff F x selected).mpr
      exact ⟨y, Finset.mem_inter.mpr ⟨y_mem, y_chosen⟩⟩
    rw [singletonCell, Finset.mem_singleton] at selected_mem
    have chosen_eq : chosen = petal.val := congrArg Subtype.val selected_mem
    simpa [chosen_eq] using y_chosen
  apply Finset.eq_of_subset_of_card_le residual_subset
  rw [PrivateWitnessReduction.residual_card F x]
  exact Nat.le_of_eq <|
    (PrivateWitnessReduction.residualFamily F).uniform petal.val
      ((residualMatching F).matching.petals_subset petal.property)

/--
Distinct residuals in one cell force a nontrivial rank split: one residual has
outside content, or the common cell occupies at least two disjoint petals.
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

/-- A nonempty outside remainder splits the residual into two positive lower-rank parts. -/
theorem outside_nonempty_gives_proper_rank_split
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (outsideNonempty : (residualOutside F x).Nonempty) :
    (PrivateWitnessReduction.residual F x ∩ residualSupport F).Nonempty ∧
      (PrivateWitnessReduction.residual F x ∩ residualSupport F).card < r + 1 ∧
      (residualOutside F x).card < r + 1 := by
  classical
  have insideNonempty :
      (PrivateWitnessReduction.residual F x ∩ residualSupport F).Nonempty := by
    rcases residualOverlapCell_nonempty F x with ⟨petal, petal_mem⟩
    rcases (petal_mem_residualOverlapCell_iff F x petal).mp petal_mem with
      ⟨y, y_component⟩
    rcases Finset.mem_inter.mp y_component with ⟨y_residual, y_petal⟩
    have y_support : y ∈ residualSupport F :=
      Finset.mem_biUnion.mpr ⟨petal.val, petal.property, y_petal⟩
    exact ⟨y, Finset.mem_inter.mpr ⟨y_residual, y_support⟩⟩
  have accounting := residual_support_rank_accounting F x
  have insidePositive :
      0 < (PrivateWitnessReduction.residual F x ∩ residualSupport F).card :=
    Finset.card_pos.mpr insideNonempty
  have outsidePositive : 0 < (residualOutside F x).card :=
    Finset.card_pos.mpr outsideNonempty
  exact ⟨insideNonempty, by omega, by omega⟩

/-- Every occupied component is lower-rank when its Venn cell occupies two petals. -/
theorem occupiedPetal_card_lt_of_two_le_cell
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (_petal_mem : petal ∈ residualOverlapCell F x)
    (two_le : 2 ≤ (residualOverlapCell F x).card) :
    (residualPetalComponent F x petal).card < r + 1 := by
  classical
  obtain ⟨other, other_mem, other_ne⟩ :=
    Finset.exists_mem_ne (by omega : 1 < (residualOverlapCell F x).card) petal
  rcases (petal_mem_residualOverlapCell_iff F x other).mp other_mem with
    ⟨y, y_component⟩
  rcases Finset.mem_inter.mp y_component with ⟨y_residual, y_other⟩
  have petals_disjoint : Disjoint other.val petal.val := by
    simpa using
      (residualMatching F).matching.residuals_disjoint
        other.val petal.val other.property petal.property
        (fun same => other_ne (Subtype.ext same))
  have y_not_petal : y ∉ petal.val := fun y_petal =>
    Finset.disjoint_left.mp petals_disjoint y_other y_petal
  have component_subset : residualPetalComponent F x petal ⊆
      PrivateWitnessReduction.residual F x := by
    exact Finset.inter_subset_left
  have component_strict : residualPetalComponent F x petal ⊂
      PrivateWitnessReduction.residual F x :=
    (Finset.ssubset_iff_of_subset component_subset).mpr
      ⟨y, y_residual, fun y_component =>
        y_not_petal (Finset.mem_inter.mp y_component).2⟩
  rw [← PrivateWitnessReduction.residual_card F x]
  exact Finset.card_lt_card component_strict

/-- A concrete finite witness that two same-cell residuals are still different. -/
structure ResidualDistinctionWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) where
  point : alpha
  membershipDiff :
    (point ∈ PrivateWitnessReduction.residual F left ∧
        point ∉ PrivateWitnessReduction.residual F right) ∨
      (point ∈ PrivateWitnessReduction.residual F right ∧
        point ∉ PrivateWitnessReduction.residual F left)

/-- Every unequal pair of residuals has a finite symmetric-difference witness. -/
noncomputable def distinctionWitnessOfNe
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (different : PrivateWitnessReduction.residual F left ≠
      PrivateWitnessReduction.residual F right) :
    ResidualDistinctionWitness F left right := by
  classical
  have nonempty :
      (PrivateWitnessReduction.residual F left ∆
        PrivateWitnessReduction.residual F right).Nonempty :=
    Finset.symmDiff_nonempty.mpr different
  let point := Classical.choose nonempty
  have point_mem := Classical.choose_spec nonempty
  refine ⟨point, ?_⟩
  exact Finset.mem_symmDiff.mp point_mem

/--
A residual distinction is same-domain finite data.  In the fixed-base AASC
ledger it is a same-side refinement, never an independent authorizer.
-/
def residualDistinctionAttempt : CorpusMachinery.FixedBaseStrengtheningAttempt where
  locus := .auxiliaryData
  auxiliaryFactor := .sameSideRefinement

theorem residualDistinctionAttempt_disposition :
    CorpusMachinery.strengtheningDisposition residualDistinctionAttempt =
      SameScopeFactorDisposition.sameSideRefinement := by
  rfl

theorem residualDistinctionAttempt_not_independent :
    Not (CorpusMachinery.strengtheningDisposition residualDistinctionAttempt =
      SameScopeFactorDisposition.independentAuthorizer) :=
  CorpusMachinery.strengtheningDisposition_ne_independentAuthorizer _

/--
The Mathlib-AASC pincer step.  Inside one visible residual Venn cell, either
the residual is exactly duplicated (the bounded-fiber branch), or a concrete
finite distinction survives and is classified as non-authorizing same-domain
data.  This theorem does not identify the latter branch with skin; that is the
remaining endpoint-factorization obligation.
-/
theorem sameCell_duplicate_or_finiteDistinction
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (_sameCell : residualOverlapCell F left = residualOverlapCell F right) :
    PrivateWitnessReduction.residual F left =
        PrivateWitnessReduction.residual F right ∨
      Nonempty (ResidualDistinctionWitness F left right) := by
  by_cases sameResidual : PrivateWitnessReduction.residual F left =
      PrivateWitnessReduction.residual F right
  · exact Or.inl sameResidual
  · exact Or.inr ⟨distinctionWitnessOfNe sameResidual⟩

/-- Exact-residual occupants, hence also exact occupants of one Venn cell, are bounded by `k - 1`. -/
theorem exactResidualFiber_card_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (edge : Finset alpha) :
    (PrivateWitnessReduction.residualFiber F edge).card < k :=
  PrivateWitnessReduction.residualFiber_card_lt F noSunflower edge

/-- Every residual has positive content inside the second matching support. -/
theorem residual_inter_support_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (PrivateWitnessReduction.residual F x ∩ residualSupport F).Nonempty := by
  classical
  rcases residualOverlapCell_nonempty F x with ⟨petal, petal_mem⟩
  rcases (petal_mem_residualOverlapCell_iff F x petal).mp petal_mem with
    ⟨y, y_component⟩
  rcases Finset.mem_inter.mp y_component with ⟨y_residual, y_petal⟩
  have y_support : y ∈ residualSupport F :=
    Finset.mem_biUnion.mpr ⟨petal.val, petal.property, y_petal⟩
  exact ⟨y, Finset.mem_inter.mpr ⟨y_residual, y_support⟩⟩

/-- The outside coordinate always consumes strictly less than the residual rank. -/
theorem residualOutside_card_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (residualOutside F x).card < r + 1 := by
  have insidePositive :
      0 < (PrivateWitnessReduction.residual F x ∩ residualSupport F).card :=
    Finset.card_pos.mpr (residual_inter_support_nonempty F x)
  have accounting := residual_support_rank_accounting F x
  omega

/-- A full-rank component inside one matching petal is the whole residual and the whole petal. -/
theorem residual_eq_petal_of_full_component
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (fullRank : (residualPetalComponent F x petal).card = r + 1) :
    PrivateWitnessReduction.residual F x = petal.val := by
  classical
  have component_eq_residual : residualPetalComponent F x petal =
      PrivateWitnessReduction.residual F x := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    change (PrivateWitnessReduction.residual F x).card ≤
      (residualPetalComponent F x petal).card
    rw [fullRank, PrivateWitnessReduction.residual_card F x]
  have petal_mem_residualFamily : petal.val ∈
      (PrivateWitnessReduction.residualFamily F).edges :=
    (residualMatching F).matching.petals_subset petal.property
  have petal_card : petal.val.card = r + 1 :=
    (PrivateWitnessReduction.residualFamily F).uniform
      petal.val petal_mem_residualFamily
  have component_eq_petal : residualPetalComponent F x petal = petal.val := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    change petal.val.card ≤ (residualPetalComponent F x petal).card
    rw [fullRank, petal_card]
  exact component_eq_residual.symm.trans component_eq_petal

/-- The outside coordinate of every realized residual is lower-rank. -/
theorem realizedOutsideComponent_card_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    (productComponentAt F (residualProductCode F edge) none).card < r + 1 := by
  rcases PrivateWitnessReduction.mem_residualFamily_iff.mp edge.property with
    ⟨x, sameEdge⟩
  change (edge.val \ residualSupport F).card < r + 1
  rw [← sameEdge]
  exact residualOutside_card_lt F x

/-- At a fixed petal, a realized full-rank component determines the residual uniquely. -/
theorem realizedEdge_eq_petal_of_full_component
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {petal // petal ∈ (residualMatching F).matching.petals})
    (fullRank :
      (productComponentAt F (residualProductCode F edge) (some petal)).card =
        r + 1) :
    edge.val = petal.val := by
  rcases PrivateWitnessReduction.mem_residualFamily_iff.mp edge.property with
    ⟨x, sameEdge⟩
  have componentFull : (residualPetalComponent F x petal).card = r + 1 := by
    simpa [productComponentAt, residualProductCode, residualPetalComponent,
      sameEdge] using fullRank
  rw [← sameEdge]
  exact residual_eq_petal_of_full_component F x petal componentFull

/-- Every selected component of a realized residual has rank at most the residual rank. -/
theorem realizedComponent_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (slot : GateSlot F) :
    (productComponentAt F (residualProductCode F edge) slot).card ≤ r + 1 := by
  cases slot with
  | none =>
      change (edge.val \ residualSupport F).card ≤ r + 1
      calc
        (edge.val \ residualSupport F).card ≤ edge.val.card :=
          Finset.card_le_card Finset.sdiff_subset
        _ = r + 1 :=
          (PrivateWitnessReduction.residualFamily F).uniform edge.val edge.property
  | some petal =>
      change (edge.val ∩ petal.val).card ≤ r + 1
      calc
        (edge.val ∩ petal.val).card ≤ edge.val.card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = r + 1 :=
          (PrivateWitnessReduction.residualFamily F).uniform edge.val edge.property

/-- The realized residuals whose component at one slot still has full rank. -/
noncomputable def fullRankGateEdges
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (slot : GateSlot F) :
    Finset {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges} :=
  Finset.univ.filter fun edge =>
    (productComponentAt F (residualProductCode F edge) slot).card = r + 1

theorem mem_fullRankGateEdges_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (slot : GateSlot F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    edge ∈ fullRankGateEdges F slot ↔
      (productComponentAt F (residualProductCode F edge) slot).card = r + 1 := by
  simp [fullRankGateEdges]

/-- At every gate slot there is at most one realized full-rank exception. -/
theorem fullRankGateEdges_card_le_one
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (slot : GateSlot F) :
    (fullRankGateEdges F slot).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro left right left_mem right_mem
  have leftFull := (mem_fullRankGateEdges_iff F slot left).mp left_mem
  have rightFull := (mem_fullRankGateEdges_iff F slot right).mp right_mem
  cases slot with
  | none =>
      have leftLower := realizedOutsideComponent_card_lt F left
      omega
  | some petal =>
      apply Subtype.ext
      exact (realizedEdge_eq_petal_of_full_component F left petal leftFull).trans
        (realizedEdge_eq_petal_of_full_component F right petal rightFull).symm

/-- The rank-lowered part of one gate-disagreement branch. -/
noncomputable def lowerRankGateDisagreementFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F) :
    Finset {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges} :=
  (gateDisagreementFiber F missing slot).filter fun edge =>
    (productComponentAt F (residualProductCode F edge) slot).card < r + 1

/-- The complementary, necessarily full-rank, part of a gate-disagreement branch. -/
noncomputable def nonLowerRankGateDisagreementFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F) :
    Finset {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges} :=
  (gateDisagreementFiber F missing slot).filter fun edge =>
    Not ((productComponentAt F (residualProductCode F edge) slot).card < r + 1)

theorem gateFiber_rank_partition
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F) :
    (lowerRankGateDisagreementFiber F missing slot).card +
        (nonLowerRankGateDisagreementFiber F missing slot).card =
      (gateDisagreementFiber F missing slot).card := by
  classical
  simpa [lowerRankGateDisagreementFiber,
    nonLowerRankGateDisagreementFiber] using
    (Finset.card_filter_add_card_filter_not
      (s := gateDisagreementFiber F missing slot)
      (fun edge =>
        (productComponentAt F (residualProductCode F edge) slot).card < r + 1))

theorem nonLowerRankGateDisagreementFiber_subset_fullRank
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F) :
    nonLowerRankGateDisagreementFiber F missing slot ⊆
      fullRankGateEdges F slot := by
  classical
  intro edge edge_mem
  have notLower : Not
      ((productComponentAt F (residualProductCode F edge) slot).card < r + 1) :=
    (Finset.mem_filter.mp edge_mem).2
  have rankLe := realizedComponent_card_le F edge slot
  apply (mem_fullRankGateEdges_iff F slot edge).mpr
  omega

theorem nonLowerRankGateDisagreementFiber_card_le_one
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F) :
    (nonLowerRankGateDisagreementFiber F missing slot).card ≤ 1 :=
  (Finset.card_le_card
    (nonLowerRankGateDisagreementFiber_subset_fullRank F missing slot)).trans
      (fullRankGateEdges_card_le_one F slot)

/-- Each gate branch consists of a lower-rank part plus at most one exceptional residual. -/
theorem gateDisagreementFiber_card_le_lowerRank_succ
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F) :
    (gateDisagreementFiber F missing slot).card ≤
      (lowerRankGateDisagreementFiber F missing slot).card + 1 := by
  have partition := gateFiber_rank_partition F missing slot
  have exceptional :=
    nonLowerRankGateDisagreementFiber_card_le_one F missing slot
  omega

/--
If the non-full relation exceeds `k * (t + 1)`, more than `t` residuals are
forced into one named gate branch at a strictly lower component rank.
-/
theorem exists_large_lowerRankGateDisagreementFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r k t : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (oversized : k * (t + 1) <
      (PrivateWitnessReduction.residualFamily F).edges.card) :
    ∃ slot : GateSlot F,
      t < (lowerRankGateDisagreementFiber F missing slot).card := by
  rcases exists_large_gateDisagreementFiber F noSunflower missing oversized with
    ⟨slot, large⟩
  refine ⟨slot, ?_⟩
  have branchBound := gateDisagreementFiber_card_le_lowerRank_succ F missing slot
  omega

/--
A uniform bound on the lower-rank branches of one missing tuple bounds the
entire residual relation.  Thus the non-full coercivity burden is now localized
to the lower-rank gate fibers rather than the raw component product.
-/
theorem residualFamily_card_le_of_lowerRankGateFiberBound
    {alpha : Type}
    [DecidableEq alpha]
    {r k M : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (fiberBound : ∀ slot : GateSlot F,
      (lowerRankGateDisagreementFiber F missing slot).card ≤ M) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤ k * (M + 1) := by
  by_contra notBounded
  have oversized : k * (M + 1) <
      (PrivateWitnessReduction.residualFamily F).edges.card :=
    Nat.lt_of_not_ge notBounded
  rcases exists_large_lowerRankGateDisagreementFiber
      F noSunflower missing oversized with ⟨slot, large⟩
  exact (Nat.not_lt_of_ge (fiberBound slot)) large

/-- The same lower-rank gate bound controls the concrete minimal blocker. -/
theorem minimalBlocker_card_le_of_lowerRankGateFiberBound
    {alpha : Type}
    [DecidableEq alpha]
    {r k M : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (fiberBound : ∀ slot : GateSlot F,
      (lowerRankGateDisagreementFiber F missing slot).card ≤ M) :
    (MinimalBlocker.minimalBlocker F).card ≤ k * (k * (M + 1)) := by
  calc
    (MinimalBlocker.minimalBlocker F).card ≤
        k * (PrivateWitnessReduction.residualFamily F).edges.card :=
      PrivateWitnessReduction.minimalBlocker_card_le_k_mul_residualFamily
        F noSunflower
    _ ≤ k * (k * (M + 1)) :=
      Nat.mul_le_mul_left k
        (residualFamily_card_le_of_lowerRankGateFiberBound
          F noSunflower missing fiberBound)

/--
Unconditional exhaustion of the component relation: either it is the already
recursive full tensor product, or one missing tuple reduces every cardinality
estimate to uniformly bounding its named lower-rank gate fibers.
-/
theorem componentProductFull_or_lowerRankGateBound
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    ComponentProductFull F ∨
      ∃ missing : MissingComponentCombination F,
        ∀ M : Nat,
          (∀ slot : GateSlot F,
            (lowerRankGateDisagreementFiber F missing slot).card ≤ M) →
          (PrivateWitnessReduction.residualFamily F).edges.card ≤
            k * (M + 1) := by
  rcases componentProductFull_or_missing F with full | nonempty
  · exact Or.inl full
  · rcases nonempty with ⟨missing⟩
    exact Or.inr ⟨missing, fun M bound =>
      residualFamily_card_le_of_lowerRankGateFiberBound
        F noSunflower missing bound⟩

end ResidualVennPincer
end V2
end SunflowerAASC
