import SunflowerAASC.V2.MergeDispositionClosure
import SunflowerAASC.V2.ResidualContextSignatures
import SunflowerAASC.V2.RankChargedProductSystem

namespace SunflowerAASC
namespace V2
namespace GlobalMergeReconstruction

open ResidualVennPincer
open ResidualGateSections
open ResidualGateContextQuotient
open ResidualContextSignatures

/--
The full-product branch reconstructs every residual from disjoint component
languages whose ranks add exactly to the residual rank.  Consequently any
uniform lower-rank endpoint estimate composes without exponent loss.
-/
structure FullProductRecursiveBranch
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F)) where
  full : ComponentProductFull F
  residualCode_injective : Function.Injective (residualProductCode F)
  residualRank_exact :
    ∀ edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges},
      (componentCodeOfEdge F edge.val).rank = r + 1
  recursiveBound :
    ∀ base : Nat,
      0 < base ->
      (∀ s : Nat, s < r + 1 ->
        ∀ G : Concrete.UniformSetFamily alpha s,
          Not (Concrete.HasSunflower k G) ->
          G.edges.card ≤ base ^ s) ->
      (PrivateWitnessReduction.residualFamily F).edges.card ≤
        base ^ (r + 1)

/-- The exact full-product branch constructed from its literal fullness proof. -/
noncomputable def fullProductRecursiveBranch
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : ComponentProductFull F) :
    FullProductRecursiveBranch F noSunflower where
  full := full
  residualCode_injective := residualProductCode_injective F
  residualRank_exact := by
    intro edge
    exact componentCodeOfEdge_rank F edge.val |>.trans
      ((PrivateWitnessReduction.residualFamily F).uniform
        edge.val edge.property)
  recursiveBound := by
    intro base basePositive lowerRankBound
    by_cases familyNonempty :
        (PrivateWitnessReduction.residualFamily F).edges.Nonempty
    · rcases familyNonempty with ⟨edge, edgeMem⟩
      let product : ResidualComponentProduct F :=
        residualProductCode F ⟨edge, edgeMem⟩
      exact residualFamily_card_le_pow_of_full_lowerRankBounds
        F noSunflower full product basePositive lowerRankBound
    · have familyEmpty :
          (PrivateWitnessReduction.residualFamily F).edges = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp familyNonempty
      simp [familyEmpty]

/--
The non-full branch has one missing component tuple.  Every residual is charged
to a named gate; only one full-rank exception can occur at each gate, and every
other charged member has an honest lower-rank sunflower-free recursive section.
-/
structure MissingGateRecursiveBranch
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F)) where
  missing : MissingComponentCombination F
  gateCount_le : Fintype.card (GateSlot F) ≤ k
  assignedGate :
    {edge // edge ∈ (PrivateWitnessReduction.residualFamily F).edges} ->
      GateSlot F
  assignedGate_differs :
    ∀ edge,
      productComponentAt F (residualProductCode F edge) (assignedGate edge) ≠
        productComponentAt F missing.code (assignedGate edge)
  fullRankException_card_le_one :
    ∀ slot : GateSlot F,
      (nonLowerRankGateDisagreementFiber F missing slot).card ≤ 1
  lowerRankRecursiveSection :
    ∀ slot : GateSlot F,
      ∀ edge : {edge // edge ∈
        (PrivateWitnessReduction.residualFamily F).edges},
        edge ∈ lowerRankGateDisagreementFiber F missing slot ->
          ∃ s : Nat, s < r + 1 ∧
            ∃ G : Concrete.UniformSetFamily alpha s,
              Not (Concrete.HasSunflower k G) ∧
                productComponentAt F (residualProductCode F edge) slot ∈
                  G.edges
  cardinalReduction :
    ∀ M : Nat,
      (∀ slot : GateSlot F,
        (lowerRankGateDisagreementFiber F missing slot).card ≤ M) ->
      (PrivateWitnessReduction.residualFamily F).edges.card ≤ k * (M + 1)

/-- The exact missing-gate branch constructed from a literal missing tuple. -/
noncomputable def missingGateRecursiveBranch
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F) :
    MissingGateRecursiveBranch F noSunflower where
  missing := missing
  gateCount_le := gateSlot_card_le F noSunflower
  assignedGate := gateDisagreementSlot F missing
  assignedGate_differs := gateDisagreementSlot_spec F missing
  fullRankException_card_le_one :=
    nonLowerRankGateDisagreementFiber_card_le_one F missing
  lowerRankRecursiveSection := by
    intro slot edge edgeMem
    exact lowerRankGateFiber_member_has_recursive_section
      F noSunflower missing slot edge edgeMem
  cardinalReduction := by
    intro M fiberBound
    exact residualFamily_card_le_of_lowerRankGateFiberBound
      F noSunflower missing fiberBound

/-- The complete global residual reconstruction ledger. -/
inductive ResidualReconstructionDisposition
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F)) : Type
  | fullProduct
      (branch : FullProductRecursiveBranch F noSunflower) :
      ResidualReconstructionDisposition F noSunflower
  | missingGate
      (branch : MissingGateRecursiveBranch F noSunflower) :
      ResidualReconstructionDisposition F noSunflower

/--
Every sunflower-free private-residual family enters the full recursive product
or the explicit missing-gate charging branch.  This theorem has no role code,
Hall law, injective terminal selector, or endpoint-bound premise.
-/
theorem residualReconstruction_disposition
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Nonempty (ResidualReconstructionDisposition F noSunflower) := by
  rcases componentProductFull_or_missing F with full | missing
  · exact ⟨ResidualReconstructionDisposition.fullProduct
      (fullProductRecursiveBranch F noSunflower full)⟩
  · rcases missing with ⟨missing⟩
    exact ⟨ResidualReconstructionDisposition.missingGate
      (missingGateRecursiveBranch F noSunflower missing)⟩

/--
Inside one occupied coarse support cell, distinct normalized contexts always
carry a named finite component witness.  This is the profile-refinement branch
needed before any AASC tensor or prime classification is invoked.
-/
theorem sameSupportContext_equal_or_finiteWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (left right : {context // context ∈
      occupiedLowerRankGateContexts F missing selected})
    (sameSupportCode :
      occupiedContextSupportCode F noSunflower missing selected left =
        occupiedContextSupportCode F noSunflower missing selected right) :
    left = right ∨
      Nonempty (SameSupportContextDistinctionWitness
        F missing.code left.val right.val) := by
  by_cases same : left = right
  · exact Or.inl same
  · exact Or.inr <| sameSupportCode_distinct_has_finite_witness
      F noSunflower missing selected left right sameSupportCode same

end GlobalMergeReconstruction
end V2
end SunflowerAASC
