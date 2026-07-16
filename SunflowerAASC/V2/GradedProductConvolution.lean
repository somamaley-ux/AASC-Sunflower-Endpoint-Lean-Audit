import SunflowerAASC.V2.RankCompatibleProductGate
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace SunflowerAASC
namespace V2
namespace GradedProductConvolution

open ResidualVennPincer
open RankCompatibleProductGate

/-- Every available component has rank at most the residual rank. -/
theorem productComponent_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (slot : GateSlot F) :
    (productComponentAt F product slot).card ≤ r + 1 := by
  cases slot with
  | none =>
      rcases Finset.mem_image.mp product.2.property with
        ⟨edge, edgeMem, sameOutside⟩
      change product.2.val.card ≤ r + 1
      rw [← sameOutside]
      calc
        (edge \ residualSupport F).card ≤ edge.card :=
          Finset.card_le_card Finset.sdiff_subset
        _ = r + 1 :=
          (PrivateWitnessReduction.residualFamily F).uniform edge edgeMem
  | some petal =>
      change (product.1 petal).val.card ≤ r + 1
      calc
        (product.1 petal).val.card ≤ petal.val.card :=
          Finset.card_le_card
            (petalComponent_subset_petal F petal (product.1 petal))
        _ = r + 1 :=
          (PrivateWitnessReduction.residualFamily F).uniform petal.val
            ((residualMatching F).matching.petals_subset petal.property)

/-- The finite vector of component ranks attached to one product tuple. -/
abbrev ComponentRankProfile
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :=
  GateSlot F → Fin (r + 2)

noncomputable def productRankProfile
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F) : ComponentRankProfile F :=
  fun slot => ⟨(productComponentAt F product slot).card, by
    have rankLe := productComponent_card_le F product slot
    omega⟩

/-- Compatible tuples carrying one fixed component-rank profile. -/
abbrev RankProfileFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (profile : ComponentRankProfile F) :=
  {code : RankCompatibleProduct F //
    productRankProfile F code.val = profile}

/-- The independent product of fixed-rank component slices for one profile. -/
abbrev RankProfileProduct
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (profile : ComponentRankProfile F) :=
  ((petal : {edge // edge ∈ (residualMatching F).matching.petals}) →
      {part // part ∈
        (petalRankGradeFamily F petal (profile (some petal)).val).edges}) ×
    {outside // outside ∈
      (outsideRankGradeFamily F (profile none).val).edges}

/-- Forget compatibility while retaining all fixed-rank component choices. -/
noncomputable def rankProfileProductCode
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (profile : ComponentRankProfile F) :
    RankProfileFiber F profile → RankProfileProduct F profile :=
  fun code =>
    (fun petal => ⟨(code.val.val.1 petal).val, by
      apply (mem_petalRankGradeFamily_iff F petal _).mpr
      refine ⟨(code.val.val.1 petal).property, ?_⟩
      have sameAt := congrFun code.property (some petal)
      exact congrArg Fin.val sameAt⟩,
    ⟨code.val.val.2.val, by
      apply (mem_outsideRankGradeFamily_iff F _).mpr
      refine ⟨code.val.val.2.property, ?_⟩
      have sameAt := congrFun code.property none
      exact congrArg Fin.val sameAt⟩)

theorem rankProfileProductCode_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (profile : ComponentRankProfile F) :
    Function.Injective (rankProfileProductCode F profile) := by
  intro left right sameCode
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · funext petal
    apply Subtype.ext
    exact congrArg
      (fun encoded => ((encoded.1 petal).val : Finset alpha)) sameCode
  · apply Subtype.ext
    exact congrArg (fun encoded => (encoded.2.val : Finset alpha)) sameCode

theorem rankProfileFiber_card_le_product
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (profile : ComponentRankProfile F) :
    Fintype.card (RankProfileFiber F profile) ≤
      Fintype.card (RankProfileProduct F profile) :=
  Fintype.card_le_of_injective (rankProfileProductCode F profile)
    (rankProfileProductCode_injective F profile)

theorem rankProfileProduct_card
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (profile : ComponentRankProfile F) :
    Fintype.card (RankProfileProduct F profile) =
      (∏ petal : {edge // edge ∈ (residualMatching F).matching.petals},
        (petalRankGradeFamily F petal (profile (some petal)).val).edges.card) *
      (outsideRankGradeFamily F (profile none).val).edges.card := by
  classical
  simp [RankProfileProduct]

/-- Every occupied compatible profile spends exactly the residual rank. -/
theorem profile_rank_sum_of_fiber_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (profile : ComponentRankProfile F)
    (fiberNonempty : Nonempty (RankProfileFiber F profile)) :
    (∑ slot : GateSlot F, (profile slot).val) = r + 1 := by
  rcases fiberNonempty with ⟨code⟩
  calc
    (∑ slot : GateSlot F, (profile slot).val) =
        ∑ slot : GateSlot F,
          (productRankProfile F code.val.val slot).val := by
      rw [code.property]
    _ = ∑ slot : GateSlot F,
          (productComponentAt F code.val.val slot).card := by
      rfl
    _ = (componentCodeOfProduct F code.val.val).rank :=
      productComponentCardSum_eq_rank F code.val.val
    _ = r + 1 := code.val.property

/-- One occupied rank-profile fibre costs exactly one parent-rank power. -/
theorem rankProfileProduct_card_le_pow
    {alpha : Type}
    [DecidableEq alpha]
    {r k base : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : RankCompatibleProductFull F)
    (profile : ComponentRankProfile F)
    (fiberNonempty : Nonempty (RankProfileFiber F profile))
    (basePositive : 0 < base)
    (lowerRankBound : ∀ t : Nat, t < r + 1 →
      ∀ G : Concrete.UniformSetFamily alpha t,
        Not (Concrete.HasSunflower k G) → G.edges.card ≤ base ^ t) :
    Fintype.card (RankProfileProduct F profile) ≤ base ^ (r + 1) := by
  classical
  have profileSum := profile_rank_sum_of_fiber_nonempty F profile fiberNonempty
  have profileSumParts :
      (∑ petal : {edge // edge ∈ (residualMatching F).matching.petals},
          (profile (some petal)).val) + (profile none).val = r + 1 := by
    simpa [GateSlot, Fintype.sum_option, Nat.add_comm] using profileSum
  have petalProductBound :
      (∏ petal : {edge // edge ∈ (residualMatching F).matching.petals},
        (petalRankGradeFamily F petal (profile (some petal)).val).edges.card) ≤
      ∏ petal : {edge // edge ∈ (residualMatching F).matching.petals},
        base ^ (profile (some petal)).val := by
    apply Finset.prod_le_prod
    · intro petal _
      exact Nat.zero_le _
    · intro petal _
      apply petalRankGrade_card_le_pow F noSunflower full petal
      · have rankLt := (profile (some petal)).isLt
        omega
      · exact basePositive
      · exact lowerRankBound
  have outsideBound :
      (outsideRankGradeFamily F (profile none).val).edges.card ≤
        base ^ (profile none).val :=
    outsideRankGrade_card_le_of_lowerRankBound
      F noSunflower full lowerRankBound
  rw [rankProfileProduct_card]
  calc
    (∏ petal : {edge // edge ∈ (residualMatching F).matching.petals},
          (petalRankGradeFamily F petal (profile (some petal)).val).edges.card) *
        (outsideRankGradeFamily F (profile none).val).edges.card ≤
      (∏ petal : {edge // edge ∈ (residualMatching F).matching.petals},
          base ^ (profile (some petal)).val) *
        base ^ (profile none).val :=
      Nat.mul_le_mul petalProductBound outsideBound
    _ = base ^
        ((∑ petal : {edge // edge ∈ (residualMatching F).matching.petals},
          (profile (some petal)).val) + (profile none).val) := by
      rw [Finset.prod_pow_eq_pow_sum, pow_add]
    _ = base ^ (r + 1) := by rw [profileSumParts]

theorem rankProfileFiber_card_le_pow
    {alpha : Type}
    [DecidableEq alpha]
    {r k base : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : RankCompatibleProductFull F)
    (profile : ComponentRankProfile F)
    (basePositive : 0 < base)
    (lowerRankBound : ∀ t : Nat, t < r + 1 →
      ∀ G : Concrete.UniformSetFamily alpha t,
        Not (Concrete.HasSunflower k G) → G.edges.card ≤ base ^ t) :
    Fintype.card (RankProfileFiber F profile) ≤ base ^ (r + 1) := by
  by_cases fiberNonempty : Nonempty (RankProfileFiber F profile)
  · exact (rankProfileFiber_card_le_product F profile).trans
      (rankProfileProduct_card_le_pow F noSunflower full profile
        fiberNonempty basePositive lowerRankBound)
  · letI : IsEmpty (RankProfileFiber F profile) :=
      ⟨fun code => fiberNonempty ⟨code⟩⟩
    simp

theorem componentRankProfile_card
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    Fintype.card (ComponentRankProfile F) =
      (r + 2) ^ Fintype.card (GateSlot F) := by
  simp [ComponentRankProfile]

/-- The graded compatible layer is bounded by its finite rank-profile multiplicity. -/
theorem rankCompatibleProducts_card_le_profile_mul_pow
    {alpha : Type}
    [DecidableEq alpha]
    {r k base : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : RankCompatibleProductFull F)
    (basePositive : 0 < base)
    (lowerRankBound : ∀ t : Nat, t < r + 1 →
      ∀ G : Concrete.UniformSetFamily alpha t,
        Not (Concrete.HasSunflower k G) → G.edges.card ≤ base ^ t) :
    Fintype.card (RankCompatibleProduct F) ≤
      Fintype.card (ComponentRankProfile F) * base ^ (r + 1) := by
  by_contra notBounded
  have oversized : Fintype.card (ComponentRankProfile F) * base ^ (r + 1) <
      Fintype.card (RankCompatibleProduct F) :=
    Nat.lt_of_not_ge notBounded
  rcases Fintype.exists_lt_card_fiber_of_mul_lt_card
      (fun code : RankCompatibleProduct F => productRankProfile F code.val)
      oversized with ⟨profile, large⟩
  have fiberBound := rankProfileFiber_card_le_pow
    F noSunflower full profile basePositive lowerRankBound
  have largeFiber : base ^ (r + 1) <
      Fintype.card (RankProfileFiber F profile) := by
    change base ^ (r + 1) < Fintype.card
      {code : RankCompatibleProduct F //
        productRankProfile F code.val = profile}
    rw [Fintype.card_subtype]
    exact large
  exact (Nat.not_lt_of_ge fiberBound) largeFiber

/-- Graded fullness gives an explicit residual bound with only rank-profile overhead. -/
theorem residualFamily_card_le_rankProfile_mul_pow_of_gradedFull
    {alpha : Type}
    [DecidableEq alpha]
    {r k base : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : RankCompatibleProductFull F)
    (basePositive : 0 < base)
    (lowerRankBound : ∀ t : Nat, t < r + 1 →
      ∀ G : Concrete.UniformSetFamily alpha t,
        Not (Concrete.HasSunflower k G) → G.edges.card ≤ base ^ t) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤
      (r + 2) ^ Fintype.card (GateSlot F) * base ^ (r + 1) := by
  rw [residualFamily_card_eq_rankCompatibleProducts_of_full F full,
    ← componentRankProfile_card F]
  exact rankCompatibleProducts_card_le_profile_mul_pow
    F noSunflower full basePositive lowerRankBound

/-- Under the sunflower obstruction, at most `k` component slots remain. -/
theorem residualFamily_card_le_rankProfileBound_of_gradedFull
    {alpha : Type}
    [DecidableEq alpha]
    {r k base : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : RankCompatibleProductFull F)
    (basePositive : 0 < base)
    (lowerRankBound : ∀ t : Nat, t < r + 1 →
      ∀ G : Concrete.UniformSetFamily alpha t,
        Not (Concrete.HasSunflower k G) → G.edges.card ≤ base ^ t) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤
      (r + 2) ^ k * base ^ (r + 1) := by
  calc
    (PrivateWitnessReduction.residualFamily F).edges.card ≤
        (r + 2) ^ Fintype.card (GateSlot F) * base ^ (r + 1) :=
      residualFamily_card_le_rankProfile_mul_pow_of_gradedFull
        F noSunflower full basePositive lowerRankBound
    _ ≤ (r + 2) ^ k * base ^ (r + 1) :=
      Nat.mul_le_mul_right (base ^ (r + 1))
        (pow_le_pow_right' (by omega : 1 ≤ r + 2)
          (gateSlot_card_le F noSunflower))

end GradedProductConvolution
end V2
end SunflowerAASC
