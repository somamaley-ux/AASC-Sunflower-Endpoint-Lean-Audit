import SunflowerAASC.V2.GlobalMergeReconstruction

namespace SunflowerAASC
namespace V2
namespace RankWeightedMergeCharging

open ResidualVennPincer
open ResidualGateContextQuotient
open GlobalMergeReconstruction

/--
The exact deletion charge missing from the non-full product branch.  Contexts
are not counted as unweighted labels: a context section of rank `s` consumes
`base ^ s`, and the sum of those costs must fit in the parent rank budget.
-/
def RankWeightedContextCharge
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (base : Nat) : Prop :=
  (Finset.univ.sum fun context : {context // context ∈
      occupiedLowerRankGateContexts F missing slot} =>
    base ^ gateContextSectionRank F missing slot context) <=
    base ^ (r + 1)

/--
A rank-weighted context charge and the ordinary lower-rank induction bound
control one complete lower-rank gate fibre.  No root-to-seed injection occurs.
-/
theorem lowerRankGateFiber_card_le_of_rankWeightedContextCharge
    {alpha : Type}
    [DecidableEq alpha]
    {r k base : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (lowerRankBound : forall s : Nat, s < r + 1 ->
      forall G : Concrete.UniformSetFamily alpha s,
        Not (Concrete.HasSunflower k G) ->
        G.edges.card <= base ^ s)
    (charge : RankWeightedContextCharge F missing slot base) :
    (lowerRankGateDisagreementFiber F missing slot).card <=
      base ^ (r + 1) := by
  rw [lowerRankGateFiber_card_eq_sum_contextFibers]
  calc
    (∑ context ∈ occupiedLowerRankGateContexts F missing slot,
        (lowerRankGateContextFiber F missing slot context).card) =
        ∑ context : {context // context ∈
          occupiedLowerRankGateContexts F missing slot},
          (lowerRankGateContextFiber F missing slot context.val).card := by
      rw [← Finset.sum_attach, Finset.univ_eq_attach]
    _ <= ∑ context : {context // context ∈
        occupiedLowerRankGateContexts F missing slot},
          base ^ gateContextSectionRank F missing slot context := by
      apply Finset.sum_le_sum
      intro context _contextMem
      exact (contextFiber_card_le_section
        F missing slot context).trans
          (lowerRankBound
            (gateContextSectionRank F missing slot context)
            (gateContextSection_rank_lt
              F missing slot context)
            (gateContextSection F missing slot context)
            (gateContextSection_noSunflower
              F noSunflower missing slot context))
    _ <= base ^ (r + 1) := charge

/-- Every gate in one missing-tuple branch carries the exact weighted charge. -/
structure MissingGateRankWeightedCharging
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (base : Nat) : Prop where
  charge : forall slot : GateSlot F,
    RankWeightedContextCharge F missing slot base

/--
Weighted charging controls the complete missing branch, including its at-most
`k` gate labels and one full-rank exception at each gate.
-/
theorem residualFamily_card_le_of_rankWeightedCharging
    {alpha : Type}
    [DecidableEq alpha]
    {r k base : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (lowerRankBound : forall s : Nat, s < r + 1 ->
      forall G : Concrete.UniformSetFamily alpha s,
        Not (Concrete.HasSunflower k G) ->
        G.edges.card <= base ^ s)
    (charging : MissingGateRankWeightedCharging
      F noSunflower missing base) :
    (PrivateWitnessReduction.residualFamily F).edges.card <=
      k * (base ^ (r + 1) + 1) := by
  apply residualFamily_card_le_of_lowerRankGateFiberBound
    F noSunflower missing
  intro slot
  exact lowerRankGateFiber_card_le_of_rankWeightedContextCharge
    F noSunflower missing slot lowerRankBound (charging.charge slot)

/-- One parent-rank unit absorbs the finite gate label and exceptional member. -/
theorem gateFactor_absorbed_by_nextPower
    {r k base : Nat}
    (basePositive : 0 < base)
    (twoK_le_base : 2 * k <= base) :
    k * (base ^ (r + 1) + 1) <= base ^ (r + 2) := by
  have powerPositive : 0 < base ^ (r + 1) := pow_pos basePositive _
  have one_le_power : 1 <= base ^ (r + 1) := by omega
  calc
    k * (base ^ (r + 1) + 1) <=
        k * (base ^ (r + 1) + base ^ (r + 1)) := by
      exact Nat.mul_le_mul_left k (Nat.add_le_add_left one_le_power _)
    _ = (2 * k) * base ^ (r + 1) := by ring
    _ <= base * base ^ (r + 1) :=
      Nat.mul_le_mul_right (base ^ (r + 1)) twoK_le_base
    _ = base ^ (r + 2) := by
      rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
      exact Nat.mul_comm _ _

/--
The missing branch therefore satisfies a next-rank power estimate once its
contexts are genuinely charged rather than assumed injective.
-/
theorem residualFamily_card_le_nextPower_of_rankWeightedCharging
    {alpha : Type}
    [DecidableEq alpha]
    {r k base : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (basePositive : 0 < base)
    (twoK_le_base : 2 * k <= base)
    (lowerRankBound : forall s : Nat, s < r + 1 ->
      forall G : Concrete.UniformSetFamily alpha s,
        Not (Concrete.HasSunflower k G) ->
        G.edges.card <= base ^ s)
    (charging : MissingGateRankWeightedCharging
      F noSunflower missing base) :
    (PrivateWitnessReduction.residualFamily F).edges.card <=
      base ^ (r + 2) :=
  (residualFamily_card_le_of_rankWeightedCharging
    F noSunflower missing lowerRankBound charging).trans
      (gateFactor_absorbed_by_nextPower basePositive twoK_le_base)

/--
The precise rank-uniform source still to be constructed: every literal missing
component tuple receives the weighted deletion charge above.  It contains no
Hall law, terminal selector, role injection, finite endpoint code, or endpoint
cardinality conclusion.
-/
structure RankUniformMissingGateChargingSource
    (alpha : Type)
    [DecidableEq alpha]
    (k base : Nat) : Prop where
  charge : forall r : Nat,
    forall F : Concrete.UniformSetFamily alpha (r + 2),
    forall noSunflower : Not (Concrete.HasSunflower k F),
    forall missing : MissingComponentCombination F,
      MissingGateRankWeightedCharging F noSunflower missing base

/--
Full products recurse exactly, while every non-full product is handled by the
rank-weighted charging source.  The result is a uniform next-rank estimate for
the private residual family, with no claim that the source has yet been built.
-/
theorem residualFamily_card_le_nextPower_of_rankUniformCharging
    {alpha : Type}
    [DecidableEq alpha]
    {r k base : Nat}
    (source : RankUniformMissingGateChargingSource alpha k base)
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (basePositive : 0 < base)
    (twoK_le_base : 2 * k <= base)
    (lowerRankBound : forall s : Nat, s < r + 1 ->
      forall G : Concrete.UniformSetFamily alpha s,
        Not (Concrete.HasSunflower k G) ->
        G.edges.card <= base ^ s) :
    (PrivateWitnessReduction.residualFamily F).edges.card <=
      base ^ (r + 2) := by
  rcases componentProductFull_or_missing F with full | missing
  · have fullBound :=
      (fullProductRecursiveBranch F noSunflower full).recursiveBound
        base basePositive lowerRankBound
    exact fullBound.trans <|
      pow_le_pow_right' (by omega : 1 <= base) (by omega)
  · rcases missing with ⟨missing⟩
    exact residualFamily_card_le_nextPower_of_rankWeightedCharging
      F noSunflower missing basePositive twoK_le_base lowerRankBound
        (source.charge r F noSunflower missing)

end RankWeightedMergeCharging
end V2
end SunflowerAASC
