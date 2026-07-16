import SunflowerAASC.V2.TraceAssembly
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace SunflowerAASC
namespace V2
namespace RankChargedProductSystem

/--
A bounded union of recursive product pieces.  Every piece is assembled from
lower-rank states whose total rank is charged to `rank`.
-/
structure RankChargedProductCover
    (State : Nat → Type)
    (Domain : Type)
    (rank pieceBound : Nat) where
  Piece : Type
  pieceFintype : Fintype Piece
  pieceCard_le : @Fintype.card Piece pieceFintype ≤ pieceBound
  factorCount : Piece → Nat
  factorRank : ∀ piece : Piece, Fin (factorCount piece) → Nat
  rankCharge : ∀ piece : Piece,
    (Finset.univ.sum fun factor : Fin (factorCount piece) =>
      factorRank piece factor) ≤ rank
  code : Domain →
    Sigma fun piece : Piece =>
      ∀ factor : Fin (factorCount piece), State (factorRank piece factor)
  code_injective : Function.Injective code

theorem RankChargedProductCover.factorRank_le
    {State : Nat → Type}
    {Domain : Type}
    {rank pieceBound : Nat}
    (Cover : RankChargedProductCover State Domain rank pieceBound)
    (piece : Cover.Piece)
    (factor : Fin (Cover.factorCount piece)) :
    Cover.factorRank piece factor ≤ rank := by
  have rank_le_sum : Cover.factorRank piece factor ≤
      Finset.univ.sum (fun index : Fin (Cover.factorCount piece) =>
        Cover.factorRank piece index) :=
    Finset.single_le_sum
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ factor)
  exact rank_le_sum.trans (Cover.rankCharge piece)

/--
If all recursive states through `rank` satisfy a constant-base estimate, then
the covered domain costs only one finite piece factor times that rank budget.
-/
theorem RankChargedProductCover.card_le_piece_mul_pow
    {State : Nat → Type}
    {Domain : Type}
    {rank pieceBound base : Nat}
    (Cover : RankChargedProductCover State Domain rank pieceBound)
    (domainFintype : Fintype Domain)
    (stateFintype : ∀ s : Nat, Fintype (State s))
    (base_positive : 0 < base)
    (lowerRankBound : ∀ s : Nat, s ≤ rank →
      @Fintype.card (State s) (stateFintype s) ≤ base ^ s) :
    @Fintype.card Domain domainFintype ≤ pieceBound * base ^ rank := by
  letI : Fintype Domain := domainFintype
  letI : Fintype Cover.Piece := Cover.pieceFintype
  letI stateFintypeInstance (s : Nat) : Fintype (State s) :=
    stateFintype s
  have codeBound := Fintype.card_le_of_injective
    Cover.code Cover.code_injective
  have pieceProductBound : ∀ piece : Cover.Piece,
      (Finset.univ.prod fun factor : Fin (Cover.factorCount piece) =>
        Fintype.card (State (Cover.factorRank piece factor))) ≤
        base ^ rank := by
    intro piece
    have one_le_base : 1 ≤ base := by omega
    calc
      (Finset.univ.prod fun factor : Fin (Cover.factorCount piece) =>
          Fintype.card (State (Cover.factorRank piece factor))) ≤
          Finset.univ.prod (fun factor : Fin (Cover.factorCount piece) =>
            base ^ Cover.factorRank piece factor) := by
        apply Finset.prod_le_prod
        · intro factor _
          exact Nat.zero_le _
        · intro factor _
          exact lowerRankBound (Cover.factorRank piece factor)
            (Cover.factorRank_le piece factor)
      _ = base ^ (Finset.univ.sum fun factor : Fin (Cover.factorCount piece) =>
            Cover.factorRank piece factor) := by
        rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ base ^ rank :=
        pow_le_pow_right' one_le_base (Cover.rankCharge piece)
  have targetBound :
      Fintype.card
          (Sigma fun piece : Cover.Piece =>
            ∀ factor : Fin (Cover.factorCount piece),
              State (Cover.factorRank piece factor)) ≤
        Fintype.card Cover.Piece * base ^ rank := by
    rw [Fintype.card_sigma]
    calc
      (Finset.univ.sum fun piece : Cover.Piece =>
          Fintype.card
            (∀ factor : Fin (Cover.factorCount piece),
              State (Cover.factorRank piece factor))) =
          Finset.univ.sum (fun piece : Cover.Piece =>
            Finset.univ.prod fun factor : Fin (Cover.factorCount piece) =>
              Fintype.card (State (Cover.factorRank piece factor))) := by
        apply Finset.sum_congr rfl
        intro piece _
        rw [Fintype.card_pi]
      _ ≤ Finset.univ.sum (fun _piece : Cover.Piece => base ^ rank) := by
        apply Finset.sum_le_sum
        intro piece _
        exact pieceProductBound piece
      _ = Fintype.card Cover.Piece * base ^ rank := by simp
  have boundedTarget := targetBound.trans
    (Nat.mul_le_mul_right (base ^ rank) Cover.pieceCard_le)
  exact codeBound.trans boundedTarget

/--
A Noetherian product trace.  A successor state is reconstructed from one of at
most `base` pieces and recursively smaller factors with total rank at most the
predecessor rank.
-/
structure System (base : Nat) where
  State : Nat → Type
  stateFintype : ∀ rank : Nat, Fintype (State rank)
  baseSubsingleton : ∀ left right : State 0, left = right
  successorCover : ∀ rank : Nat,
    RankChargedProductCover State (State (rank + 1)) rank base

/-- The ordinary one-predecessor trace is the one-factor special case. -/
noncomputable def ofRankDeletionSystem
    {base : Nat}
    (Deletion : TraceAssembly.RankDeletionSystem base) : System base where
  State := Deletion.State
  stateFintype := fun rank =>
    Fintype.ofInjective (Deletion.trace rank) (Deletion.trace_injective rank)
  baseSubsingleton := Deletion.baseSubsingleton
  successorCover := by
    intro rank
    exact {
      Piece := Fin base
      pieceFintype := inferInstance
      pieceCard_le := by simp
      factorCount := fun _piece => 1
      factorRank := fun _piece _factor => rank
      rankCharge := by intro _piece; simp
      code := fun state =>
        ⟨Deletion.headCode rank state,
          fun _factor => Deletion.predecessor rank state⟩
      code_injective := by
        intro left right sameCode
        apply Deletion.step_injective rank
        have pairEq :
            (Deletion.headCode rank left,
              Deletion.predecessor rank left) =
            (Deletion.headCode rank right,
              Deletion.predecessor rank right) := by
          simpa using congrArg
            (fun encoded => (encoded.1, encoded.2 (0 : Fin 1))) sameCode
        exact pairEq }

/-- Every state in a rank-charged product system has a constant-base trace. -/
theorem System.state_card_le_pow
    {base : Nat}
    (System : System base)
    (base_positive : 0 < base) :
    ∀ rank : Nat,
      @Fintype.card (System.State rank) (System.stateFintype rank) ≤
        base ^ rank := by
  intro rank
  induction rank using Nat.strong_induction_on with
  | h rank inductionHypothesis =>
      cases rank with
      | zero =>
          letI : Fintype (System.State 0) := System.stateFintype 0
          have baseCard :
              @Fintype.card (System.State 0) (System.stateFintype 0) ≤ 1 :=
            Fintype.card_le_one_iff.mpr System.baseSubsingleton
          simpa using baseCard
      | succ predecessorRank =>
          have lowerRankBound : ∀ s : Nat, s ≤ predecessorRank →
              @Fintype.card (System.State s) (System.stateFintype s) ≤
                base ^ s := by
            intro s s_le
            exact inductionHypothesis s (by omega)
          have covered :=
            (System.successorCover predecessorRank).card_le_piece_mul_pow
              (System.stateFintype (predecessorRank + 1))
              System.stateFintype base_positive lowerRankBound
          simpa [pow_succ, Nat.mul_comm] using covered

end RankChargedProductSystem
end V2
end SunflowerAASC
