import SunflowerAASC.V2.SelectedCoordinateReduction

namespace SunflowerAASC
namespace V2
namespace OutgoingCrossTower

open SelectedCoordinateReduction

/-- Every selected-coordinate residual step in the tower is cross-free. -/
noncomputable def CrossFreeTower
    {alpha : Type}
    [DecidableEq alpha] :
    (n : Nat) -> Concrete.UniformSetFamily alpha n -> Prop
  | 0, _ => True
  | n + 1, F =>
      Not (HasOutgoingCross F) ∧
        CrossFreeTower n (residualFamily F)

/-- A concrete outgoing cross occurs at some selected-coordinate rank. -/
noncomputable def HasOutgoingCrossInTower
    {alpha : Type}
    [DecidableEq alpha] :
    (n : Nat) -> Concrete.UniformSetFamily alpha n -> Prop
  | 0, _ => False
  | n + 1, F =>
      HasOutgoingCross F ∨
        HasOutgoingCrossInTower n (residualFamily F)

/-- A source-labelled finite witness locating an outgoing cross in the tower. -/
inductive OutgoingCrossTowerWitness
    {alpha : Type}
    [DecidableEq alpha] :
    (n : Nat) -> Concrete.UniformSetFamily alpha n -> Type
  | here
      {n : Nat}
      {F : Concrete.UniformSetFamily alpha (n + 1)}
      (cross : HasOutgoingCross F) :
      OutgoingCrossTowerWitness (n + 1) F
  | later
      {n : Nat}
      {F : Concrete.UniformSetFamily alpha (n + 1)}
      (tail : OutgoingCrossTowerWitness n (residualFamily F)) :
      OutgoingCrossTowerWitness (n + 1) F

/-- At one step, a negative endpoint either descends or realizes a cross. -/
theorem residualFamily_noSunflower_or_outgoingCross
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Not (Concrete.HasSunflower k (residualFamily F)) ∨
      HasOutgoingCross F := by
  by_cases residualNoSunflower :
      Not (Concrete.HasSunflower k (residualFamily F))
  · exact Or.inl residualNoSunflower
  · apply Or.inr
    exact outgoingCross_of_residualSunflower_of_noSunflower
      noSunflower (Classical.not_not.mp residualNoSunflower)

/-- A zero-uniform finite family contains at most the empty edge. -/
theorem rankZero_family_card_le_one
    {alpha : Type}
    [DecidableEq alpha]
    (F : Concrete.UniformSetFamily alpha 0) :
    F.edges.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro left left_mem right right_mem
  have left_empty : left = ∅ :=
    Finset.card_eq_zero.mp (F.uniform left left_mem)
  have right_empty : right = ∅ :=
    Finset.card_eq_zero.mp (F.uniform right right_mem)
  exact left_empty.trans right_empty.symm

/--
Cross-free selected-coordinate deletion gives a complete `Fin k` trace. The
proof is pure finite combinatorics: each residual fibre has size below `k`,
and absence of an outgoing cross keeps the residual family sunflower-free.
-/
theorem family_card_le_k_pow_rank_of_crossFreeTower
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (F : Concrete.UniformSetFamily alpha n)
    (noSunflower : Not (Concrete.HasSunflower k F))
    (crossFree : CrossFreeTower n F) :
    F.edges.card ≤ k ^ n := by
  induction n with
  | zero =>
      simpa using rankZero_family_card_le_one F
  | succ n ih =>
      change Not (HasOutgoingCross F) ∧
        CrossFreeTower n (residualFamily F) at crossFree
      rcases crossFree with ⟨noOutgoingCross, residualCrossFree⟩
      have residualNoSunflower :
          Not (Concrete.HasSunflower k (residualFamily F)) :=
        residualFamily_noSunflower_of_noOutgoingCross
          noSunflower noOutgoingCross
      calc
        F.edges.card ≤ k * (residualFamily F).edges.card :=
          family_card_le_k_mul_residualFamily F noSunflower
        _ ≤ k * k ^ n :=
          Nat.mul_le_mul_left k
            (ih (residualFamily F) residualNoSunflower residualCrossFree)
        _ = k ^ (n + 1) := by
          simp [pow_succ, Nat.mul_comm]

/-- Cross-free and cross-realized towers are exact complements. -/
theorem crossFreeTower_iff_not_hasOutgoingCrossInTower
    {alpha : Type}
    [DecidableEq alpha]
    (n : Nat)
    (F : Concrete.UniformSetFamily alpha n) :
    CrossFreeTower n F ↔ Not (HasOutgoingCrossInTower n F) := by
  induction n with
  | zero =>
      simp [CrossFreeTower, HasOutgoingCrossInTower]
  | succ n ih =>
      change
        (Not (HasOutgoingCross F) ∧
          CrossFreeTower n (residualFamily F)) ↔
        Not (HasOutgoingCross F ∨
          HasOutgoingCrossInTower n (residualFamily F))
      constructor
      · rintro ⟨noCross, tailCrossFree⟩ (cross | tailCross)
        · exact noCross cross
        · exact (ih (residualFamily F)).mp tailCrossFree tailCross
      · intro noCrossInTower
        exact
          ⟨fun cross => noCrossInTower (Or.inl cross),
            (ih (residualFamily F)).mpr
              (fun tailCross => noCrossInTower (Or.inr tailCross))⟩

/-- The recursive proposition is inhabited exactly by a concrete tower witness. -/
theorem nonempty_outgoingCrossTowerWitness_iff
    {alpha : Type}
    [DecidableEq alpha]
    (n : Nat)
    (F : Concrete.UniformSetFamily alpha n) :
    Nonempty (OutgoingCrossTowerWitness n F) ↔
      HasOutgoingCrossInTower n F := by
  induction n with
  | zero =>
      constructor
      · rintro ⟨witness⟩
        cases witness
      · intro impossible
        exact False.elim impossible
  | succ n ih =>
      constructor
      · rintro ⟨witness⟩
        cases witness with
        | here cross =>
            exact Or.inl cross
        | later tail =>
            exact Or.inr <| (ih (residualFamily F)).mp ⟨tail⟩
      · intro crossInTower
        rcases crossInTower with cross | tailCross
        · exact ⟨OutgoingCrossTowerWitness.here cross⟩
        · rcases (ih (residualFamily F)).mpr tailCross with ⟨tail⟩
          exact ⟨OutgoingCrossTowerWitness.later tail⟩

/--
Every sunflower-free family above the cross-free `k^n` capacity positively
realizes an outgoing-cross witness at some rank of the generated tower.
-/
theorem hasOutgoingCrossInTower_of_card_gt_k_pow_rank
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (F : Concrete.UniformSetFamily alpha n)
    (noSunflower : Not (Concrete.HasSunflower k F))
    (sizeExcess : k ^ n < F.edges.card) :
    HasOutgoingCrossInTower n F := by
  apply Classical.byContradiction
  intro noCrossInTower
  have crossFree : CrossFreeTower n F :=
    (crossFreeTower_iff_not_hasOutgoingCrossInTower n F).mpr
      noCrossInTower
  exact Nat.not_lt_of_ge
    (family_card_le_k_pow_rank_of_crossFreeTower
      F noSunflower crossFree) sizeExcess

/-- Any larger comparison base still forces the same outgoing-cross witness. -/
theorem hasOutgoingCrossInTower_of_card_gt_base_pow
    {alpha : Type}
    [DecidableEq alpha]
    {n k base : Nat}
    (F : Concrete.UniformSetFamily alpha n)
    (noSunflower : Not (Concrete.HasSunflower k F))
    (k_le_base : k ≤ base)
    (sizeExcess : base ^ n < F.edges.card) :
    HasOutgoingCrossInTower n F := by
  apply hasOutgoingCrossInTower_of_card_gt_k_pow_rank F noSunflower
  exact lt_of_le_of_lt (pow_le_pow_left' k_le_base n) sizeExcess

/-- Dense countercases populate an explicit finite outgoing-cross witness. -/
theorem outgoingCrossTowerWitness_nonempty_of_card_gt_base_pow
    {alpha : Type}
    [DecidableEq alpha]
    {n k base : Nat}
    (F : Concrete.UniformSetFamily alpha n)
    (noSunflower : Not (Concrete.HasSunflower k F))
    (k_le_base : k ≤ base)
    (sizeExcess : base ^ n < F.edges.card) :
    Nonempty (OutgoingCrossTowerWitness n F) := by
  exact (nonempty_outgoingCrossTowerWitness_iff n F).mpr
    (hasOutgoingCrossInTower_of_card_gt_base_pow
      F noSunflower k_le_base sizeExcess)

end OutgoingCrossTower
end V2
end SunflowerAASC
