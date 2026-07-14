import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import SunflowerAASC.V2.ConstraintMapPopulation

namespace SunflowerAASC
namespace V2
namespace DenseCountercaseRange

open scoped BigOperators

/-- A balanced-product base for the factorial, asymptotic to `3 * n / 4`. -/
def pairedFactorialBase (n : Nat) : Nat :=
  (3 * ((n + 1) / 2) + 1) / 2

private theorem three_mul_le_twice_pairedBase (a : Nat) :
    3 * a <= 2 * ((3 * a + 1) / 2) := by
  omega

private theorem twice_sq_le_pairedBase_sq (a : Nat) :
    2 * a * a <= ((3 * a + 1) / 2) * ((3 * a + 1) / 2) := by
  have halfBound := three_mul_le_twice_pairedBase a
  nlinarith

/-- Split off the upper `d` factorial factors and bound each by `a + d`. -/
theorem factorial_add_le_pow_mul_factorial (a d : Nat) :
    (a + d).factorial <= (a + d) ^ d * a.factorial := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show a + (d + 1) = (a + d) + 1 by omega,
        Nat.factorial_succ]
      calc
        (a + d + 1) * (a + d).factorial <=
            (a + d + 1) * ((a + d) ^ d * a.factorial) :=
          Nat.mul_le_mul_left _ ih
        _ <= (a + d + 1) * ((a + d + 1) ^ d * a.factorial) := by
          exact Nat.mul_le_mul_left _ <|
            Nat.mul_le_mul_right _ <|
              Nat.pow_le_pow_left (by omega) d
        _ = (a + (d + 1)) ^ (d + 1) * a.factorial := by
          rw [Nat.pow_succ]
          ring

/-- A balanced Mathlib factorial bound improving `n! <= n^n`. -/
theorem factorial_le_pairedFactorialBase_pow (n : Nat) :
    n.factorial <= pairedFactorialBase n ^ n := by
  let a := (n + 1) / 2
  let d := n - a
  let b := (3 * a + 1) / 2
  have a_add_d : a + d = n := by
    dsimp [a, d]
    omega
  have d_le_a : d <= a := by
    dsimp [a, d]
    omega
  have n_le_two_a : n <= 2 * a := by
    dsimp [a]
    omega
  have a_le_b : a <= b := by
    dsimp [b]
    omega
  have na_le_bsq : n * a <= b * b := by
    have squareBound := twice_sq_le_pairedBase_sq a
    change 2 * a * a <= b * b at squareBound
    calc
      n * a <= (2 * a) * a := Nat.mul_le_mul_right a n_le_two_a
      _ = 2 * a * a := by ring
      _ <= b * b := squareBound
  calc
    n.factorial = (a + d).factorial := by rw [a_add_d]
    _ <= (a + d) ^ d * a.factorial :=
      factorial_add_le_pow_mul_factorial a d
    _ <= n ^ d * a ^ a := by
      rw [a_add_d]
      gcongr
      exact a.factorial_le_pow
    _ = n ^ d * (a ^ d * a ^ (a - d)) := by
      congr 1
      rw [← pow_add, Nat.add_sub_of_le d_le_a]
    _ = (n * a) ^ d * a ^ (a - d) := by
      rw [Nat.mul_pow, Nat.mul_assoc]
    _ <= (b * b) ^ d * b ^ (a - d) := by
      gcongr
    _ = b ^ (a + d) := by
      rw [Nat.mul_pow, ← pow_add, ← pow_add]
      congr 1
      omega
    _ = pairedFactorialBase n ^ n := by
      rw [a_add_d]
      rfl

/-- The symmetric lower/upper-factor pairing base, asymptotic to `n / 2`. -/
def reflectedFactorialBase (n : Nat) : Nat :=
  (n + 2) / 2

private theorem factorial_two_mul_le_reflectedBase (m : Nat) :
    (2 * m).factorial <= (m + 1) ^ (2 * m) := by
  calc
    (2 * m).factorial = (m + m).factorial := by congr 1; omega
    _ = m.factorial * (m + 1).ascFactorial m :=
      (Nat.factorial_mul_ascFactorial m m).symm
    _ <= (m + 1) ^ (2 * m) := by
      rw [Nat.factorial_eq_prod_range_add_one, Nat.ascFactorial_eq_prod_range]
      have hreflect :
          (∏ i ∈ Finset.range m, (m + 1 + i)) =
            ∏ i ∈ Finset.range m, (m + 1 + (m - 1 - i)) := by
        exact (Finset.prod_range_reflect (fun i => m + 1 + i) m).symm
      rw [hreflect, ← Finset.prod_mul_distrib]
      calc
        (∏ i ∈ Finset.range m, (i + 1) * (m + 1 + (m - 1 - i))) <=
            ∏ _i ∈ Finset.range m, (m + 1) * (m + 1) := by
          apply Finset.prod_le_prod'
          intro i hi
          have hi' : i < m := Finset.mem_range.mp hi
          have hsum :
              (i + 1) + (m + 1 + (m - 1 - i)) = 2 * m + 1 := by
            omega
          nlinarith [Nat.zero_le (m + 1 - (i + 1))]
        _ = ((m + 1) * (m + 1)) ^ m := by simp
        _ = (m + 1) ^ (2 * m) := by
          rw [Nat.mul_pow, ← pow_add]
          congr 1
          omega

private theorem factorial_two_mul_add_one_le_reflectedBase (m : Nat) :
    (2 * m + 1).factorial <= (m + 1) ^ (2 * m + 1) := by
  have inner :
      m.factorial * (m + 2).ascFactorial m <=
        (m + 1) ^ (2 * m) := by
    rw [Nat.factorial_eq_prod_range_add_one, Nat.ascFactorial_eq_prod_range]
    have hreflect :
        (∏ i ∈ Finset.range m, (m + 2 + i)) =
          ∏ i ∈ Finset.range m, (m + 2 + (m - 1 - i)) := by
      exact (Finset.prod_range_reflect (fun i => m + 2 + i) m).symm
    rw [hreflect, ← Finset.prod_mul_distrib]
    calc
      (∏ i ∈ Finset.range m, (i + 1) * (m + 2 + (m - 1 - i))) <=
          ∏ _i ∈ Finset.range m, (m + 1) * (m + 1) := by
        apply Finset.prod_le_prod'
        intro i hi
        have hi' : i < m := Finset.mem_range.mp hi
        have hsum :
            (i + 1) + (m + 2 + (m - 1 - i)) = 2 * (m + 1) := by
          omega
        nlinarith [Nat.zero_le (m + 1 - (i + 1))]
      _ = ((m + 1) * (m + 1)) ^ m := by simp
      _ = (m + 1) ^ (2 * m) := by
        rw [Nat.mul_pow, ← pow_add]
        congr 1
        omega
  calc
    (2 * m + 1).factorial = (m + 1 + m).factorial := by congr 1; omega
    _ = (m + 1).factorial * (m + 2).ascFactorial m :=
      (Nat.factorial_mul_ascFactorial (m + 1) m).symm
    _ = (m + 1) * (m.factorial * (m + 2).ascFactorial m) := by
      rw [Nat.factorial_succ]
      ring
    _ <= (m + 1) * (m + 1) ^ (2 * m) := Nat.mul_le_mul_left _ inner
    _ = (m + 1) ^ (2 * m + 1) := by rw [pow_succ']

/-- Symmetric factor reflection gives `n! <= ceil((n + 1) / 2)^n`. -/
theorem factorial_le_reflectedFactorialBase_pow (n : Nat) :
    n.factorial <= reflectedFactorialBase n ^ n := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [show reflectedFactorialBase (2 * m) = m + 1 by
      simp [reflectedFactorialBase]]
    exact factorial_two_mul_le_reflectedBase m
  · rw [show reflectedFactorialBase (2 * m + 1) = m + 1 by
      simp [reflectedFactorialBase]
      omega]
    exact factorial_two_mul_add_one_le_reflectedBase m

/-- The factorial estimate is below the corpus constant-base estimate here. -/
theorem family_card_le_corpusBase_pow_of_k_mul_rank_le
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (rankRange : k * n <= ConstraintMapPopulation.corpusConstraintBase k)
    (F : Concrete.UniformSetFamily alpha n)
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    F.edges.card <= ConstraintMapPopulation.corpusConstraintBase k ^ n := by
  calc
    F.edges.card <= k ^ n * n.factorial :=
      EffectiveBlocker.family_card_le_classicalFactorial n F noSunflower
    _ <= k ^ n * n ^ n :=
      Nat.mul_le_mul_left (k ^ n) n.factorial_le_pow
    _ = (k * n) ^ n := by rw [Nat.mul_pow]
    _ <= ConstraintMapPopulation.corpusConstraintBase k ^ n :=
      Nat.pow_le_pow_left rankRange n

theorem no_denseCountercase_of_k_mul_rank_le
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (rankRange : k * n <= ConstraintMapPopulation.corpusConstraintBase k)
    (F : Concrete.UniformSetFamily alpha n)
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Not (ConstraintMapPopulation.corpusConstraintBase k ^ n < F.edges.card) := by
  exact Nat.not_lt_of_ge <|
    family_card_le_corpusBase_pow_of_k_mul_rank_le rankRange F noSunflower

/-- The sharpened factorial estimate is below the corpus base in this range. -/
theorem family_card_le_corpusBase_pow_of_pairedFactorialRange
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (rankRange :
      k * pairedFactorialBase n <=
        ConstraintMapPopulation.corpusConstraintBase k)
    (F : Concrete.UniformSetFamily alpha n)
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    F.edges.card <= ConstraintMapPopulation.corpusConstraintBase k ^ n := by
  calc
    F.edges.card <= k ^ n * n.factorial :=
      EffectiveBlocker.family_card_le_classicalFactorial n F noSunflower
    _ <= k ^ n * pairedFactorialBase n ^ n :=
      Nat.mul_le_mul_left (k ^ n) (factorial_le_pairedFactorialBase_pow n)
    _ = (k * pairedFactorialBase n) ^ n := by rw [Nat.mul_pow]
    _ <= ConstraintMapPopulation.corpusConstraintBase k ^ n :=
      Nat.pow_le_pow_left rankRange n

theorem no_denseCountercase_of_pairedFactorialRange
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (rankRange :
      k * pairedFactorialBase n <=
        ConstraintMapPopulation.corpusConstraintBase k)
    (F : Concrete.UniformSetFamily alpha n)
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Not (ConstraintMapPopulation.corpusConstraintBase k ^ n < F.edges.card) := by
  exact Nat.not_lt_of_ge <|
    family_card_le_corpusBase_pow_of_pairedFactorialRange
      rankRange F noSunflower

/-- The reflected-factorial estimate is below any target base in this range. -/
theorem family_card_le_base_pow_of_reflectedFactorialRange
    {alpha : Type}
    [DecidableEq alpha]
    {n k base : Nat}
    (rankRange :
      (k - 1) * reflectedFactorialBase n <=
        base)
    (F : Concrete.UniformSetFamily alpha n)
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    F.edges.card <= base ^ n := by
  calc
    F.edges.card <= (k - 1) ^ n * n.factorial :=
      EffectiveBlocker.family_card_le_erdosRadoFactorial n F noSunflower
    _ <= (k - 1) ^ n * reflectedFactorialBase n ^ n :=
      Nat.mul_le_mul_left ((k - 1) ^ n)
        (factorial_le_reflectedFactorialBase_pow n)
    _ = ((k - 1) * reflectedFactorialBase n) ^ n := by rw [Nat.mul_pow]
    _ <= base ^ n :=
      Nat.pow_le_pow_left rankRange n

/-- The reflected-factorial estimate is below the corpus base in this range. -/
theorem family_card_le_corpusBase_pow_of_reflectedFactorialRange
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (rankRange :
      (k - 1) * reflectedFactorialBase n <=
        ConstraintMapPopulation.corpusConstraintBase k)
    (F : Concrete.UniformSetFamily alpha n)
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    F.edges.card <= ConstraintMapPopulation.corpusConstraintBase k ^ n := by
  exact family_card_le_base_pow_of_reflectedFactorialRange
    rankRange F noSunflower

theorem no_denseCountercase_of_reflectedFactorialRange
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (rankRange :
      (k - 1) * reflectedFactorialBase n <=
        ConstraintMapPopulation.corpusConstraintBase k)
    (F : Concrete.UniformSetFamily alpha n)
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Not (ConstraintMapPopulation.corpusConstraintBase k ^ n < F.edges.card) := by
  exact Nat.not_lt_of_ge <|
    family_card_le_corpusBase_pow_of_reflectedFactorialRange
      rankRange F noSunflower

/--
In the factorially controlled rank range, the dense source is populated by
eliminating the impossible countercase before AASC role exhaustion is needed.
-/
def privateWitnessFactorization_of_k_mul_rank_le
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (rankRange :
      k * (r + 1) <= ConstraintMapPopulation.corpusConstraintBase k)
    (noSunflower : Not (Concrete.HasSunflower k F))
    (sizeExcess :
      ConstraintMapPopulation.corpusConstraintBase k ^ (r + 1) <
        F.edges.card) :
    ConstraintMapPopulation.PrivateWitnessConstraintFactorization
      noSunflower := by
  exact False.elim <|
    no_denseCountercase_of_k_mul_rank_le
      rankRange F noSunflower sizeExcess

def privateWitnessFactorization_of_pairedFactorialRange
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (rankRange :
      k * pairedFactorialBase (r + 1) <=
        ConstraintMapPopulation.corpusConstraintBase k)
    (noSunflower : Not (Concrete.HasSunflower k F))
    (sizeExcess :
      ConstraintMapPopulation.corpusConstraintBase k ^ (r + 1) <
        F.edges.card) :
    ConstraintMapPopulation.PrivateWitnessConstraintFactorization
      noSunflower := by
  exact False.elim <|
    no_denseCountercase_of_pairedFactorialRange
      rankRange F noSunflower sizeExcess

def privateWitnessFactorization_of_reflectedFactorialRange
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (rankRange :
      (k - 1) * reflectedFactorialBase (r + 1) <=
        ConstraintMapPopulation.corpusConstraintBase k)
    (noSunflower : Not (Concrete.HasSunflower k F))
    (sizeExcess :
      ConstraintMapPopulation.corpusConstraintBase k ^ (r + 1) <
        F.edges.card) :
    ConstraintMapPopulation.PrivateWitnessConstraintFactorization
      noSunflower := by
  exact False.elim <|
    no_denseCountercase_of_reflectedFactorialRange
      rankRange F noSunflower sizeExcess

theorem rank_682_is_factorially_controlled_for_three_petals :
    3 * 682 <= ConstraintMapPopulation.corpusConstraintBase 3 := by
  decide

theorem rank_908_is_paired_factorially_controlled_for_three_petals :
    3 * pairedFactorialBase 908 <=
      ConstraintMapPopulation.corpusConstraintBase 3 := by
  decide

theorem rank_1363_is_k_coefficient_reflected_controlled_for_three_petals :
    3 * reflectedFactorialBase 1363 <=
      ConstraintMapPopulation.corpusConstraintBase 3 := by
  decide

theorem rank_1364_is_not_k_coefficient_reflected_controlled_for_three_petals :
    Not (3 * reflectedFactorialBase 1364 <=
      ConstraintMapPopulation.corpusConstraintBase 3) := by
  decide

theorem rank_2047_is_erdosRado_reflected_controlled_for_three_petals :
    (3 - 1) * reflectedFactorialBase 2047 <=
      ConstraintMapPopulation.corpusConstraintBase 3 := by
  decide

theorem rank_2048_is_not_erdosRado_reflected_controlled_for_three_petals :
    Not ((3 - 1) * reflectedFactorialBase 2048 <=
      ConstraintMapPopulation.corpusConstraintBase 3) := by
  decide

/-- The genuinely AASC-facing remainder after factorial range elimination. -/
structure LargeRankConstraintFactorizationSource
    (alpha : Type)
    [DecidableEq alpha]
    (k : Nat)
    (k_nondegenerate : 3 <= k) where
  factorize :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      forall _sizeExcess :
        ConstraintMapPopulation.corpusConstraintBase k ^ (r + 1) <
          F.edges.card,
      ConstraintMapPopulation.corpusConstraintBase k <
          (k - 1) * reflectedFactorialBase (r + 1) ->
        ConstraintMapPopulation.PrivateWitnessConstraintFactorization
          noSunflower

/-- Large-rank source stated in the native AASC population language. -/
structure LargeRankConstraintPopulationSource
    (alpha : Type)
    [DecidableEq alpha]
    (k : Nat)
    (k_nondegenerate : 3 <= k) where
  populate :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      forall _sizeExcess :
        ConstraintMapPopulation.corpusConstraintBase k ^ (r + 1) <
          F.edges.card,
      ConstraintMapPopulation.corpusConstraintBase k <
          (k - 1) * reflectedFactorialBase (r + 1) ->
        ConstraintMapPopulation.KernelFirstPrivateWitnessConstraintPopulation
          noSunflower
          (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
            alpha k k_nondegenerate r)

def LargeRankConstraintPopulationSource.toFactorizationSource
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : LargeRankConstraintPopulationSource
      alpha k k_nondegenerate) :
    LargeRankConstraintFactorizationSource alpha k k_nondegenerate where
  factorize := by
    intro r F noSunflower sizeExcess largeRank
    exact (Src.populate r F noSunflower sizeExcess largeRank).toFactorization

def LargeRankConstraintFactorizationSource.toDenseCountercaseSource
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : LargeRankConstraintFactorizationSource
      alpha k k_nondegenerate) :
    ConstraintMapPopulation.DenseCountercaseConstraintFactorizationSource
      alpha k k_nondegenerate where
  factorize := by
    intro r F noSunflower sizeExcess
    by_cases factorialRange :
        (k - 1) * reflectedFactorialBase (r + 1) <=
          ConstraintMapPopulation.corpusConstraintBase k
    · exact privateWitnessFactorization_of_reflectedFactorialRange
        factorialRange noSunflower sizeExcess
    · exact Src.factorize r F noSunflower sizeExcess
        (Nat.lt_of_not_ge factorialRange)

theorem sunflower_of_largeRankConstraintFactorization
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : LargeRankConstraintFactorizationSource
      alpha k k_nondegenerate)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      ConstraintMapPopulation.corpusConstraintBase k ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  exact ConstraintMapPopulation.sunflower_of_dense_constraintMapFactorization
    Src.toDenseCountercaseSource F sizeExcess

theorem sunflower_of_largeRankConstraintPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : LargeRankConstraintPopulationSource
      alpha k k_nondegenerate)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      ConstraintMapPopulation.corpusConstraintBase k ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  exact sunflower_of_largeRankConstraintFactorization
    Src.toFactorizationSource F sizeExcess

/-- The unconditional constant-base endpoint over one fixed ground type. -/
def CorpusBaseEndpointBound
    (alpha : Type)
    [DecidableEq alpha]
    (k : Nat) : Prop :=
  forall n : Nat,
    forall F : Concrete.UniformSetFamily alpha n,
      Not (Concrete.HasSunflower k F) ->
        F.edges.card <= ConstraintMapPopulation.corpusConstraintBase k ^ n

/-- A populated large-rank source proves the full constant-base endpoint. -/
theorem LargeRankConstraintPopulationSource.provesEndpointBound
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : LargeRankConstraintPopulationSource
      alpha k k_nondegenerate) :
    CorpusBaseEndpointBound alpha k := by
  intro n F noSunflower
  exact Nat.le_of_not_gt <| fun sizeExcess =>
    noSunflower <| sunflower_of_largeRankConstraintPopulation
      Src F sizeExcess

/--
Conversely, the endpoint bound can populate the large-rank source only
vacuously, because every requested dense countercase is already impossible.
This direction is useful as an audit: the source must not be presented as a
weaker theorem than the endpoint it closes.
-/
def CorpusBaseEndpointBound.toLargeRankConstraintPopulationSource
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k}
    (Bound : CorpusBaseEndpointBound alpha k) :
    LargeRankConstraintPopulationSource alpha k k_nondegenerate where
  populate := by
    intro r F noSunflower sizeExcess _largeRank
    exact False.elim <| Nat.not_lt_of_ge
      (Bound (r + 1) F noSunflower) sizeExcess

/--
The remaining population source is logically equivalent to the desired
constant-base sunflower bound. Kernel necessity, role exhaustion, and global
skin finality do not inhabit it without an additional finite-type theorem.
-/
theorem nonempty_largeRankConstraintPopulationSource_iff_endpointBound
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k} :
    Nonempty (LargeRankConstraintPopulationSource
      alpha k k_nondegenerate) <->
      CorpusBaseEndpointBound alpha k := by
  constructor
  case mp =>
    intro Source
    exact Source.some.provesEndpointBound
  case mpr =>
    intro Bound
    exact Nonempty.intro Bound.toLargeRankConstraintPopulationSource

end DenseCountercaseRange
end V2
end SunflowerAASC
