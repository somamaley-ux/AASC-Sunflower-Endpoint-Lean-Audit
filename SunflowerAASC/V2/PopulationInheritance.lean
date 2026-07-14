import SunflowerAASC.V2.DenseCountercaseRange
import SunflowerAASC.V2.InternalTensorProfiles

namespace SunflowerAASC
namespace V2
namespace PopulationInheritance

open InternalTensorProfiles

/--
The common internal-profile reservoir inherited from a traditionally controlled
rank interval.  The Erdős-Rado blocker has at most `(k - 1) * n` coordinates at
rank `n`, so one cutoff gives a finite reservoir depending only on `k` and the
cutoff.
-/
def traditionalSeedTensorProfileBound (k cutoff : Nat) : Nat :=
  (k - 1) * cutoff

theorem traditionalSeedTensorProfileBound_positive
    {k cutoff : Nat}
    (k_nondegenerate : 3 <= k)
    (cutoff_positive : 0 < cutoff) :
    0 < traditionalSeedTensorProfileBound k cutoff := by
  simp only [traditionalSeedTensorProfileBound]
  exact Nat.mul_pos (by omega) cutoff_positive

/-- The checked traditional blocker bound supplies enough slots below a cutoff. -/
theorem minimalBlocker_card_le_traditionalSeed
    {alpha : Type}
    [DecidableEq alpha]
    {r k cutoff : Nat}
    (rankAtMost : r + 1 <= cutoff)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    (MinimalBlocker.minimalBlocker F).card <=
      traditionalSeedTensorProfileBound k cutoff := by
  calc
    (MinimalBlocker.minimalBlocker F).card <=
        (EffectiveBlocker.canonicalRawBlocker F).card :=
      Finset.card_le_card (MinimalBlocker.minimalBlocker_subset_raw F)
    _ <= (k - 1) * (r + 1) :=
      EffectiveBlocker.canonicalRawBlocker_card_le_erdosRado_rank_bound
        F noSunflower
    _ <= (k - 1) * cutoff := Nat.mul_le_mul_left (k - 1) rankAtMost

/-- A genuine finite labeling of every minimal blocker in the seed interval. -/
noncomputable def traditionalSeedProfileEmbedding
    {alpha : Type}
    [DecidableEq alpha]
    {r k cutoff : Nat}
    (rankAtMost : r + 1 <= cutoff)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ↪
      Fin (traditionalSeedTensorProfileBound k cutoff) :=
  (Fintype.equivFinOfCardEq
      (Fintype.card_coe (MinimalBlocker.minimalBlocker F))).toEmbedding.trans
    ⟨Fin.castLE
        (minimalBlocker_card_le_traditionalSeed
          rankAtMost F noSunflower),
      Fin.castLE_injective
        (minimalBlocker_card_le_traditionalSeed
          rankAtMost F noSunflower)⟩

/--
Non-vacuous population on the traditionally controlled ranks.  The internal
slot is an actual injective finite label, so a realized load is separated by
the inherited reservoir before any impossibility branch is invoked.
-/
noncomputable def traditionalSeedPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r k cutoff : Nat}
    (k_nondegenerate : 3 <= k)
    (cutoff_positive : 0 < cutoff)
    (rankAtMost : r + 1 <= cutoff)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := traditionalSeedTensorProfileBound k cutoff)
      noSunflower
      (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
        alpha k k_nondegenerate r) where
  tensorProfileBound_positive :=
    traditionalSeedTensorProfileBound_positive
      k_nondegenerate cutoff_positive
  constraintProfile := fun _ => ∅
  forcedRole := fun _ => .boundedFiber
  internalTensorProfileSlot :=
    traditionalSeedProfileEmbedding rankAtMost F noSunflower
  primeChangingTensorSplit := fun _ _ => False
  loadExhaustive := by
    intro left right _sameCell _sameProfile _sameRole load
    apply Or.inl
    intro sameSlot
    have sameWitness : left = right :=
      (traditionalSeedProfileEmbedding
        rankAtMost F noSunflower).injective sameSlot
    subst right
    exact load.rightNegative load.leftPositive
  primeChangingTensorSplitExcluded := fun _ _ impossible => impossible

/--
The remaining structural inheritance datum, restricted to dense countercases.
At rank `r + 1`, the step may use every already constructed
lower-rank dense population in the same fixed finite reservoir. Standing is
binary before this step. The required theorem is bounded population inheritance
for the live standing-bearing realizations after skin and the forbidden roles
are removed; it is not asserted by the seed construction.
-/
structure DenseRankDeletionPopulationInheritanceSource
    (alpha : Type)
    [DecidableEq alpha]
    (k cutoff : Nat)
    (k_nondegenerate : 3 <= k)
    (cutoff_positive : 0 < cutoff) where
  inheritFromLowerRanks :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      cutoff < r + 1 ->
      internalTensorConstraintBase k
          (traditionalSeedTensorProfileBound k cutoff) ^ (r + 1) <
        F.edges.card ->
      (forall s : Nat,
        s < r ->
        forall G : Concrete.UniformSetFamily alpha (s + 1),
        forall noSunflowerG : Not (Concrete.HasSunflower k G),
        internalTensorConstraintBase k
            (traditionalSeedTensorProfileBound k cutoff) ^ (s + 1) <
          G.edges.card ->
        BoundedPrivateWitnessLoadExhaustion
          (tensorProfileBound := traditionalSeedTensorProfileBound k cutoff)
          noSunflowerG
          (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
            alpha k k_nondegenerate s)) ->
      BoundedPrivateWitnessLoadExhaustion
        (tensorProfileBound := traditionalSeedTensorProfileBound k cutoff)
        noSunflower
        (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
          alpha k k_nondegenerate r)

/--
Strong induction combines genuine seed population with density-corrected
rank-deletion inheritance.
-/
noncomputable def DenseRankDeletionPopulationInheritanceSource.population
    {alpha : Type}
    [DecidableEq alpha]
    {k cutoff : Nat}
    {k_nondegenerate : 3 <= k}
    {cutoff_positive : 0 < cutoff}
    (Src : DenseRankDeletionPopulationInheritanceSource
      alpha k cutoff k_nondegenerate cutoff_positive)
    (r : Nat)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (sizeExcess :
      internalTensorConstraintBase k
          (traditionalSeedTensorProfileBound k cutoff) ^ (r + 1) <
        F.edges.card) :
    BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := traditionalSeedTensorProfileBound k cutoff)
      noSunflower
      (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
        alpha k k_nondegenerate r) := by
  let motive := fun r : Nat =>
    forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      internalTensorConstraintBase k
          (traditionalSeedTensorProfileBound k cutoff) ^ (r + 1) <
        F.edges.card ->
      BoundedPrivateWitnessLoadExhaustion
        (tensorProfileBound := traditionalSeedTensorProfileBound k cutoff)
        noSunflower
        (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
          alpha k k_nondegenerate r)
  refine (Nat.strongRecOn (motive := motive) r ?_)
    F noSunflower sizeExcess
  intro currentRank lowerPopulation F noSunflower sizeExcess
  by_cases rankAtMost : currentRank + 1 <= cutoff
  · exact traditionalSeedPopulation
      k_nondegenerate cutoff_positive rankAtMost F noSunflower
  · apply Src.inheritFromLowerRanks currentRank F noSunflower
      (Nat.lt_of_not_ge rankAtMost) sizeExcess
    intro s s_lt G noSunflowerG sizeExcessG
    exact lowerPopulation s s_lt G noSunflowerG sizeExcessG

noncomputable def
    DenseRankDeletionPopulationInheritanceSource.toDensePopulationSource
    {alpha : Type}
    [DecidableEq alpha]
    {k cutoff : Nat}
    {k_nondegenerate : 3 <= k}
    {cutoff_positive : 0 < cutoff}
    (Src : DenseRankDeletionPopulationInheritanceSource
      alpha k cutoff k_nondegenerate cutoff_positive) :
    DenseBoundedPrivateWitnessLoadSource
      alpha k (traditionalSeedTensorProfileBound k cutoff) k_nondegenerate where
  exhaust := by
    intro r F noSunflower sizeExcess
    exact Src.population r F noSunflower sizeExcess

/-- The seeded Mathlib-AASC pincer closes once bounded population inheritance is built. -/
theorem sunflower_of_seeded_rankDeletionPopulationInheritance
    {alpha : Type}
    [DecidableEq alpha]
    {n k cutoff : Nat}
    {k_nondegenerate : 3 <= k}
    {cutoff_positive : 0 < cutoff}
    (Src : DenseRankDeletionPopulationInheritanceSource
      alpha k cutoff k_nondegenerate cutoff_positive)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      internalTensorConstraintBase k
          (traditionalSeedTensorProfileBound k cutoff) ^ n <
        F.edges.card) :
    Concrete.HasSunflower k F := by
  exact sunflower_of_dense_boundedPrivateWitnessLoad
    Src.toDensePopulationSource F sizeExcess

/-- The verified traditional three-petal cutoff from the reflected bound. -/
def threePetalTraditionalCutoff : Nat := 2047

theorem threePetalTraditionalCutoff_controlled :
    (3 - 1) *
        DenseCountercaseRange.reflectedFactorialBase
          threePetalTraditionalCutoff <=
      ConstraintMapPopulation.corpusConstraintBase 3 := by
  simpa [threePetalTraditionalCutoff] using
    DenseCountercaseRange.rank_2047_is_erdosRado_reflected_controlled_for_three_petals

theorem threePetalTraditionalSeedTensorProfileBound_eq :
    traditionalSeedTensorProfileBound 3 threePetalTraditionalCutoff = 4094 := by
  decide

theorem threePetalTraditionalSeedConstraintBase_eq :
    internalTensorConstraintBase 3
        (traditionalSeedTensorProfileBound 3 threePetalTraditionalCutoff) =
      8384512 := by
  decide

/-- Largest rank reached by factor reflection under the seeded refined base. -/
def threePetalSeedReflectedCutoff : Nat := 8384511

theorem threePetalSeedReflectedCutoff_controlled :
    (3 - 1) * DenseCountercaseRange.reflectedFactorialBase
        threePetalSeedReflectedCutoff <=
      internalTensorConstraintBase 3
        (traditionalSeedTensorProfileBound
          3 threePetalTraditionalCutoff) := by
  decide

/--
The seeded base itself gives an unconditional traditional bound through rank
`8384511`; no AASC population inheritance is used in this interval.
-/
theorem threePetal_family_card_le_seedBase_pow
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (rankAtMost : n <= threePetalSeedReflectedCutoff)
    (F : Concrete.UniformSetFamily alpha n)
    (noSunflower : Not (Concrete.HasSunflower 3 F)) :
    F.edges.card <=
      internalTensorConstraintBase 3
        (traditionalSeedTensorProfileBound
          3 threePetalTraditionalCutoff) ^ n := by
  refine DenseCountercaseRange.family_card_le_base_pow_of_reflectedFactorialRange
      (k := 3) (F := F) ?_ noSunflower
  rw [threePetalTraditionalSeedConstraintBase_eq]
  change 2 * ((n + 2) / 2) <= 8384512
  have reflected_mono :
      (n + 2) / 2 <= (threePetalSeedReflectedCutoff + 2) / 2 :=
    Nat.div_le_div_right (Nat.add_le_add_right rankAtMost 2)
  calc
    2 * ((n + 2) / 2) <=
        2 * ((threePetalSeedReflectedCutoff + 2) / 2) :=
      Nat.mul_le_mul_left 2 reflected_mono
    _ = 8384512 := by decide

theorem no_threePetal_denseCountercase_through_seedReflectedCutoff
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (rankAtMost : n <= threePetalSeedReflectedCutoff)
    (F : Concrete.UniformSetFamily alpha n)
    (noSunflower : Not (Concrete.HasSunflower 3 F)) :
    Not (
      internalTensorConstraintBase 3
          (traditionalSeedTensorProfileBound
            3 threePetalTraditionalCutoff) ^ n <
        F.edges.card) := by
  exact Nat.not_lt_of_ge <|
    threePetal_family_card_le_seedBase_pow
      rankAtMost F noSunflower

/--
After the seed and reflected-factorial ranges are discharged, inheritance is
needed only strictly above rank `8384511`.
-/
structure ThreePetalHighRankPopulationInheritanceSource
    (alpha : Type)
    [DecidableEq alpha] where
  inheritAboveReflectedCutoff :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower 3 F),
      threePetalSeedReflectedCutoff < r + 1 ->
      internalTensorConstraintBase 3
          (traditionalSeedTensorProfileBound
            3 threePetalTraditionalCutoff) ^ (r + 1) <
        F.edges.card ->
      (forall s : Nat,
        s < r ->
        forall G : Concrete.UniformSetFamily alpha (s + 1),
        forall noSunflowerG : Not (Concrete.HasSunflower 3 G),
        internalTensorConstraintBase 3
            (traditionalSeedTensorProfileBound
              3 threePetalTraditionalCutoff) ^ (s + 1) <
          G.edges.card ->
        BoundedPrivateWitnessLoadExhaustion
          (tensorProfileBound := traditionalSeedTensorProfileBound
            3 threePetalTraditionalCutoff)
          noSunflowerG
          (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
            alpha 3 (by decide) s)) ->
      BoundedPrivateWitnessLoadExhaustion
        (tensorProfileBound := traditionalSeedTensorProfileBound
          3 threePetalTraditionalCutoff)
        noSunflower
        (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
          alpha 3 (by decide) r)

/-- The corrected seeded three-petal closeout now has one structural source item. -/
inductive ThreePetalSeededClosureObligation where
  | highRankBoundedAASCTypePopulation
deriving DecidableEq, Repr

def threePetalSeededClosureObligations :
    List ThreePetalSeededClosureObligation :=
  [.highRankBoundedAASCTypePopulation]

theorem threePetalSeededClosureObligationCount_eq :
    threePetalSeededClosureObligations.length = 1 := by
  rfl

/--
Strong induction uses concrete population through rank `2047`, eliminates the
middle interval through rank `8384511`, and invokes the source only above it.
-/
noncomputable def ThreePetalHighRankPopulationInheritanceSource.population
    {alpha : Type}
    [DecidableEq alpha]
    (Src : ThreePetalHighRankPopulationInheritanceSource alpha)
    (r : Nat)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower 3 F))
    (sizeExcess :
      internalTensorConstraintBase 3
          (traditionalSeedTensorProfileBound
            3 threePetalTraditionalCutoff) ^ (r + 1) <
        F.edges.card) :
    BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := traditionalSeedTensorProfileBound
        3 threePetalTraditionalCutoff)
      noSunflower
      (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
        alpha 3 (by decide) r) := by
  let motive := fun r : Nat =>
    forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower 3 F),
      internalTensorConstraintBase 3
          (traditionalSeedTensorProfileBound
            3 threePetalTraditionalCutoff) ^ (r + 1) <
        F.edges.card ->
      BoundedPrivateWitnessLoadExhaustion
        (tensorProfileBound := traditionalSeedTensorProfileBound
          3 threePetalTraditionalCutoff)
        noSunflower
        (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
          alpha 3 (by decide) r)
  refine (Nat.strongRecOn (motive := motive) r ?_)
    F noSunflower sizeExcess
  intro currentRank lowerPopulation F noSunflower sizeExcess
  by_cases seedRank : currentRank + 1 <= threePetalTraditionalCutoff
  · exact traditionalSeedPopulation
      (by decide) (by decide) seedRank F noSunflower
  by_cases reflectedRank :
      currentRank + 1 <= threePetalSeedReflectedCutoff
  · exact False.elim <|
      no_threePetal_denseCountercase_through_seedReflectedCutoff
        reflectedRank F noSunflower sizeExcess
  · apply Src.inheritAboveReflectedCutoff
      currentRank F noSunflower
      (Nat.lt_of_not_ge reflectedRank) sizeExcess
    intro s s_lt G noSunflowerG sizeExcessG
    exact lowerPopulation s s_lt G noSunflowerG sizeExcessG

noncomputable def
    ThreePetalHighRankPopulationInheritanceSource.toDensePopulationSource
    {alpha : Type}
    [DecidableEq alpha]
    (Src : ThreePetalHighRankPopulationInheritanceSource alpha) :
    DenseBoundedPrivateWitnessLoadSource alpha 3
      (traditionalSeedTensorProfileBound
        3 threePetalTraditionalCutoff) (by decide) where
  exhaust := by
    intro r F noSunflower sizeExcess
    exact Src.population r F noSunflower sizeExcess

/-- The three-petal endpoint now depends only on inheritance above rank 8384511. -/
theorem sunflower_of_threePetalHighRankPopulationInheritance
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (Src : ThreePetalHighRankPopulationInheritanceSource alpha)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      internalTensorConstraintBase 3
          (traditionalSeedTensorProfileBound
            3 threePetalTraditionalCutoff) ^ n <
        F.edges.card) :
    Concrete.HasSunflower 3 F := by
  exact sunflower_of_dense_boundedPrivateWitnessLoad
    Src.toDensePopulationSource F sizeExcess

end PopulationInheritance
end V2
end SunflowerAASC
