import SunflowerAASC.V2.PopulationInheritance

namespace SunflowerAASC
namespace V2
namespace HighRankPopulationInheritance

open ConstraintMapPopulation
open InternalTensorProfiles
open PopulationInheritance

/-- Every fibre of a finite classifier fits in one fixed local alphabet. -/
def FiniteFiberBound
    {A C : Type}
    [Fintype A]
    [DecidableEq C]
    (classify : A -> C)
    (bound : Nat) : Prop :=
  forall c : C, Fintype.card {a : A // classify a = c} <= bound

/-- A local code that is injective after the inherited class is fixed. -/
structure FiberwiseFiniteCode
    {A C : Type}
    (classify : A -> C)
    (bound : Nat) where
  code : A -> Fin bound
  sameClassSameCodeFinal :
    forall left right : A,
      classify left = classify right ->
      code left = code right ->
      left = right

noncomputable def fiberEmbedding
    {A C : Type}
    [Fintype A]
    [DecidableEq C]
    {classify : A -> C}
    {bound : Nat}
    (Bound : FiniteFiberBound classify bound)
    (c : C) :
    {a : A // classify a = c} ↪ Fin bound :=
  (Fintype.equivFin {a : A // classify a = c}).toEmbedding.trans
    ⟨Fin.castLE (Bound c), Fin.castLE_injective (Bound c)⟩

/-- Package all fibre embeddings into one coherent sigma embedding. -/
noncomputable def fiberSigmaEmbedding
    {A C : Type}
    [Fintype A]
    [DecidableEq C]
    {classify : A -> C}
    {bound : Nat}
    (Bound : FiniteFiberBound classify bound) :
    (Sigma fun c : C => {a : A // classify a = c}) ↪ C × Fin bound where
  toFun state := (state.1, fiberEmbedding Bound state.1 state.2)
  inj' := by
    intro left right same
    rcases left with ⟨leftClass, left⟩
    rcases right with ⟨rightClass, right⟩
    have sameClass : leftClass = rightClass := congrArg Prod.fst same
    subst rightClass
    have sameFiber : left = right := by
      apply (fiberEmbedding Bound leftClass).injective
      exact congrArg Prod.snd same
    subst right
    rfl

/-- Fibre cardinality is constructive population data for a local code. -/
noncomputable def FiberwiseFiniteCode.ofFiniteFiberBound
    {A C : Type}
    [Fintype A]
    [DecidableEq C]
    {classify : A -> C}
    {bound : Nat}
    (Bound : FiniteFiberBound classify bound) :
    FiberwiseFiniteCode classify bound where
  code := fun a =>
    (fiberSigmaEmbedding Bound ⟨classify a, ⟨a, rfl⟩⟩).2
  sameClassSameCodeFinal := by
    intro left right sameClass sameCode
    have samePair :
        fiberSigmaEmbedding Bound ⟨classify left, ⟨left, rfl⟩⟩ =
          fiberSigmaEmbedding Bound ⟨classify right, ⟨right, rfl⟩⟩ := by
      apply Prod.ext
      · exact sameClass
      · exact sameCode
    have sameSigma := (fiberSigmaEmbedding Bound).injective samePair
    exact congrArg (fun state => state.2.val) sameSigma

/-- A fibrewise code gives the corresponding cardinal bound. -/
theorem FiberwiseFiniteCode.finiteFiberBound
    {A C : Type}
    [Fintype A]
    [DecidableEq C]
    {classify : A -> C}
    {bound : Nat}
    (Code : FiberwiseFiniteCode classify bound) :
    FiniteFiberBound classify bound := by
  intro c
  let localCode : {a : A // classify a = c} -> Fin bound :=
    fun a => Code.code a.val
  have localCode_injective : Function.Injective localCode := by
    intro left right sameCode
    apply Subtype.ext
    exact Code.sameClassSameCodeFinal left.val right.val
      (left.property.trans right.property.symm) sameCode
  simpa using Fintype.card_le_of_injective
    localCode localCode_injective

/-- Finite fibre cardinality and coherent local coding have identical content. -/
theorem nonempty_fiberwiseFiniteCode_iff_finiteFiberBound
    {A C : Type}
    [Fintype A]
    [DecidableEq C]
    {classify : A -> C}
    {bound : Nat} :
    Nonempty (FiberwiseFiniteCode classify bound) <->
      FiniteFiberBound classify bound := by
  constructor
  · intro Code
    exact Code.some.finiteFiberBound
  · intro Bound
    exact ⟨FiberwiseFiniteCode.ofFiniteFiberBound Bound⟩

/-- The inherited support class of one minimal private-witness coordinate. -/
noncomputable def minimalBlockerSupportClass
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    {x // x ∈ MinimalBlocker.minimalBlocker F} -> Finset (Fin k) :=
  fun x =>
    BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
      ⟨x.val, MinimalBlocker.minimalBlocker_subset_raw F x.property⟩

/--
The concrete population inequality: after the inherited support cell is fixed,
the surviving private witnesses fit in the refined identity alphabet.
-/
def CanonicalSupportFiberBound
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) : Prop :=
  FiniteFiberBound
    (minimalBlockerSupportClass F noSunflower)
    (refinedConstraintSignatureSize tensorProfileBound)

/-- The exact within-support identity capacity in the seeded three-petal case. -/
def threePetalRefinedIdentityFiberBound : Nat :=
  refinedConstraintSignatureSize
    (traditionalSeedTensorProfileBound 3 threePetalTraditionalCutoff)

theorem threePetalRefinedIdentityFiberBound_eq :
    threePetalRefinedIdentityFiberBound = 1048064 := by
  decide

/-- A support-fibre bound mechanically populates the bounded identity object. -/
noncomputable def boundedLoadExhaustionOfCanonicalSupportFiberBound
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (tensorProfileBound_positive : 0 < tensorProfileBound)
    (Bound : CanonicalSupportFiberBound
      (tensorProfileBound := tensorProfileBound) F noSunflower) :
    BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := tensorProfileBound) noSunflower corpus := by
  let Code : FiberwiseFiniteCode
      (minimalBlockerSupportClass F noSunflower)
      (refinedConstraintSignatureSize tensorProfileBound) :=
    FiberwiseFiniteCode.ofFiniteFiberBound Bound
  let identityOf := fun x : {x // x ∈ MinimalBlocker.minimalBlocker F} =>
    (refinedConstraintSignatureEquivFin tensorProfileBound).symm
      (Code.code x)
  exact {
    tensorProfileBound_positive := tensorProfileBound_positive
    constraintProfile := fun x => (identityOf x).1.1
    forcedRole := fun x => (identityOf x).1.2
    internalTensorProfileSlot := fun x => (identityOf x).2
    primeChangingTensorSplit := fun _ _ => False
    loadExhaustive := by
      intro left right sameCell sameProfile sameRole load
      apply Or.inl
      intro sameSlot
      have sameIdentity : identityOf left = identityOf right := by
        apply Prod.ext
        · apply Prod.ext
          · exact sameProfile
          · exact sameRole
        · exact sameSlot
      have sameCode : Code.code left = Code.code right := by
        apply (refinedConstraintSignatureEquivFin
          tensorProfileBound).symm.injective
        exact sameIdentity
      have sameWitness := Code.sameClassSameCodeFinal
        left right sameCell sameCode
      subst right
      exact load.rightNegative load.leftPositive
    primeChangingTensorSplitExcluded := fun _ _ impossible => impossible }

/-- Every bounded load restricts to an injective identity code in each cell. -/
theorem canonicalSupportFiberBoundOfBoundedLoadExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Exhaustion : BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := tensorProfileBound) noSunflower corpus) :
    CanonicalSupportFiberBound
      (tensorProfileBound := tensorProfileBound) F noSunflower := by
  intro cell
  let identityOf :=
    fun x : {x : {x // x ∈ MinimalBlocker.minimalBlocker F} //
        minimalBlockerSupportClass F noSunflower x = cell} =>
      ((Exhaustion.constraintProfile x.val, Exhaustion.forcedRole x.val),
        Exhaustion.internalTensorProfileSlot x.val)
  have identityOf_injective : Function.Injective identityOf := by
    intro left right sameIdentity
    apply Subtype.ext
    apply Exhaustion.code_injective
    apply Prod.ext
    · simpa [minimalBlockerSupportClass] using
        left.property.trans right.property.symm
    · exact congrArg
        (refinedConstraintSignatureEquivFin tensorProfileBound)
        sameIdentity
  calc
    Fintype.card
        {x : {x // x ∈ MinimalBlocker.minimalBlocker F} //
          minimalBlockerSupportClass F noSunflower x = cell} <=
        Fintype.card (RefinedConstraintSignature tensorProfileBound) :=
      Fintype.card_le_of_injective identityOf identityOf_injective
    _ = refinedConstraintSignatureSize tensorProfileBound :=
      refinedConstraintSignature_card tensorProfileBound

/-- The support-fibre inequality is exactly local bounded population. -/
theorem nonempty_boundedLoadExhaustion_iff_canonicalSupportFiberBound
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (tensorProfileBound_positive : 0 < tensorProfileBound) :
    Nonempty (BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := tensorProfileBound) noSunflower corpus) <->
      CanonicalSupportFiberBound
        (tensorProfileBound := tensorProfileBound) F noSunflower := by
  constructor
  · intro Exhaustion
    exact canonicalSupportFiberBoundOfBoundedLoadExhaustion Exhaustion.some
  · intro Bound
    exact ⟨boundedLoadExhaustionOfCanonicalSupportFiberBound
      tensorProfileBound_positive Bound⟩

/--
Unconditional finite exhaustion of the local population question. Either the
bounded load is populated, or one explicit inherited support cell contains
strictly more realizers than the complete refined identity alphabet.
-/
theorem population_or_oversizedCanonicalSupportFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (tensorProfileBound_positive : 0 < tensorProfileBound) :
    Nonempty (BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := tensorProfileBound) noSunflower corpus) ∨
      Exists fun cell : Finset (Fin k) =>
        refinedConstraintSignatureSize tensorProfileBound <
          Fintype.card
            {x : {x // x ∈ MinimalBlocker.minimalBlocker F} //
              minimalBlockerSupportClass F noSunflower x = cell} := by
  classical
  by_cases Bound : CanonicalSupportFiberBound
      (tensorProfileBound := tensorProfileBound) F noSunflower
  · exact Or.inl ⟨boundedLoadExhaustionOfCanonicalSupportFiberBound
      tensorProfileBound_positive Bound⟩
  · apply Or.inr
    simp only [CanonicalSupportFiberBound, FiniteFiberBound] at Bound
    rcases Classical.not_forall.mp Bound with ⟨cell, oversized⟩
    exact ⟨cell, Nat.lt_of_not_ge oversized⟩

/--
The reduced high-rank inheritance input. The lower-rank populations are
available to the combinatorial proof, but the conclusion is only the explicit
same-support fibre inequality needed by the generic constructor above.
-/
structure ThreePetalDenseHighRankSupportFiberInheritanceSource
    (alpha : Type)
    [DecidableEq alpha] where
  inheritSupportFiberBound :
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
      CanonicalSupportFiberBound
        (tensorProfileBound := traditionalSeedTensorProfileBound
          3 threePetalTraditionalCutoff)
        F noSunflower

/-- The concrete fibre inheritance theorem constructs the requested source. -/
noncomputable def
    ThreePetalDenseHighRankSupportFiberInheritanceSource.toPopulationInheritanceSource
    {alpha : Type}
    [DecidableEq alpha]
    (Source : ThreePetalDenseHighRankSupportFiberInheritanceSource alpha) :
    ThreePetalHighRankPopulationInheritanceSource alpha where
  inheritAboveReflectedCutoff := by
    intro r F noSunflower aboveCutoff sizeExcess lowerPopulation
    exact boundedLoadExhaustionOfCanonicalSupportFiberBound
      (by simp [threePetalTraditionalSeedTensorProfileBound_eq])
      (Source.inheritSupportFiberBound r F noSunflower aboveCutoff
        sizeExcess lowerPopulation)

/-- The explicit same-support inheritance theorem closes the endpoint pipeline. -/
theorem sunflower_of_threePetalDenseHighRankSupportFiberInheritance
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (Source : ThreePetalDenseHighRankSupportFiberInheritanceSource alpha)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      internalTensorConstraintBase 3
          (traditionalSeedTensorProfileBound
            3 threePetalTraditionalCutoff) ^ n < F.edges.card) :
    Concrete.HasSunflower 3 F :=
  sunflower_of_threePetalHighRankPopulationInheritance
    Source.toPopulationInheritanceSource F sizeExcess

/-- The exact constant-base endpoint carried by the high-rank source. -/
def ThreePetalSeedBaseEndpointBound
    (alpha : Type)
    [DecidableEq alpha] : Prop :=
  forall n : Nat,
    forall F : Concrete.UniformSetFamily alpha n,
      Not (Concrete.HasSunflower 3 F) ->
        F.edges.card <=
          internalTensorConstraintBase 3
            (traditionalSeedTensorProfileBound
              3 threePetalTraditionalCutoff) ^ n

theorem highRankPopulationInheritance_provesEndpointBound
    {alpha : Type}
    [DecidableEq alpha]
    (Source : ThreePetalHighRankPopulationInheritanceSource alpha) :
    ThreePetalSeedBaseEndpointBound alpha := by
  intro n F noSunflower
  exact Nat.le_of_not_gt fun sizeExcess =>
    noSunflower <|
      sunflower_of_threePetalHighRankPopulationInheritance
        Source F sizeExcess

/-- The endpoint bound supplies the reverse direction of the transfer correspondence. -/
def threePetalHighRankPopulationInheritanceSourceOfEndpointBound
    {alpha : Type}
    [DecidableEq alpha]
    (Bound : ThreePetalSeedBaseEndpointBound alpha) :
    ThreePetalHighRankPopulationInheritanceSource alpha where
  inheritAboveReflectedCutoff := by
    intro r F noSunflower _aboveCutoff sizeExcess _lowerPopulation
    exact False.elim <| Nat.not_lt_of_ge
      (Bound (r + 1) F noSunflower) sizeExcess

/--
Exact correspondence between the dense high-rank population presentation and
the three-petal constant-base endpoint at the checked base.
-/
theorem nonempty_threePetalHighRankPopulationInheritanceSource_iff_endpointBound
    {alpha : Type}
    [DecidableEq alpha] :
    Nonempty (ThreePetalHighRankPopulationInheritanceSource alpha) <->
      ThreePetalSeedBaseEndpointBound alpha := by
  constructor
  · intro Source
    exact highRankPopulationInheritance_provesEndpointBound Source.some
  · intro Bound
    exact ⟨threePetalHighRankPopulationInheritanceSourceOfEndpointBound
      Bound⟩

end HighRankPopulationInheritance
end V2
end SunflowerAASC
