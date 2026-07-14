import SunflowerAASC.V2.ConstraintMapPopulation

namespace SunflowerAASC
namespace V2
namespace InternalTensorProfiles

open ConstraintMapPopulation

/--
Skin is representative-only and inherits whatever standing its underlying
content already has.  It is not a primitive standing-bearing outcome.
-/
abbrev InheritedEndpointSkin
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) :=
  MinimalBlocker.EndpointSkinEquivalent F left right

/-- A coarse corpus signature refined by one lawful internal tensor profile. -/
abbrev RefinedConstraintSignature (tensorProfileBound : Nat) :=
  ConstraintSignature × Fin tensorProfileBound

def refinedConstraintSignatureSize (tensorProfileBound : Nat) : Nat :=
  constraintSignatureSize * tensorProfileBound

theorem refinedConstraintSignature_card (tensorProfileBound : Nat) :
    Fintype.card (RefinedConstraintSignature tensorProfileBound) =
      refinedConstraintSignatureSize tensorProfileBound := by
  simp [RefinedConstraintSignature, refinedConstraintSignatureSize,
    ConstraintSignature, constraintSignatureSize, constraintMapLevel_card,
    WitnessCompression.aascBlockerRole_card]

noncomputable def refinedConstraintSignatureEquivFin
    (tensorProfileBound : Nat) :
    RefinedConstraintSignature tensorProfileBound ≃
      Fin (refinedConstraintSignatureSize tensorProfileBound) :=
  Fintype.equivFinOfCardEq
    (refinedConstraintSignature_card tensorProfileBound)

theorem refinedConstraintSignatureSize_eq (tensorProfileBound : Nat) :
    refinedConstraintSignatureSize tensorProfileBound =
      256 * tensorProfileBound := by
  simp [refinedConstraintSignatureSize, constraintSignatureSize_eq]

/--
The corrected load-bearing exhaustion.  A distinct private witness already
carries a concrete endpoint load, so skin is absent.  A same-cell/coarse-code
load must instead:

* occupy a different lawful internal tensor-profile slot;
* change the admissible relation through a prime-changing tensor split;
* realize a concrete sunflower; or
* claim an independent authorizer, which fixed-domain AASC excludes.

The finite tensor-profile reservoir is structural population data.  Its
numerical cardinal is derived only after the roles are populated; the four
broad AASC labels alone do not construct the population map into that
reservoir.
-/
structure BoundedPrivateWitnessLoadExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (noSunflower : Not (Concrete.HasSunflower k F))
    (corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)) where
  tensorProfileBound_positive : 0 < tensorProfileBound
  constraintProfile :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      Finset ConstraintMapLevel
  forcedRole :
    {x // x ∈ MinimalBlocker.minimalBlocker F} -> AASCBlockerRole
  internalTensorProfileSlot :
    {x // x ∈ MinimalBlocker.minimalBlocker F} -> Fin tensorProfileBound
  primeChangingTensorSplit :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
    {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  loadExhaustive :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩ ->
      constraintProfile left = constraintProfile right ->
      forcedRole left = forcedRole right ->
      MinimalBlocker.PrivateWitnessEndpointLoad F left right ->
        internalTensorProfileSlot left ≠ internalTensorProfileSlot right ∨
        primeChangingTensorSplit left right ∨
        Concrete.HasSunflower k F ∨
        Exists (fun factor :
          (Concrete.concreteSunflowerCarrier alpha (r + 1) k).StandingFactor =>
          corpus.fixedDomainClosure.disposition factor =
            SameScopeFactorDisposition.independentAuthorizer)
  primeChangingTensorSplitExcluded :
    forall left right, primeChangingTensorSplit left right -> False

/-- The lawful internal-tensor branch is precisely separation by its bounded slot. -/
def BoundedPrivateWitnessLoadExhaustion.InternalTensorProfileDifference
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Exhaustion : BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := tensorProfileBound) noSunflower corpus)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Prop :=
  Exhaustion.internalTensorProfileSlot left ≠
    Exhaustion.internalTensorProfileSlot right

/-- Every realized load is unconditionally outside inherited endpoint skin. -/
theorem BoundedPrivateWitnessLoadExhaustion.load_not_inheritedSkin
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (_Exhaustion : BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := tensorProfileBound) noSunflower corpus)
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (load : MinimalBlocker.PrivateWitnessEndpointLoad F left right) :
    Not (InheritedEndpointSkin F left right) :=
  load.not_endpointSkin

noncomputable def BoundedPrivateWitnessLoadExhaustion.code
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Exhaustion : BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := tensorProfileBound) noSunflower corpus) :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      VennSeparation.VennCellCode k
        (refinedConstraintSignatureSize tensorProfileBound) :=
  fun x =>
    (BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
      ⟨x.val, MinimalBlocker.minimalBlocker_subset_raw F x.property⟩,
      refinedConstraintSignatureEquivFin tensorProfileBound
        ((Exhaustion.constraintProfile x, Exhaustion.forcedRole x),
          Exhaustion.internalTensorProfileSlot x))

theorem BoundedPrivateWitnessLoadExhaustion.collision
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Exhaustion : BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := tensorProfileBound) noSunflower corpus)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameCode : Exhaustion.code left = Exhaustion.code right) :
    left = right := by
  have sameCell := congrArg Prod.fst sameCode
  have sameRefinedCode := congrArg Prod.snd sameCode
  have sameRefinedSignature :
      ((Exhaustion.constraintProfile left, Exhaustion.forcedRole left),
          Exhaustion.internalTensorProfileSlot left) =
        ((Exhaustion.constraintProfile right, Exhaustion.forcedRole right),
          Exhaustion.internalTensorProfileSlot right) :=
    (refinedConstraintSignatureEquivFin tensorProfileBound).injective
      sameRefinedCode
  have sameConstraintSignature := congrArg Prod.fst sameRefinedSignature
  have sameTensorProfile := congrArg Prod.snd sameRefinedSignature
  apply Classical.byContradiction
  intro distinct
  let load := MinimalBlocker.privateWitnessEndpointLoadOfDistinct
    F left right distinct
  rcases Exhaustion.loadExhaustive
      left right sameCell
      (congrArg Prod.fst sameConstraintSignature)
      (congrArg Prod.snd sameConstraintSignature)
      load with
    internalTensorDifferent | splitOrSunOrIndependent
  · exact internalTensorDifferent sameTensorProfile
  · rcases splitOrSunOrIndependent with split | sunOrIndependent
    · exact Exhaustion.primeChangingTensorSplitExcluded left right split
    · rcases sunOrIndependent with sunflower | independent
      · exact noSunflower sunflower
      · rcases independent with ⟨factor, authorizer⟩
        exact corpus.fixedDomainClosure.excludesIndependentAuthorizer
          factor authorizer

theorem BoundedPrivateWitnessLoadExhaustion.code_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Exhaustion : BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := tensorProfileBound) noSunflower corpus) :
    Function.Injective Exhaustion.code := by
  intro left right sameCode
  exact Exhaustion.collision left right sameCode

theorem BoundedPrivateWitnessLoadExhaustion.minimalBlocker_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Exhaustion : BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := tensorProfileBound) noSunflower corpus) :
    (MinimalBlocker.minimalBlocker F).card <=
      VennSeparation.vennAlphabetSize k
        (refinedConstraintSignatureSize tensorProfileBound) := by
  have card_le := Fintype.card_le_of_injective
    Exhaustion.code Exhaustion.code_injective
  simpa [VennSeparation.vennCellCode_card] using card_le

/-- The old singleton-profile population is exactly the `B = 1` special case. -/
noncomputable def boundedLoadExhaustionOfConstraintPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : PrivateWitnessConstraintPopulation noSunflower corpus) :
    BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := 1) noSunflower corpus where
  tensorProfileBound_positive := by decide
  constraintProfile := Population.constraintProfile
  forcedRole := Population.forcedRole
  internalTensorProfileSlot := fun _ => 0
  primeChangingTensorSplit := fun _ _ => False
  loadExhaustive := by
    intro left right sameCell sameProfile sameRole load
    exact Or.inr <| Or.inr <| Or.inr <|
      Population.completeSignatureExhaustion
        left right sameCell sameProfile sameRole load
  primeChangingTensorSplitExcluded := fun _ _ impossible => impossible

/-- A one-slot bounded exhaustion recovers the original singleton population. -/
def BoundedPrivateWitnessLoadExhaustion.toSingletonPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Exhaustion : BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := 1) noSunflower corpus) :
    PrivateWitnessConstraintPopulation noSunflower corpus where
  constraintProfile := Exhaustion.constraintProfile
  forcedRole := Exhaustion.forcedRole
  completeSignatureExhaustion := by
    intro left right sameCell sameProfile sameRole load
    rcases Exhaustion.loadExhaustive
        left right sameCell sameProfile sameRole load with
      internalTensorDifferent | splitOrSunOrIndependent
    · exact False.elim <| internalTensorDifferent (Subsingleton.elim _ _)
    · rcases splitOrSunOrIndependent with split | sunOrIndependent
      · exact False.elim <|
          Exhaustion.primeChangingTensorSplitExcluded left right split
      · rcases sunOrIndependent with sunflower | independent
        · exact False.elim (noSunflower sunflower)
        · exact independent

theorem nonempty_boundedLoadExhaustion_one_iff_population
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)} :
    Nonempty (BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := 1) noSunflower corpus) <->
      Nonempty (PrivateWitnessConstraintPopulation noSunflower corpus) := by
  constructor
  · intro Exhaustion
    exact ⟨Exhaustion.some.toSingletonPopulation⟩
  · intro Population
    exact ⟨boundedLoadExhaustionOfConstraintPopulation Population.some⟩

def internalTensorConstraintBase
    (k tensorProfileBound : Nat) : Nat :=
  VennSeparation.vennAlphabetSize k
    (refinedConstraintSignatureSize tensorProfileBound)

theorem internalTensorConstraintBase_eq (k tensorProfileBound : Nat) :
    internalTensorConstraintBase k tensorProfileBound =
      2 ^ k * (256 * tensorProfileBound) := by
  simp [internalTensorConstraintBase, VennSeparation.vennAlphabetSize,
    refinedConstraintSignatureSize_eq]

/-- Dense-countercase population with a uniformly bounded internal tensor profile. -/
structure DenseBoundedPrivateWitnessLoadSource
    (alpha : Type)
    [DecidableEq alpha]
    (k tensorProfileBound : Nat)
    (k_nondegenerate : 3 <= k) where
  exhaust :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      internalTensorConstraintBase k tensorProfileBound ^ (r + 1) <
          F.edges.card ->
        BoundedPrivateWitnessLoadExhaustion
          (tensorProfileBound := tensorProfileBound)
          noSunflower
          (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
            alpha k k_nondegenerate r)

noncomputable def DenseBoundedPrivateWitnessLoadSource.toDenseBlockerSource
    {alpha : Type}
    [DecidableEq alpha]
    {k tensorProfileBound : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseBoundedPrivateWitnessLoadSource
      alpha k tensorProfileBound k_nondegenerate) :
    EffectiveBlocker.DenseCountercaseSource
      alpha k (internalTensorConstraintBase k tensorProfileBound) where
  certificate := by
    intro r F noSunflower sizeExcess
    let Exhaustion := Src.exhaust r F noSunflower sizeExcess
    exact
      { blocker := MinimalBlocker.minimalBlocker F
        blocker_card_le := Exhaustion.minimalBlocker_card_le
        hitsEveryEdge := by
          intro edge edge_mem
          rcases Finset.not_disjoint_iff.mp
              (MinimalBlocker.minimalBlocker_hitsEveryEdge F edge edge_mem) with
            ⟨x, x_edge, x_blocker⟩
          exact ⟨x, x_blocker, x_edge⟩ }

theorem sunflower_of_dense_boundedPrivateWitnessLoad
    {alpha : Type}
    [DecidableEq alpha]
    {n k tensorProfileBound : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseBoundedPrivateWitnessLoadSource
      alpha k tensorProfileBound k_nondegenerate)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      internalTensorConstraintBase k tensorProfileBound ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  exact EffectiveBlocker.sunflower_of_card_gt_pow_of_denseCountercaseSource
    Src.toDenseBlockerSource F sizeExcess

end InternalTensorProfiles
end V2
end SunflowerAASC
