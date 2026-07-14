import SunflowerAASC.V2.GovernedDeletion
import SunflowerAASC.V2.InternalTensorProfiles
import SunflowerAASC.V2.PopulationInheritance

namespace SunflowerAASC
namespace V2
namespace FixedIdentityPopulation

open GovernedDeletion
open GovernedStructuralForms
open InternalTensorProfiles
open ConstraintMapPopulation

/-- The governed role carried by one fixed refined endpoint identity. -/
def refinedIdentitySemantics
    (tensorProfileBound : Nat) :
    GovernedFormSemantics
      (RefinedConstraintSignature tensorProfileBound) where
  role := fun identity => identity.1.2

/--
The fixed identity carrier is inherited unchanged at every rank. This is the
kernel-faithful, rank-independent identity system used by the population map.
-/
noncomputable def refinedIdentityInheritance
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (tensorProfileBound : Nat) :
    KernelFaithfulStableIdentityInheritance corpus endpointUse :=
  kernelFaithfulFixedIdentityInheritance
    endpointUse
    (RefinedConstraintSignature tensorProfileBound)
    (refinedIdentitySemantics tensorProfileBound)

/--
Concrete population of live private witnesses by one fixed identity carrier.
The matching-support cell is the overlapping Venn layer. Inside one cell,
equality of determinate identities is final.
-/
structure KernelFaithfulFixedIdentityRealization
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) where
  tensorProfileBound_positive : 0 < tensorProfileBound
  identityOf :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      RefinedConstraintSignature tensorProfileBound
  identityFinality :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩ ->
      identityOf left = identityOf right ->
      left = right

/--
AASC-native same-side closure. Different finite identities occupy the bounded
fiber. At equal identity, exhaustion leaves only skin, a prime-changing tensor
split, or a sunflower. There is no independent-authorizer branch because the
residual variation is same-side data.
-/
structure AASCSameSideIdentityExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) where
  tensorProfileBound_positive : 0 < tensorProfileBound
  identityOf :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      RefinedConstraintSignature tensorProfileBound
  skinEquivalent :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  tensorSplit :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  sameIdentityExhaustive :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩ ->
      identityOf left = identityOf right ->
      skinEquivalent left right ∨
        tensorSplit left right ∨
        Concrete.HasSunflower k F
  skinFinality :
    forall left right, skinEquivalent left right -> left = right
  tensorSplitExcluded :
    forall left right, tensorSplit left right -> False

/-- Exhaustion and impossibility derive fixed-identity finality. -/
theorem AASCSameSideIdentityExhaustion.collision
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Exhaustion : AASCSameSideIdentityExhaustion
      (tensorProfileBound := tensorProfileBound) F noSunflower)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameSupport :
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩)
    (sameIdentity : Exhaustion.identityOf left = Exhaustion.identityOf right) :
    left = right := by
  rcases Exhaustion.sameIdentityExhaustive
      left right sameSupport sameIdentity with skin | tensorOrSunflower
  · exact Exhaustion.skinFinality left right skin
  · rcases tensorOrSunflower with tensor | sunflower
    · exact False.elim <| Exhaustion.tensorSplitExcluded left right tensor
    · exact False.elim <| noSunflower sunflower

noncomputable def AASCSameSideIdentityExhaustion.toFixedIdentityRealization
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Exhaustion : AASCSameSideIdentityExhaustion
      (tensorProfileBound := tensorProfileBound) F noSunflower) :
    KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower where
  tensorProfileBound_positive := Exhaustion.tensorProfileBound_positive
  identityOf := Exhaustion.identityOf
  identityFinality := by
    intro left right sameSupport sameIdentity
    exact Exhaustion.collision left right sameSupport sameIdentity

/-- Any completed realization can be presented in exhaustion-first form. -/
noncomputable def
    KernelFaithfulFixedIdentityRealization.toAASCSameSideIdentityExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Realization : KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower) :
    AASCSameSideIdentityExhaustion
      (tensorProfileBound := tensorProfileBound) F noSunflower where
  tensorProfileBound_positive := Realization.tensorProfileBound_positive
  identityOf := Realization.identityOf
  skinEquivalent := fun left right => left = right
  tensorSplit := fun _ _ => False
  sameIdentityExhaustive := by
    intro left right sameSupport sameIdentity
    exact Or.inl <| Realization.identityFinality
      left right sameSupport sameIdentity
  skinFinality := fun _ _ same => same
  tensorSplitExcluded := fun _ _ impossible => impossible

/-- Exhaustion-first closure is exact, rather than an extra assumption. -/
theorem nonempty_sameSideExhaustion_iff_fixedIdentityRealization
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)} :
    Nonempty (AASCSameSideIdentityExhaustion
      (tensorProfileBound := tensorProfileBound) F noSunflower) <->
      Nonempty (KernelFaithfulFixedIdentityRealization
        (tensorProfileBound := tensorProfileBound) F noSunflower) := by
  constructor
  · intro Exhaustion
    exact ⟨Exhaustion.some.toFixedIdentityRealization⟩
  · intro Realization
    exact ⟨Realization.some.toAASCSameSideIdentityExhaustion⟩

/--
The literal six-level constraint formalism. Each blocker receives six Boolean
observations and one of the four roles. Equal observations and equal role are
then closed by same-side exhaustion and impossibility.
-/
structure SixLevelAASCSameSideExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) where
  constraintObserved :
    ConstraintMapLevel ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Bool
  forcedRole :
    {x // x ∈ MinimalBlocker.minimalBlocker F} -> AASCBlockerRole
  skinEquivalent :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  tensorSplit :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  sameObservationExhaustive :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩ ->
      (forall level,
        constraintObserved level left = constraintObserved level right) ->
      forcedRole left = forcedRole right ->
      skinEquivalent left right ∨
        tensorSplit left right ∨
        Concrete.HasSunflower k F
  skinFinality :
    forall left right, skinEquivalent left right -> left = right
  tensorSplitExcluded :
    forall left right, tensorSplit left right -> False

/-- The six observations are assembled mechanically into a finite profile. -/
def SixLevelAASCSameSideExhaustion.constraintProfile
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Exhaustion : SixLevelAASCSameSideExhaustion F noSunflower)
    (witness : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    Finset ConstraintMapLevel :=
  Finset.univ.filter fun level =>
    Exhaustion.constraintObserved level witness = true

theorem SixLevelAASCSameSideExhaustion.observation_eq_of_profile_eq
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Exhaustion : SixLevelAASCSameSideExhaustion F noSunflower)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameProfile :
      Exhaustion.constraintProfile left = Exhaustion.constraintProfile right)
    (level : ConstraintMapLevel) :
    Exhaustion.constraintObserved level left =
      Exhaustion.constraintObserved level right := by
  cases leftObservation : Exhaustion.constraintObserved level left <;>
    cases rightObservation : Exhaustion.constraintObserved level right
  · rfl
  · exfalso
    have memberRight : level ∈ Exhaustion.constraintProfile right := by
      simp [SixLevelAASCSameSideExhaustion.constraintProfile,
        rightObservation]
    rw [← sameProfile] at memberRight
    simp [SixLevelAASCSameSideExhaustion.constraintProfile,
      leftObservation] at memberRight
  · exfalso
    have memberLeft : level ∈ Exhaustion.constraintProfile left := by
      simp [SixLevelAASCSameSideExhaustion.constraintProfile,
        leftObservation]
    rw [sameProfile] at memberLeft
    simp [SixLevelAASCSameSideExhaustion.constraintProfile,
      rightObservation] at memberLeft
  · rfl

/-- The six-level truth vector and role are the complete one-slot identity. -/
noncomputable def SixLevelAASCSameSideExhaustion.identityOf
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Exhaustion : SixLevelAASCSameSideExhaustion F noSunflower)
    (witness : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    RefinedConstraintSignature 1 :=
  ((Exhaustion.constraintProfile witness, Exhaustion.forcedRole witness), 0)

/-- Finite constraint exhaustion constructs the fixed AASC identity object. -/
noncomputable def
    SixLevelAASCSameSideExhaustion.toAASCSameSideIdentityExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Exhaustion : SixLevelAASCSameSideExhaustion F noSunflower) :
    AASCSameSideIdentityExhaustion
      (tensorProfileBound := 1) F noSunflower where
  tensorProfileBound_positive := by decide
  identityOf := Exhaustion.identityOf
  skinEquivalent := Exhaustion.skinEquivalent
  tensorSplit := Exhaustion.tensorSplit
  sameIdentityExhaustive := by
    intro left right sameSupport sameIdentity
    have sameSignature := congrArg Prod.fst sameIdentity
    have sameProfile := congrArg Prod.fst sameSignature
    have sameRole := congrArg Prod.snd sameSignature
    exact Exhaustion.sameObservationExhaustive
      left right sameSupport
      (fun level => Exhaustion.observation_eq_of_profile_eq
        left right sameProfile level)
      sameRole
  skinFinality := Exhaustion.skinFinality
  tensorSplitExcluded := Exhaustion.tensorSplitExcluded

theorem internalTensorConstraintBase_one_eq_corpusConstraintBase (k : Nat) :
    internalTensorConstraintBase k 1 = corpusConstraintBase k := by
  simp [internalTensorConstraintBase, refinedConstraintSignatureSize,
    corpusConstraintBase]

/-- Every assigned live identity is inherited literally unchanged. -/
theorem KernelFaithfulFixedIdentityRealization.identity_preserved_at_rank
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    {branch : Concrete.UniformSetFamily alpha (r + 1) -> Prop}
    (endpointUse : LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k) branch)
    (Realization : KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower)
    (rank : Nat)
    (witness : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (refinedIdentityInheritance (corpus := corpus)
      endpointUse tensorProfileBound).inheritedForm rank
        (Realization.identityOf witness) =
      Realization.identityOf witness := by
  rfl

/-- Fixed identity finality mechanically supplies the four-way load exhaustion. -/
noncomputable def KernelFaithfulFixedIdentityRealization.toBoundedLoadExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Realization : KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower) :
    BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := tensorProfileBound) noSunflower corpus where
  tensorProfileBound_positive := Realization.tensorProfileBound_positive
  constraintProfile := fun witness => (Realization.identityOf witness).1.1
  forcedRole := fun witness => (Realization.identityOf witness).1.2
  internalTensorProfileSlot := fun witness => (Realization.identityOf witness).2
  primeChangingTensorSplit := fun _ _ => False
  loadExhaustive := by
    intro left right sameCell sameProfile sameRole load
    apply Or.inl
    intro sameSlot
    have sameSignature :
        (Realization.identityOf left).1 =
          (Realization.identityOf right).1 := by
      apply Prod.ext
      · exact sameProfile
      · exact sameRole
    have sameIdentity :
        Realization.identityOf left = Realization.identityOf right := by
      apply Prod.ext
      · exact sameSignature
      · exact sameSlot
    have sameWitness := Realization.identityFinality
      left right sameCell sameIdentity
    subst right
    exact load.rightNegative load.leftPositive
  primeChangingTensorSplitExcluded := fun _ _ impossible => impossible

/-- Existing bounded exhaustion already determines a fixed endpoint identity. -/
noncomputable def
    BoundedPrivateWitnessLoadExhaustion.toFixedIdentityRealization
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Exhaustion : BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound := tensorProfileBound) noSunflower corpus) :
    KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower where
  tensorProfileBound_positive := Exhaustion.tensorProfileBound_positive
  identityOf := fun witness =>
    ((Exhaustion.constraintProfile witness, Exhaustion.forcedRole witness),
      Exhaustion.internalTensorProfileSlot witness)
  identityFinality := by
    intro left right sameCell sameIdentity
    have sameConstraintSignature := congrArg Prod.fst sameIdentity
    have sameSlot := congrArg Prod.snd sameIdentity
    have sameProfile := congrArg Prod.fst sameConstraintSignature
    have sameRole := congrArg Prod.snd sameConstraintSignature
    apply Classical.byContradiction
    intro distinct
    let load := MinimalBlocker.privateWitnessEndpointLoadOfDistinct
      F left right distinct
    rcases Exhaustion.loadExhaustive
        left right sameCell sameProfile sameRole load with
      differentSlot | splitOrSunOrIndependent
    · exact differentSlot sameSlot
    · rcases splitOrSunOrIndependent with split | sunOrIndependent
      · exact Exhaustion.primeChangingTensorSplitExcluded left right split
      · rcases sunOrIndependent with sunflower | independent
        · exact noSunflower sunflower
        · rcases independent with ⟨factor, authorizer⟩
          exact corpus.fixedDomainClosure.excludesIndependentAuthorizer
            factor authorizer

/-- The identity and exhaustion formulations have exactly the same content. -/
theorem nonempty_fixedIdentityRealization_iff_boundedLoadExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)} :
    Nonempty (KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower) <->
      Nonempty (BoundedPrivateWitnessLoadExhaustion
        (tensorProfileBound := tensorProfileBound) noSunflower corpus) := by
  constructor
  · intro Realization
    exact ⟨Realization.some.toBoundedLoadExhaustion⟩
  · intro Exhaustion
    exact ⟨SunflowerAASC.V2.FixedIdentityPopulation.BoundedPrivateWitnessLoadExhaustion.toFixedIdentityRealization
      Exhaustion.some⟩

/-- The checked traditional seed population already realizes fixed identities. -/
noncomputable def traditionalSeedFixedIdentityRealization
    {alpha : Type}
    [DecidableEq alpha]
    {r k cutoff : Nat}
    (k_nondegenerate : 3 <= k)
    (cutoff_positive : 0 < cutoff)
    (rankAtMost : r + 1 <= cutoff)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    KernelFaithfulFixedIdentityRealization
      (tensorProfileBound :=
        PopulationInheritance.traditionalSeedTensorProfileBound k cutoff)
      F noSunflower :=
  SunflowerAASC.V2.FixedIdentityPopulation.BoundedPrivateWitnessLoadExhaustion.toFixedIdentityRealization <|
    PopulationInheritance.traditionalSeedPopulation
      k_nondegenerate cutoff_positive rankAtMost F noSunflower

/--
The one remaining rank-uniform datum, restricted to genuine dense
countercases: realize every live blocker in the fixed identity carrier.
-/
structure DenseKernelFaithfulFixedIdentitySource
    (alpha : Type)
    [DecidableEq alpha]
    (k tensorProfileBound : Nat)
    (k_nondegenerate : 3 <= k) where
  realize :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      internalTensorConstraintBase k tensorProfileBound ^ (r + 1) <
          F.edges.card ->
        KernelFaithfulFixedIdentityRealization
          (tensorProfileBound := tensorProfileBound) F noSunflower

/-- The preferred dense source states the native exhaustion theorem directly. -/
structure DenseAASCSameSideExhaustionSource
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
        AASCSameSideIdentityExhaustion
          (tensorProfileBound := tensorProfileBound) F noSunflower

/-- Rank-uniform exhaustion of the literal six-level/four-role formalism. -/
structure DenseSixLevelAASCExhaustionSource
    (alpha : Type)
    [DecidableEq alpha]
    (k : Nat)
    (k_nondegenerate : 3 <= k) where
  exhaust :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      corpusConstraintBase k ^ (r + 1) < F.edges.card ->
        SixLevelAASCSameSideExhaustion F noSunflower

noncomputable def DenseSixLevelAASCExhaustionSource.toDenseSameSideSource
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseSixLevelAASCExhaustionSource alpha k k_nondegenerate) :
    DenseAASCSameSideExhaustionSource alpha k 1 k_nondegenerate where
  exhaust := by
    intro r F noSunflower sizeExcess
    apply SixLevelAASCSameSideExhaustion.toAASCSameSideIdentityExhaustion
    apply Src.exhaust r F noSunflower
    simpa only [internalTensorConstraintBase_one_eq_corpusConstraintBase] using
      sizeExcess

noncomputable def DenseAASCSameSideExhaustionSource.toDenseFixedIdentitySource
    {alpha : Type}
    [DecidableEq alpha]
    {k tensorProfileBound : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseAASCSameSideExhaustionSource
      alpha k tensorProfileBound k_nondegenerate) :
    DenseKernelFaithfulFixedIdentitySource
      alpha k tensorProfileBound k_nondegenerate where
  realize := by
    intro r F noSunflower sizeExcess
    exact (Src.exhaust r F noSunflower sizeExcess).toFixedIdentityRealization

noncomputable def DenseKernelFaithfulFixedIdentitySource.toDenseLoadSource
    {alpha : Type}
    [DecidableEq alpha]
    {k tensorProfileBound : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseKernelFaithfulFixedIdentitySource
      alpha k tensorProfileBound k_nondegenerate) :
    DenseBoundedPrivateWitnessLoadSource
      alpha k tensorProfileBound k_nondegenerate where
  exhaust := by
    intro r F noSunflower sizeExcess
    exact (Src.realize r F noSunflower sizeExcess).toBoundedLoadExhaustion

/-- A dense bounded-load source already is a dense fixed-identity source. -/
noncomputable def denseFixedIdentitySourceOfDenseLoadSource
    {alpha : Type}
    [DecidableEq alpha]
    {k tensorProfileBound : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseBoundedPrivateWitnessLoadSource
      alpha k tensorProfileBound k_nondegenerate) :
    DenseKernelFaithfulFixedIdentitySource
      alpha k tensorProfileBound k_nondegenerate where
  realize := by
    intro r F noSunflower sizeExcess
    exact
      SunflowerAASC.V2.FixedIdentityPopulation.BoundedPrivateWitnessLoadExhaustion.toFixedIdentityRealization <|
        Src.exhaust r F noSunflower sizeExcess

/--
No-laundering at the rank-uniform source boundary: fixed identity population
removes duplicate transport premises but is not weaker than bounded population.
-/
theorem nonempty_denseFixedIdentitySource_iff_denseLoadSource
    {alpha : Type}
    [DecidableEq alpha]
    {k tensorProfileBound : Nat}
    {k_nondegenerate : 3 <= k} :
    Nonempty (DenseKernelFaithfulFixedIdentitySource
      alpha k tensorProfileBound k_nondegenerate) <->
      Nonempty (DenseBoundedPrivateWitnessLoadSource
        alpha k tensorProfileBound k_nondegenerate) := by
  constructor
  · intro Src
    exact ⟨Src.some.toDenseLoadSource⟩
  · intro Src
    exact ⟨denseFixedIdentitySourceOfDenseLoadSource Src.some⟩

/-- Rank-deletion population inheritance and fixed identity population compose. -/
noncomputable def denseFixedIdentitySourceOfRankDeletionInheritance
    {alpha : Type}
    [DecidableEq alpha]
    {k cutoff : Nat}
    {k_nondegenerate : 3 <= k}
    {cutoff_positive : 0 < cutoff}
    (Src : PopulationInheritance.DenseRankDeletionPopulationInheritanceSource
      alpha k cutoff k_nondegenerate cutoff_positive) :
    DenseKernelFaithfulFixedIdentitySource
      alpha k
        (PopulationInheritance.traditionalSeedTensorProfileBound k cutoff)
        k_nondegenerate where
  realize := by
    intro r F noSunflower sizeExcess
    exact
      SunflowerAASC.V2.FixedIdentityPopulation.BoundedPrivateWitnessLoadExhaustion.toFixedIdentityRealization <|
        Src.population r F noSunflower sizeExcess

/-- Fixed, kernel-faithful identity population gives the classical endpoint. -/
theorem sunflower_of_dense_fixedIdentityPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {n k tensorProfileBound : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseKernelFaithfulFixedIdentitySource
      alpha k tensorProfileBound k_nondegenerate)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      internalTensorConstraintBase k tensorProfileBound ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  exact sunflower_of_dense_boundedPrivateWitnessLoad
    Src.toDenseLoadSource F sizeExcess

/-- The endpoint stated in AASC's native exhaustion-and-impossibility form. -/
theorem sunflower_of_dense_aascSameSideExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {n k tensorProfileBound : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseAASCSameSideExhaustionSource
      alpha k tensorProfileBound k_nondegenerate)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      internalTensorConstraintBase k tensorProfileBound ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  exact sunflower_of_dense_fixedIdentityPopulation
    Src.toDenseFixedIdentitySource F sizeExcess

/--
Six-level AASC exhaustion closes at the exact derived alphabet
`2^k * 256`; no additional tensor-profile numeral is primitive.
-/
theorem sunflower_of_dense_sixLevelAASCExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseSixLevelAASCExhaustionSource alpha k k_nondegenerate)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess : corpusConstraintBase k ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  apply sunflower_of_dense_aascSameSideExhaustion
    Src.toDenseSameSideSource F
  simpa only [internalTensorConstraintBase_one_eq_corpusConstraintBase] using
    sizeExcess

/-- The dense six-level exhaustion source proves the full endpoint bound. -/
theorem DenseSixLevelAASCExhaustionSource.provesEndpointBound
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseSixLevelAASCExhaustionSource alpha k k_nondegenerate) :
    DenseCountercaseRange.CorpusBaseEndpointBound alpha k := by
  intro n F noSunflower
  exact Nat.le_of_not_gt fun sizeExcess =>
    noSunflower <| sunflower_of_dense_sixLevelAASCExhaustion
      Src F sizeExcess

/--
Conversely, a completed endpoint bound can inhabit dense exhaustion only by
eliminating the requested countercase. This direction audits logical strength.
-/
def denseSixLevelAASCExhaustionSourceOfEndpointBound
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k}
    (Bound : DenseCountercaseRange.CorpusBaseEndpointBound alpha k) :
    DenseSixLevelAASCExhaustionSource alpha k k_nondegenerate where
  exhaust := by
    intro r F noSunflower sizeExcess
    exact False.elim <| Nat.not_lt_of_ge
      (Bound (r + 1) F noSunflower) sizeExcess

/--
No-laundering theorem: the rank-uniform semantic exhaustion clause is
logically equivalent to the desired constant-base sunflower endpoint.
-/
theorem nonempty_denseSixLevelAASCExhaustionSource_iff_endpointBound
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k} :
    Nonempty (DenseSixLevelAASCExhaustionSource
      alpha k k_nondegenerate) <->
      DenseCountercaseRange.CorpusBaseEndpointBound alpha k := by
  constructor
  · intro Source
    exact Source.some.provesEndpointBound
  · intro Bound
    exact ⟨denseSixLevelAASCExhaustionSourceOfEndpointBound Bound⟩

end FixedIdentityPopulation
end V2
end SunflowerAASC
