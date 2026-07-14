import SunflowerAASC.V2.BlockerSupportLayers

namespace SunflowerAASC
namespace V2
namespace ConstraintMapPopulation

/-- The six finite levels of the published admissibility constraint map. -/
inductive ConstraintMapLevel where
  | architecturalFoundation
  | ametricBoundary
  | operatorEnvelope
  | lawfulRedescription
  | compositionSequencing
  | standingEnforcement
deriving DecidableEq, Repr

instance : Fintype ConstraintMapLevel where
  elems := {
    .architecturalFoundation,
    .ametricBoundary,
    .operatorEnvelope,
    .lawfulRedescription,
    .compositionSequencing,
    .standingEnforcement }
  complete := by
    intro level
    cases level <;> simp

theorem constraintMapLevel_card : Fintype.card ConstraintMapLevel = 6 := by
  decide

/--
An overlapping coarse constraint-bundle profile together with its forced AASC
role.  The profile is not a partition, and finite-index completeness remains a
quantitative theorem rather than part of this definition.
-/
abbrev ConstraintSignature :=
  Finset ConstraintMapLevel × AASCBlockerRole

def constraintSignatureSize : Nat := 2 ^ 6 * 4

theorem constraintSignature_card :
    Fintype.card ConstraintSignature = constraintSignatureSize := by
  simp [ConstraintSignature, constraintSignatureSize,
    constraintMapLevel_card, WitnessCompression.aascBlockerRole_card]

theorem constraintSignatureSize_eq : constraintSignatureSize = 256 := by
  decide

noncomputable def constraintSignatureEquivFin :
    ConstraintSignature ≃ Fin constraintSignatureSize :=
  Fintype.equivFinOfCardEq constraintSignature_card

/--
The generative half of the finite-candidate argument.  Combinatorics supplies
the candidate type, proves its quantitative bound, and sends every realized
private witness to a candidate.  No AASC corpus, endpoint disposition, or
collision impossibility occurs in this structure.
-/
structure PrivateWitnessCombinatorialCandidateRealization
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (candidateBound : Nat)
    (_noSunflower : Not (Concrete.HasSunflower k F)) where
  Candidate : Type
  candidateFintype : Fintype Candidate
  candidateCard_le : Fintype.card Candidate ≤ candidateBound
  realize :
    {x // x ∈ MinimalBlocker.minimalBlocker F} -> Candidate

/--
The eliminative AASC half.  Once combinatorics has produced a candidate code,
AASC exhausts a code collision: either the realizers are already identical or
the collision would require an independent standing authorizer.  This object
does not construct a candidate and does not assert that any candidate is
occupied.
-/
structure PrivateWitnessAASCCandidateCollisionSieve
    {alpha : Type}
    [DecidableEq alpha]
    {r k candidateBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k))
    (Realization : PrivateWitnessCombinatorialCandidateRealization
      candidateBound noSunflower) where
  collisionExhaustive :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      Realization.realize left = Realization.realize right ->
      left = right \/
        Exists (fun factor :
          (Concrete.concreteSunflowerCarrier alpha (r + 1) k).StandingFactor =>
          corpus.fixedDomainClosure.disposition factor =
            SameScopeFactorDisposition.independentAuthorizer)

/-- Fixed-domain impossibility removes the non-identity collision branch. -/
theorem PrivateWitnessAASCCandidateCollisionSieve.realize_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r k candidateBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    {Realization : PrivateWitnessCombinatorialCandidateRealization
      candidateBound noSunflower}
    (Sieve : PrivateWitnessAASCCandidateCollisionSieve corpus Realization) :
    Function.Injective Realization.realize := by
  intro left right sameCandidate
  rcases Sieve.collisionExhaustive left right sameCandidate with
    sameRealizer | ⟨factor, independent⟩
  · exact sameRealizer
  · exact False.elim <|
      corpus.fixedDomainClosure.excludesIndependentAuthorizer
        factor independent

/--
Candidate existence remains a combinatorial input.  Given one such witness,
the AASC sieve upgrades it to unique realization; the sieve alone proves only
the at-most-one half.
-/
theorem PrivateWitnessAASCCandidateCollisionSieve.existsUnique_realizer_of_exists
    {alpha : Type}
    [DecidableEq alpha]
    {r k candidateBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    {Realization : PrivateWitnessCombinatorialCandidateRealization
      candidateBound noSunflower}
    (Sieve : PrivateWitnessAASCCandidateCollisionSieve corpus Realization)
    (candidate : Realization.Candidate)
    (existsRealizer : Exists (fun witness =>
      Realization.realize witness = candidate)) :
    ExistsUnique (fun witness =>
      Realization.realize witness = candidate) := by
  rcases existsRealizer with ⟨witness, realizes⟩
  refine ⟨witness, realizes, ?_⟩
  intro other otherRealizes
  exact Sieve.realize_injective (otherRealizes.trans realizes.symm)

/-- The finite candidate bound is numerical output of generation plus AASC
collision elimination, not an AASC-generated population premise. -/
theorem PrivateWitnessAASCCandidateCollisionSieve.minimalBlocker_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {r k candidateBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    {Realization : PrivateWitnessCombinatorialCandidateRealization
      candidateBound noSunflower}
    (Sieve : PrivateWitnessAASCCandidateCollisionSieve corpus Realization) :
    (MinimalBlocker.minimalBlocker F).card ≤ candidateBound := by
  letI : Fintype Realization.Candidate := Realization.candidateFintype
  have realizedCardLe :
      Fintype.card {x // x ∈ MinimalBlocker.minimalBlocker F} ≤
        Fintype.card Realization.Candidate :=
    Fintype.card_le_of_injective
      Realization.realize Sieve.realize_injective
  exact le_trans (by simpa using realizedCardLe) Realization.candidateCard_le

/--
Compatibility package combining both halves of the older API.  Its classifier
fields are generative data that must come from the combinatorial side; only
`completeSignatureExhaustion` is the AASC eliminative clause.

Distinct private witnesses already carry a concrete endpoint load, so skin is
not a possible collision branch.  The eliminative clause classifies a
same-support, same-signature load as independent standing work.
-/
structure PrivateWitnessConstraintPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (noSunflower : Not (Concrete.HasSunflower k F))
    (corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)) where
  constraintProfile :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      Finset ConstraintMapLevel
  forcedRole :
    {x // x ∈ MinimalBlocker.minimalBlocker F} -> AASCBlockerRole
  completeSignatureExhaustion :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩ ->
      constraintProfile left = constraintProfile right ->
      forcedRole left = forcedRole right ->
      MinimalBlocker.PrivateWitnessEndpointLoad F left right ->
      Exists (fun factor :
        (Concrete.concreteSunflowerCarrier alpha (r + 1) k).StandingFactor =>
        corpus.fixedDomainClosure.disposition factor =
          SameScopeFactorDisposition.independentAuthorizer)

/--
The concrete combinatorial candidate ledger behind the legacy constraint-map
API.  Its support cell and finite signature are constructed without consulting
the AASC corpus.
-/
noncomputable def privateWitnessConstraintCandidateRealization
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (noSunflower : Not (Concrete.HasSunflower k F))
    (constraintProfile :
      {x // x ∈ MinimalBlocker.minimalBlocker F} ->
        Finset ConstraintMapLevel)
    (forcedRole :
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> AASCBlockerRole) :
    PrivateWitnessCombinatorialCandidateRealization
      (VennSeparation.vennAlphabetSize k constraintSignatureSize)
      noSunflower where
  Candidate := VennSeparation.VennCellCode k constraintSignatureSize
  candidateFintype := inferInstance
  candidateCard_le := by
    exact le_of_eq (VennSeparation.vennCellCode_card
      k constraintSignatureSize)
  realize := fun witness =>
    (BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
        ⟨witness.val,
          MinimalBlocker.minimalBlocker_subset_raw F witness.property⟩,
      constraintSignatureEquivFin
        (constraintProfile witness, forcedRole witness))

/-- The combinatorial candidate ledger extracted from the hybrid package. -/
noncomputable def PrivateWitnessConstraintPopulation.candidateRealization
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : PrivateWitnessConstraintPopulation noSunflower corpus) :
    PrivateWitnessCombinatorialCandidateRealization
      (VennSeparation.vennAlphabetSize k constraintSignatureSize)
      noSunflower :=
  privateWitnessConstraintCandidateRealization noSunflower
    Population.constraintProfile Population.forcedRole

/--
The AASC collision sieve extracted from the hybrid package.  Its input is the
already-constructed combinatorial ledger above; its sole work is exhaustive
classification of equal-code collisions.
-/
noncomputable def
    PrivateWitnessConstraintPopulation.toCandidateCollisionSieve
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : PrivateWitnessConstraintPopulation noSunflower corpus) :
    PrivateWitnessAASCCandidateCollisionSieve corpus
      Population.candidateRealization where
  collisionExhaustive := by
    intro left right sameCandidate
    by_cases sameRealizer : left = right
    · exact Or.inl sameRealizer
    · apply Or.inr
      have sameCell := congrArg Prod.fst sameCandidate
      have sameSignatureCode := congrArg Prod.snd sameCandidate
      have sameSignature :=
        constraintSignatureEquivFin.injective sameSignatureCode
      exact Population.completeSignatureExhaustion
        left right sameCell
          (congrArg Prod.fst sameSignature)
          (congrArg Prod.snd sameSignature)
          (MinimalBlocker.privateWitnessEndpointLoadOfDistinct
            F left right sameRealizer)

/--
After the finite support/profile/role collision, a distinct pair supplies its
own private-edge load. Population has only to classify that realized load.
-/
theorem PrivateWitnessConstraintPopulation.distinctCollisionCreatesIndependentAuthorizer
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : PrivateWitnessConstraintPopulation noSunflower corpus)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameCell :
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩)
    (sameProfile :
      Population.constraintProfile left = Population.constraintProfile right)
    (sameRole : Population.forcedRole left = Population.forcedRole right)
    (distinct : left ≠ right) :
    Exists (fun factor :
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k).StandingFactor =>
      corpus.fixedDomainClosure.disposition factor =
        SameScopeFactorDisposition.independentAuthorizer) :=
  Population.completeSignatureExhaustion
    left right sameCell sameProfile sameRole
      (MinimalBlocker.privateWitnessEndpointLoadOfDistinct
        F left right distinct)

/-- Fixed-domain impossibility excludes every distinct populated collision. -/
theorem PrivateWitnessConstraintPopulation.distinctCollisionImpossible
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : PrivateWitnessConstraintPopulation noSunflower corpus)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameCell :
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩)
    (sameProfile :
      Population.constraintProfile left = Population.constraintProfile right)
    (sameRole : Population.forcedRole left = Population.forcedRole right)
    (distinct : left ≠ right) : False := by
  rcases Population.distinctCollisionCreatesIndependentAuthorizer
      left right sameCell sameProfile sameRole distinct with
    ⟨factor, independent⟩
  exact corpus.fixedDomainClosure.excludesIndependentAuthorizer
    factor independent

/--
Within-cell tensor multiplicity collapse. Every distinct pair carries a
private-edge endpoint load and is therefore unconditionally non-skin. Once
population classifies that load as an independent standing authorizer,
fixed-domain AASC exhaustion rules it out.

The population premise is load-bearing: this theorem does not infer finite
type completeness from the six-level vocabulary alone.
-/
theorem PrivateWitnessConstraintPopulation.withinCellTensorMultiplicityCollapse
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : PrivateWitnessConstraintPopulation noSunflower corpus)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameCell :
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩)
    (sameProfile :
      Population.constraintProfile left = Population.constraintProfile right)
    (sameRole : Population.forcedRole left = Population.forcedRole right) :
    left = right := by
  apply Classical.byContradiction
  intro distinct
  exact Population.distinctCollisionImpossible
    left right sameCell sameProfile sameRole distinct

/-- The collapse theorem stated at the complete endpoint-profile level. -/
theorem PrivateWitnessConstraintPopulation.completeEndpointStandingProfile_eq
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : PrivateWitnessConstraintPopulation noSunflower corpus)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameCell :
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩)
    (sameProfile :
      Population.constraintProfile left = Population.constraintProfile right)
    (sameRole : Population.forcedRole left = Population.forcedRole right) :
    MinimalBlocker.globalEndpointIncidenceProfile F left =
      MinimalBlocker.globalEndpointIncidenceProfile F right := by
  rw [Population.withinCellTensorMultiplicityCollapse
    left right sameCell sameProfile sameRole]

/--
Kernel-first population package. The live endpoint act licenses meaningful
identity and sameness before finite type exhaustion is invoked.
-/
structure KernelFirstPrivateWitnessConstraintPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (noSunflower : Not (Concrete.HasSunflower k F))
    (corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)) where
  endpointUse :
    LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)
      (fun G => Not (Concrete.HasSunflower k G))
  populate :
    forall license : KernelLicensedSameness
        (Concrete.concreteSunflowerCarrier alpha (r + 1) k),
      license.sameness ->
        PrivateWitnessConstraintPopulation noSunflower corpus

def KernelFirstPrivateWitnessConstraintPopulation.samenessLicense
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : KernelFirstPrivateWitnessConstraintPopulation
      noSunflower corpus) :
    KernelLicensedSameness
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k) :=
  corpus.samenessAtEndpointUse Population.endpointUse

theorem KernelFirstPrivateWitnessConstraintPopulation.samenessMeaningful
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : KernelFirstPrivateWitnessConstraintPopulation
      noSunflower corpus) :
    Population.samenessLicense.sameness := by
  exact Population.samenessLicense.sameness_holds

/--
Population is exposed only after the endpoint kernel has licensed meaningful
sameness. This is the type-level dependency gate for the exhaustion argument.
-/
def KernelFirstPrivateWitnessConstraintPopulation.population
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : KernelFirstPrivateWitnessConstraintPopulation
      noSunflower corpus) :
    PrivateWitnessConstraintPopulation noSunflower corpus :=
  Population.populate Population.samenessLicense Population.samenessMeaningful

/-- Kernel-licensed form of within-cell tensor multiplicity collapse. -/
theorem KernelFirstPrivateWitnessConstraintPopulation.withinCellTensorMultiplicityCollapse
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : KernelFirstPrivateWitnessConstraintPopulation
      noSunflower corpus)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameCell :
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩)
    (sameProfile :
      Population.population.constraintProfile left =
        Population.population.constraintProfile right)
    (sameRole :
      Population.population.forcedRole left =
        Population.population.forcedRole right) :
    left = right := by
  exact Population.population.withinCellTensorMultiplicityCollapse
    left right sameCell sameProfile sameRole

/--
The quantitative finite-index/factorization theorem specialized to concrete
private witnesses.  It says that every admitted edge-incidence consequence is
already determined by the coarse overlapping signature inside one
matching-support cell.  Constructing this object is the load-bearing bridge;
the finite corpus vocabulary alone does not construct it.
-/
structure PrivateWitnessConstraintFactorization
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (noSunflower : Not (Concrete.HasSunflower k F)) where
  constraintProfile :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      Finset ConstraintMapLevel
  forcedRole :
    {x // x ∈ MinimalBlocker.minimalBlocker F} -> AASCBlockerRole
  endpointIncidenceFactors :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩ ->
      constraintProfile left = constraintProfile right ->
      forcedRole left = forcedRole right ->
      MinimalBlocker.SameEndpointIncidence F left right

/--
Singleton realization of each fixed endpoint-role slot. This is stronger than
uniqueness of the endpoint classifier: it says that two minimal private
witnesses assigned the same support cell, constraint profile, and role are the
same realizer.
-/
structure PrivateWitnessEndpointRoleRealizerUniqueness
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (noSunflower : Not (Concrete.HasSunflower k F)) where
  constraintProfile :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      Finset ConstraintMapLevel
  forcedRole :
    {x // x ∈ MinimalBlocker.minimalBlocker F} -> AASCBlockerRole
  uniqueRealizer :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩ ->
      constraintProfile left = constraintProfile right ->
      forcedRole left = forcedRole right ->
      left = right

def PrivateWitnessEndpointRoleRealizerUniqueness.toFactorization
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Uniqueness :
      PrivateWitnessEndpointRoleRealizerUniqueness noSunflower) :
    PrivateWitnessConstraintFactorization noSunflower where
  constraintProfile := Uniqueness.constraintProfile
  forcedRole := Uniqueness.forcedRole
  endpointIncidenceFactors := by
    intro left right sameCell sameProfile sameRole
    have sameRealizer := Uniqueness.uniqueRealizer
      left right sameCell sameProfile sameRole
    subst right
    intro edge edge_mem
    exact Iff.rfl

noncomputable def PrivateWitnessConstraintFactorization.code
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Factorization : PrivateWitnessConstraintFactorization noSunflower) :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      VennSeparation.VennCellCode k constraintSignatureSize :=
  fun x =>
    (BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
      ⟨x.val, MinimalBlocker.minimalBlocker_subset_raw F x.property⟩,
      constraintSignatureEquivFin
        (Factorization.constraintProfile x, Factorization.forcedRole x))

theorem PrivateWitnessConstraintFactorization.globalProfile_eq_of_code_eq
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Factorization : PrivateWitnessConstraintFactorization noSunflower)
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (sameCode : Factorization.code left = Factorization.code right) :
    MinimalBlocker.globalEndpointIncidenceProfile F left =
      MinimalBlocker.globalEndpointIncidenceProfile F right := by
  have sameCell := congrArg Prod.fst sameCode
  have sameSignatureCode := congrArg Prod.snd sameCode
  have sameSignature :
      (Factorization.constraintProfile left, Factorization.forcedRole left) =
        (Factorization.constraintProfile right, Factorization.forcedRole right) :=
    constraintSignatureEquivFin.injective sameSignatureCode
  have sameIncidence := Factorization.endpointIncidenceFactors
    left right sameCell
    (congrArg Prod.fst sameSignature)
    (congrArg Prod.snd sameSignature)
  funext edge
  exact propext (sameIncidence edge.val edge.property)

theorem PrivateWitnessConstraintFactorization.code_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Factorization : PrivateWitnessConstraintFactorization noSunflower) :
    Function.Injective Factorization.code := by
  intro left right sameCode
  exact MinimalBlocker.globalEndpointIncidenceProfile_injective F <|
    Factorization.globalProfile_eq_of_code_eq sameCode

theorem PrivateWitnessConstraintFactorization.minimalBlocker_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Factorization : PrivateWitnessConstraintFactorization noSunflower) :
    (MinimalBlocker.minimalBlocker F).card <=
      VennSeparation.vennAlphabetSize k constraintSignatureSize := by
  have card_le := Fintype.card_le_of_injective
    Factorization.code
    Factorization.code_injective
  simpa [VennSeparation.vennCellCode_card] using card_le

def PrivateWitnessConstraintFactorization.toPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Factorization : PrivateWitnessConstraintFactorization noSunflower) :
    PrivateWitnessConstraintPopulation noSunflower corpus where
  constraintProfile := Factorization.constraintProfile
  forcedRole := Factorization.forcedRole
  completeSignatureExhaustion := by
    intro left right sameCell sameProfile sameRole load
    exact False.elim <| load.not_sameEndpointIncidence <|
      Factorization.endpointIncidenceFactors
        left right sameCell sameProfile sameRole

def PrivateWitnessConstraintPopulation.toFactorization
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : PrivateWitnessConstraintPopulation noSunflower corpus) :
    PrivateWitnessConstraintFactorization noSunflower where
  constraintProfile := Population.constraintProfile
  forcedRole := Population.forcedRole
  endpointIncidenceFactors := by
    intro left right sameCell sameProfile sameRole
    apply Classical.byContradiction
    intro distinctProfile
    have distinct : left ≠ right := by
      intro same
      subst right
      exact distinctProfile <| by
        intro edge edge_mem
        exact Iff.rfl
    rcases Population.completeSignatureExhaustion
        left right sameCell sameProfile sameRole
          (MinimalBlocker.privateWitnessEndpointLoadOfDistinct
            F left right distinct) with
      ⟨factor, independent⟩
    exact corpus.fixedDomainClosure.excludesIndependentAuthorizer
      factor independent

def PrivateWitnessEndpointRoleRealizerUniqueness.toPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Uniqueness :
      PrivateWitnessEndpointRoleRealizerUniqueness noSunflower) :
    PrivateWitnessConstraintPopulation noSunflower corpus :=
  Uniqueness.toFactorization.toPopulation

def PrivateWitnessConstraintPopulation.toEndpointRoleRealizerUniqueness
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : PrivateWitnessConstraintPopulation noSunflower corpus) :
    PrivateWitnessEndpointRoleRealizerUniqueness noSunflower where
  constraintProfile := Population.constraintProfile
  forcedRole := Population.forcedRole
  uniqueRealizer := Population.withinCellTensorMultiplicityCollapse

/--
Compatibility equivalence between the two older hybrid bundles. Both sides
already carry the same combinatorially supplied profile and role classifiers;
the theorem only interconverts their collision clauses. It does not derive a
candidate ledger from AASC uniqueness.
-/
theorem nonempty_endpointRoleRealizerUniqueness_iff_population
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)} :
    Nonempty (PrivateWitnessEndpointRoleRealizerUniqueness noSunflower) <->
      Nonempty (PrivateWitnessConstraintPopulation noSunflower corpus) := by
  constructor
  case mp =>
    intro Uniqueness
    exact ⟨Uniqueness.some.toPopulation⟩
  case mpr =>
    intro Population
    exact ⟨Population.some.toEndpointRoleRealizerUniqueness⟩

def KernelFirstPrivateWitnessConstraintPopulation.toFactorization
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : KernelFirstPrivateWitnessConstraintPopulation
      noSunflower corpus) :
    PrivateWitnessConstraintFactorization noSunflower :=
  Population.population.toFactorization

noncomputable def PrivateWitnessConstraintPopulation.toMinimalPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : PrivateWitnessConstraintPopulation noSunflower corpus) :
    BlockerSupportLayers.MinimalCorpusSupportFiberPopulation
      (fiberBound := constraintSignatureSize) noSunflower corpus where
  fiberSlot := fun x => constraintSignatureEquivFin
    (Population.constraintProfile x, Population.forcedRole x)
  skinEquivalent := MinimalBlocker.SameEndpointIncidence F
  nonSkinSameCellSlotCreatesIndependentAuthorizer := by
    intro left right sameCell sameSlot nonSkin
    have distinct : left ≠ right := by
      intro same
      subst right
      exact nonSkin <| by
        intro edge edge_mem
        exact Iff.rfl
    have sameSignature :
        (Population.constraintProfile left, Population.forcedRole left) =
          (Population.constraintProfile right, Population.forcedRole right) :=
      constraintSignatureEquivFin.injective sameSlot
    exact Population.completeSignatureExhaustion
      left right sameCell
      (congrArg Prod.fst sameSignature)
      (congrArg Prod.snd sameSignature)
      (MinimalBlocker.privateWitnessEndpointLoadOfDistinct
        F left right distinct)
  skinFinality := MinimalBlocker.eq_of_sameEndpointIncidence F

/--
The rank-uniform generative half.  For fixed `k` and a fixed bound,
combinatorics constructs a finite candidate ledger and realizes every minimal
private witness at every rank.  There is deliberately no AASC corpus argument
and no collision-completeness field here, so this source alone is not a
closure theorem.
-/
structure RankUniformPrivateWitnessCombinatorialCandidateSource
    (alpha : Type)
    [DecidableEq alpha]
    (k candidateBound : Nat) where
  realize :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
        PrivateWitnessCombinatorialCandidateRealization
          candidateBound noSunflower

/--
The actual generate-then-eliminate frontier.  `candidates` is the strictly
combinatorial input.  `collisionSieve` does not generate a code or assert that
a slot is occupied; it proves that collisions in the supplied code exhaust
into identity or the fixed-domain-impossible standing branch.
-/
structure RankUniformPrivateWitnessCandidateClosureSource
    (alpha : Type)
    [DecidableEq alpha]
    (k candidateBound : Nat)
    (k_nondegenerate : 3 <= k) where
  candidates :
    RankUniformPrivateWitnessCombinatorialCandidateSource
      alpha k candidateBound
  collisionSieve :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
        PrivateWitnessAASCCandidateCollisionSieve
          (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
            alpha k k_nondegenerate r)
          (candidates.realize r F noSunflower)

/-- The paired source yields the promised rank-uniform blocker bound. -/
theorem RankUniformPrivateWitnessCandidateClosureSource.minimalBlocker_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {k candidateBound : Nat}
    {k_nondegenerate : 3 <= k}
    (Source : RankUniformPrivateWitnessCandidateClosureSource
      alpha k candidateBound k_nondegenerate)
    (r : Nat)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    (MinimalBlocker.minimalBlocker F).card <= candidateBound := by
  exact (Source.collisionSieve r F noSunflower).minimalBlocker_card_le

/--
The density-corrected generative half. A candidate ledger is requested only
when the current family already violates the proposed power bound; sparse
families close without literal blocker compression.
-/
structure DenseRankUniformPrivateWitnessCombinatorialCandidateSource
    (alpha : Type)
    [DecidableEq alpha]
    (k candidateBound : Nat) where
  realize :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      candidateBound ^ (r + 1) < F.edges.card ->
        PrivateWitnessCombinatorialCandidateRealization
          candidateBound noSunflower

/--
The valid rank-uniform generate-then-eliminate source. Combinatorics populates
one fixed finite ledger only in a dense countercase; AASC then exhausts every
collision in that supplied ledger.
-/
structure DenseRankUniformPrivateWitnessCandidateClosureSource
    (alpha : Type)
    [DecidableEq alpha]
    (k candidateBound : Nat)
    (k_nondegenerate : 3 <= k) where
  candidates :
    DenseRankUniformPrivateWitnessCombinatorialCandidateSource
      alpha k candidateBound
  collisionSieve :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      forall sizeExcess : candidateBound ^ (r + 1) < F.edges.card,
        PrivateWitnessAASCCandidateCollisionSieve
          (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
            alpha k k_nondegenerate r)
          (candidates.realize r F noSunflower sizeExcess)

/-- The dense paired source gives exactly the blocker needed by the recurrence. -/
theorem DenseRankUniformPrivateWitnessCandidateClosureSource.minimalBlocker_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {k candidateBound : Nat}
    {k_nondegenerate : 3 <= k}
    (Source : DenseRankUniformPrivateWitnessCandidateClosureSource
      alpha k candidateBound k_nondegenerate)
    (r : Nat)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (sizeExcess : candidateBound ^ (r + 1) < F.edges.card) :
    (MinimalBlocker.minimalBlocker F).card <= candidateBound := by
  exact (Source.collisionSieve r F noSunflower sizeExcess).minimalBlocker_card_le

/-- The rejected all-family source restricts to the valid dense source. -/
def RankUniformPrivateWitnessCandidateClosureSource.toDenseSource
    {alpha : Type}
    [DecidableEq alpha]
    {k candidateBound : Nat}
    {k_nondegenerate : 3 <= k}
    (Source : RankUniformPrivateWitnessCandidateClosureSource
      alpha k candidateBound k_nondegenerate) :
    DenseRankUniformPrivateWitnessCandidateClosureSource
      alpha k candidateBound k_nondegenerate where
  candidates :=
    { realize := fun r F noSunflower _sizeExcess =>
        Source.candidates.realize r F noSunflower }
  collisionSieve := fun r F noSunflower _sizeExcess =>
    Source.collisionSieve r F noSunflower

/-- Rank-uniform population by the fixed six-level corpus map. -/
structure RankUniformConstraintProfileSource
    (alpha : Type)
    [DecidableEq alpha]
    (k : Nat)
    (k_nondegenerate : 3 <= k) where
  populate :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      PrivateWitnessConstraintPopulation
        noSunflower
        (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
          alpha k k_nondegenerate r)

/-- Rank-uniform quantitative factorization through the finite coarse map. -/
structure RankUniformConstraintFactorizationSource
    (alpha : Type)
    [DecidableEq alpha]
    (k : Nat)
    (k_nondegenerate : 3 <= k) where
  factorize :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      PrivateWitnessConstraintFactorization noSunflower

/--
The dependency-corrected source: factorization is required only for a family
that already violates the proposed constant-base bound.
-/
structure DenseCountercaseConstraintFactorizationSource
    (alpha : Type)
    [DecidableEq alpha]
    (k : Nat)
    (k_nondegenerate : 3 <= k) where
  factorize :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      (VennSeparation.vennAlphabetSize k constraintSignatureSize) ^ (r + 1) <
          F.edges.card ->
        PrivateWitnessConstraintFactorization noSunflower

def RankUniformConstraintFactorizationSource.toProfileSource
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : RankUniformConstraintFactorizationSource
      alpha k k_nondegenerate) :
    RankUniformConstraintProfileSource alpha k k_nondegenerate where
  populate := fun r F noSunflower =>
    (Src.factorize r F noSunflower).toPopulation

noncomputable def RankUniformConstraintProfileSource.toCorpusFiberSource
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : RankUniformConstraintProfileSource alpha k k_nondegenerate) :
    BlockerSupportLayers.RankUniformCorpusSupportFiberSource
      alpha k constraintSignatureSize k_nondegenerate where
  fiberBound_positive := by decide
  assign := fun r F noSunflower =>
    (Src.populate r F noSunflower).toMinimalPopulation

def corpusConstraintBase (k : Nat) : Nat :=
  VennSeparation.vennAlphabetSize k constraintSignatureSize

theorem corpusConstraintBase_eq (k : Nat) :
    corpusConstraintBase k = 2 ^ k * 256 := by
  simp [corpusConstraintBase, VennSeparation.vennAlphabetSize,
    constraintSignatureSize_eq]

noncomputable def DenseCountercaseConstraintFactorizationSource.toDenseBlockerSource
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseCountercaseConstraintFactorizationSource
      alpha k k_nondegenerate) :
    EffectiveBlocker.DenseCountercaseSource
      alpha k (corpusConstraintBase k) where
  certificate := by
    intro r F noSunflower sizeExcess
    let Factorization := Src.factorize r F noSunflower sizeExcess
    exact
      { blocker := MinimalBlocker.minimalBlocker F
        blocker_card_le := Factorization.minimalBlocker_card_le
        hitsEveryEdge := by
          intro edge edge_mem
          rcases Finset.not_disjoint_iff.mp
              (MinimalBlocker.minimalBlocker_hitsEveryEdge F edge edge_mem) with
            ⟨x, x_edge, x_blocker⟩
          exact ⟨x, x_blocker, x_edge⟩ }

/--
The existing dense six-level/four-role factorization decomposes into the
dependency-correct candidate generator and AASC collision sieve.
-/
noncomputable def
    DenseCountercaseConstraintFactorizationSource.toDenseCandidateClosureSource
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseCountercaseConstraintFactorizationSource
      alpha k k_nondegenerate) :
    DenseRankUniformPrivateWitnessCandidateClosureSource
      alpha k (corpusConstraintBase k) k_nondegenerate where
  candidates :=
    { realize := by
        intro r F noSunflower sizeExcess
        let Population : PrivateWitnessConstraintPopulation noSunflower
            (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
              alpha k k_nondegenerate r) :=
          (Src.factorize r F noSunflower sizeExcess).toPopulation
        exact Population.candidateRealization }
  collisionSieve := by
    intro r F noSunflower sizeExcess
    let Population : PrivateWitnessConstraintPopulation noSunflower
        (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
          alpha k k_nondegenerate r) :=
      (Src.factorize r F noSunflower sizeExcess).toPopulation
    exact Population.toCandidateCollisionSieve

theorem sunflower_of_constraintMapPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : RankUniformConstraintProfileSource alpha k k_nondegenerate)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess : corpusConstraintBase k ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  exact BlockerSupportLayers.sunflower_of_corpusSupportFiberCompression
    Src.toCorpusFiberSource F sizeExcess

theorem sunflower_of_constraintMapFactorization
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : RankUniformConstraintFactorizationSource
      alpha k k_nondegenerate)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess : corpusConstraintBase k ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  exact sunflower_of_constraintMapPopulation
    Src.toProfileSource F sizeExcess

theorem sunflower_of_dense_constraintMapFactorization
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseCountercaseConstraintFactorizationSource
      alpha k k_nondegenerate)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess : corpusConstraintBase k ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  exact EffectiveBlocker.sunflower_of_card_gt_pow_of_denseCountercaseSource
    Src.toDenseBlockerSource F sizeExcess

end ConstraintMapPopulation
end V2
end SunflowerAASC
