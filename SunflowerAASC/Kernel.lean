import SunflowerAASC.Basic

namespace SunflowerAASC

/-- Kernel package forced by target adequacy on a nondegenerate endpoint act. -/
structure KernelPackage (S : SunflowerCarrier) where
  admissibility : Prop
  standing : Prop
  reference : Prop
  irreversibility : Prop
  admissibility_holds : admissibility
  standing_holds : standing
  reference_holds : reference
  irreversibility_holds : irreversibility

def KernelPackage.allRolesHold
    {S : SunflowerCarrier}
    (K : KernelPackage S) : Prop :=
  K.admissibility /\ K.standing /\ K.reference /\ K.irreversibility

theorem KernelPackage.allRolesHold_holds
    {S : SunflowerCarrier}
    (K : KernelPackage S) :
    K.allRolesHold := by
  exact
    And.intro K.admissibility_holds
      (And.intro K.standing_holds
        (And.intro K.reference_holds K.irreversibility_holds))

/--
Identity and sameness are licensed only downstream of the nondegenerate kernel.
This packages the manuscript's dependency direction at the type level.
-/
structure KernelLicensedSameness (S : SunflowerCarrier) where
  kernel : KernelPackage S

def KernelLicensedSameness.determinacy
    {S : SunflowerCarrier}
    (L : KernelLicensedSameness S) : Prop :=
  L.kernel.allRolesHold

def KernelLicensedSameness.identity
    {S : SunflowerCarrier}
    (L : KernelLicensedSameness S) : Prop :=
  L.kernel.standing /\ L.kernel.reference

def KernelLicensedSameness.comparison
    {S : SunflowerCarrier}
    (L : KernelLicensedSameness S) : Prop :=
  L.kernel.admissibility /\ L.identity

def KernelLicensedSameness.sameness
    {S : SunflowerCarrier}
    (L : KernelLicensedSameness S) : Prop :=
  L.comparison /\ L.kernel.irreversibility

theorem KernelLicensedSameness.determinacy_holds
    {S : SunflowerCarrier}
    (L : KernelLicensedSameness S) :
    L.determinacy :=
  L.kernel.allRolesHold_holds

theorem KernelLicensedSameness.identity_holds
    {S : SunflowerCarrier}
    (L : KernelLicensedSameness S) :
    L.identity :=
  ⟨L.kernel.standing_holds, L.kernel.reference_holds⟩

theorem KernelLicensedSameness.comparison_holds
    {S : SunflowerCarrier}
    (L : KernelLicensedSameness S) :
    L.comparison :=
  ⟨L.kernel.admissibility_holds, L.identity_holds⟩

theorem KernelLicensedSameness.sameness_holds
    {S : SunflowerCarrier}
    (L : KernelLicensedSameness S) :
    L.sameness :=
  ⟨L.comparison_holds, L.kernel.irreversibility_holds⟩

/-- A classifier has a singleton positive fiber when any two positive states coincide. -/
def PositiveFiberIsSingleton
    {State : Type}
    (classifier : State -> Prop) : Prop :=
  forall left right : State,
    classifier left -> classifier right -> left = right

/--
Extensional uniqueness of same-domain classifier authority. This fixes which
predicate governs a domain; it does not assert that the predicate is positive
on only one state.
-/
structure SameDomainClassifierUniqueness (State : Type) where
  lawful : (State -> Prop) -> Prop
  classifier : State -> Prop
  classifier_lawful : lawful classifier
  uniqueClassifier :
    forall other : State -> Prop, lawful other -> other = classifier

theorem SameDomainClassifierUniqueness.agreesWithLawfulClassifier
    {State : Type}
    (U : SameDomainClassifierUniqueness State)
    (other : State -> Prop)
    (lawful : U.lawful other) :
    other = U.classifier := by
  exact U.uniqueClassifier other lawful

/-- A concrete unique classifier whose positive interior contains two states. -/
def twoPointAllPositiveClassifierUniqueness :
    SameDomainClassifierUniqueness (Fin 2) where
  lawful := fun classifier => classifier = fun _ => True
  classifier := fun _ => True
  classifier_lawful := rfl
  uniqueClassifier := by
    intro other lawful
    exact lawful

/--
Classifier uniqueness does not logically imply singleton realization. The
distinction prevents unique admissible-interior results from being used as
unproved cardinality-one claims about the interior's members.
-/
theorem uniqueClassifier_doesNotForceSingletonPositiveFiber :
    Not (PositiveFiberIsSingleton
      twoPointAllPositiveClassifierUniqueness.classifier) := by
  intro singleton
  have equal : (0 : Fin 2) = 1 :=
    singleton 0 1 trivial trivial
  exact (by decide : Not ((0 : Fin 2) = 1)) equal

/--
The manuscript's "target adequacy forces kernel" link, packaged as a reusable
governance rule for all local endpoint branches on the same carrier.
-/
structure KernelForcedGovernance (S : SunflowerCarrier) where
  targetAdequacyForcesKernel :
    forall {branch : S.Family -> Prop},
      LocalEndpointUse S branch ->
      KernelPackage S
  noIndependentDiscriminator :
    forall {branch positive : S.Family -> Prop},
      LocalEndpointUse S branch ->
      IndependentDiscriminator S branch positive ->
      False

def targetAdequacy_forces_kernel
    {S : SunflowerCarrier}
    (G : KernelForcedGovernance S)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    KernelPackage S := by
  exact G.targetAdequacyForcesKernel U

theorem local_endpoint_use_excludes_independent_discriminator
    {S : SunflowerCarrier}
    (G : KernelForcedGovernance S)
    {branch positive : S.Family -> Prop}
    (U : LocalEndpointUse S branch)
    (D : IndependentDiscriminator S branch positive) :
    False := by
  exact G.noIndependentDiscriminator U D

/--
Upstream instantiation of the corpus kernel-necessity theorem for a
nondegenerate determinate endpoint carrier.  Domain-specific combinatorics may
populate witnesses used by the endpoint proof, but it is not the source of the
kernel roles: every standing-bearing local endpoint use receives its kernel
package from `governance`.

This is the sunflower specialization of the corpus realism claim: the kernel is
a necessity condition of determinate endpoint use, not an optional interpretive
overlay added after an independently complete endpoint has been specified.
-/
structure DeterminateEndpointKernelSource (S : SunflowerCarrier) where
  governance : KernelForcedGovernance S
  carrierNondegenerate : S.nondegenerate

def DeterminateEndpointKernelSource.kernelAtEndpointUse
    {S : SunflowerCarrier}
    (K : DeterminateEndpointKernelSource S)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    KernelPackage S :=
  targetAdequacy_forces_kernel K.governance U

theorem DeterminateEndpointKernelSource.kernelRolesHoldAtEndpointUse
    {S : SunflowerCarrier}
    (K : DeterminateEndpointKernelSource S)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    (K.kernelAtEndpointUse U).allRolesHold := by
  exact (K.kernelAtEndpointUse U).allRolesHold_holds

theorem DeterminateEndpointKernelSource.excludesIndependentDiscriminator
    {S : SunflowerCarrier}
    (K : DeterminateEndpointKernelSource S)
    {branch positive : S.Family -> Prop}
    (U : LocalEndpointUse S branch)
    (D : IndependentDiscriminator S branch positive) :
    False := by
  exact K.governance.noIndependentDiscriminator U D

/--
The corpus-level standing-factor ledger.  Same-side refinement is explicit and
therefore cannot be collapsed into the independent-authorizer case.
-/
inductive SameScopeFactorDisposition where
  | bookkeeping
  | gateEquivalent
  | sameSideRefinement
  | scopeChange
  | independentAuthorizer
deriving DecidableEq, Repr

/-- Kernel necessity only; no fixed-domain A+ exclusion is smuggled into it. -/
structure KernelNecessitySource (S : SunflowerCarrier) where
  carrierNondegenerate : S.nondegenerate
  kernelAtEndpointUse :
    forall {branch : S.Family -> Prop},
      LocalEndpointUse S branch -> KernelPackage S

/--
Separate imported consequence of the wider corpus machinery.  It classifies
the fixed carrier's standing factors and excludes the independent-authorizer
disposition.  This is not derived from the four labels of `KernelPackage`
alone.
-/
structure FixedDomainAPlusClosureSource (S : SunflowerCarrier) where
  disposition : S.StandingFactor -> SameScopeFactorDisposition
  noIndependentAuthorizer :
    forall factor : S.StandingFactor,
      Not (
        disposition factor =
          SameScopeFactorDisposition.independentAuthorizer)

/-- Correct dependency bundle: kernel necessity first, corpus closure second. -/
structure KernelFirstCorpusMachinery (S : SunflowerCarrier) where
  kernelNecessity : KernelNecessitySource S
  fixedDomainClosure : FixedDomainAPlusClosureSource S

def KernelFirstCorpusMachinery.kernelAtEndpointUse
    {S : SunflowerCarrier}
    (K : KernelFirstCorpusMachinery S)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    KernelPackage S :=
  K.kernelNecessity.kernelAtEndpointUse U

def KernelFirstCorpusMachinery.samenessAtEndpointUse
    {S : SunflowerCarrier}
    (K : KernelFirstCorpusMachinery S)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    KernelLicensedSameness S where
  kernel := K.kernelAtEndpointUse U

theorem KernelFirstCorpusMachinery.samenessMeaningfulAtEndpointUse
    {S : SunflowerCarrier}
    (K : KernelFirstCorpusMachinery S)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    (K.samenessAtEndpointUse U).sameness := by
  exact (K.samenessAtEndpointUse U).sameness_holds

theorem KernelFirstCorpusMachinery.kernelRolesHoldAtEndpointUse
    {S : SunflowerCarrier}
    (K : KernelFirstCorpusMachinery S)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    (K.kernelAtEndpointUse U).allRolesHold := by
  exact (K.kernelAtEndpointUse U).allRolesHold_holds

theorem FixedDomainAPlusClosureSource.excludesIndependentAuthorizer
    {S : SunflowerCarrier}
    (A : FixedDomainAPlusClosureSource S)
    (factor : S.StandingFactor)
    (independent :
      A.disposition factor = SameScopeFactorDisposition.independentAuthorizer) :
    False := by
  exact A.noIndependentAuthorizer factor independent

/-- Fixed-domain AASC consequence layer used by the hardened manuscript recap. -/
structure AASCConsequenceLayer (S : SunflowerCarrier) where
  endpointBivalence : Prop
  noSelectorImport : Prop
  uniqueAdmissibleInterior : Prop
  noSameActRepair : Prop
  noCarrierTransfer : Prop
  reportPreservation : Prop
  noIndependentDiscriminatorConsequence :
    forall {branch positive : S.Family -> Prop},
      LocalEndpointUse S branch ->
      IndependentDiscriminator S branch positive ->
      False
  endpointBivalence_holds : endpointBivalence
  noSelectorImport_holds : noSelectorImport
  uniqueAdmissibleInterior_holds : uniqueAdmissibleInterior
  noSameActRepair_holds : noSameActRepair
  noCarrierTransfer_holds : noCarrierTransfer
  reportPreservation_holds : reportPreservation

def AASCConsequenceLayer.recapSurfaceComplete
    {S : SunflowerCarrier}
    (L : AASCConsequenceLayer S) : Prop :=
  L.endpointBivalence /\
  L.noSelectorImport /\
  L.uniqueAdmissibleInterior /\
  L.noSameActRepair /\
  L.noCarrierTransfer /\
  L.reportPreservation

theorem AASCConsequenceLayer.recapSurfaceComplete_holds
    {S : SunflowerCarrier}
    (L : AASCConsequenceLayer S) :
    L.recapSurfaceComplete := by
  exact
    And.intro L.endpointBivalence_holds
      (And.intro L.noSelectorImport_holds
        (And.intro L.uniqueAdmissibleInterior_holds
          (And.intro L.noSameActRepair_holds
            (And.intro L.noCarrierTransfer_holds
              L.reportPreservation_holds))))

theorem AASCConsequenceLayer.excludes_independent_discriminator
    {S : SunflowerCarrier}
    (L : AASCConsequenceLayer S)
    {branch positive : S.Family -> Prop}
    (U : LocalEndpointUse S branch)
    (D : IndependentDiscriminator S branch positive) :
    False := by
  exact L.noIndependentDiscriminatorConsequence U D

/-- Typed cost ledger for denying one kernel role while preserving endpoint use. -/
structure KernelDenialCost (S : SunflowerCarrier) where
  deniedRole : KernelRole
  destroysFixedTargetOrCarrier : Prop
  destroysStandingForce : Prop
  importsExternalSelectorOrRepair : Prop
  changesEndpointAct : Prop
  costIsExhaustive :
    destroysFixedTargetOrCarrier \/
    destroysStandingForce \/
    importsExternalSelectorOrRepair \/
    changesEndpointAct

def KernelDenialCost.isRealCost
    {S : SunflowerCarrier}
    (C : KernelDenialCost S) : Prop :=
  C.destroysFixedTargetOrCarrier \/
    C.destroysStandingForce \/
      C.importsExternalSelectorOrRepair \/
        C.changesEndpointAct

theorem KernelDenialCost.isRealCost_holds
    {S : SunflowerCarrier}
    (C : KernelDenialCost S) :
    C.isRealCost := by
  exact C.costIsExhaustive

def no_third_position_under_kernel_forced_governance
    {S : SunflowerCarrier}
    (G : KernelForcedGovernance S)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    KernelPackage S := by
  exact targetAdequacy_forces_kernel G U

end SunflowerAASC
