import MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.V22PaperStatements
import SunflowerAASC.V2.CorpusMachinery

namespace SunflowerAASC
namespace V2
namespace MechanizedKernelImport

open MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction

/--
Translate one determinate sunflower endpoint use into the construction-regime
surface of the separately mechanized admissibility-kernel repository.
-/
def endpointConstructionRegime
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (corpus : KernelFirstCorpusMachinery S) :
    ConstructionRegime S.Family S.Family :=
  let kernel := corpus.kernelAtEndpointUse endpointUse
  { target := fun family => family
    sameTarget := fun left right => left = right
    admissible := fun _ => kernel.admissibility
    standing := fun _ => kernel.standing
    referenceFixed := fun _ => kernel.reference
    irreversibleFailure := fun _ => kernel.irreversibility
    licensedContinuation := fun _ _ => True
    targetIdentityFixed := endpointUse.targetFixed /\ endpointUse.carrierFixed
    stepEligibilityFixed := endpointUse.branchRoleFixed
    actTimeFailureStable := endpointUse.lawfulActTimeBoundary
    boundaryFixed := kernel.admissibility
    governedConstructionUse := endpointUse.reportable /\ endpointUse.downstreamReusable
    noRawTraceSuffices := endpointUse.branchRoleFixed
    noSelectorImport :=
      forall factor : S.StandingFactor,
        Not (corpus.fixedDomainClosure.disposition factor =
          SameScopeFactorDisposition.independentAuthorizer)
    noDomainShift := endpointUse.carrierFixed
    noBookkeepingOnly := endpointUse.reportable }

/-- The translated regime has the determinate target phenomenon of the kernel paper. -/
theorem endpointConstructionRegime_targetPhenomenon
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (corpus : KernelFirstCorpusMachinery S) :
    TargetPhenomenon
      (endpointConstructionRegime endpointUse corpus) := by
  exact
    And.intro
      (And.intro endpointUse.targetFixed_holds endpointUse.carrierFixed_holds)
      (And.intro endpointUse.branchRoleFixed_holds
        (And.intro endpointUse.lawfulActTimeBoundary_holds
          (And.intro endpointUse.reportable_holds
            endpointUse.downstreamReusable_holds)))

/-- The four live sunflower roles instantiate the mechanized kernel package. -/
theorem endpointConstructionRegime_kernelPackage
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (corpus : KernelFirstCorpusMachinery S) :
    MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.KernelPackage
      (endpointConstructionRegime endpointUse corpus) := by
  let kernel := corpus.kernelAtEndpointUse endpointUse
  exact
    PaperConstructionForcesKernelStatement
      (endpointConstructionRegime endpointUse corpus)
      kernel.admissibility_holds
      (by
        intro _ _
        exact kernel.admissibility_holds)
      (by
        intro _
        exact kernel.reference_holds)
      (by
        intro _
        exact kernel.irreversibility_holds)

/-- The concrete no-selector ledger populates the kernel paper's fixed-domain packet. -/
theorem endpointConstructionRegime_fixedDomainClosure
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (corpus : KernelFirstCorpusMachinery S) :
    FixedDomainClosurePacket
      (endpointConstructionRegime endpointUse corpus) := by
  let kernel := corpus.kernelAtEndpointUse endpointUse
  apply PaperFixedDomainClosurePacketStatement
  · intro _
    exact Or.inl kernel.admissibility_holds
  · intro factor
    exact corpus.fixedDomainClosure.noIndependentAuthorizer factor
  · intro _
    constructor
    · intro standing
      exact
        And.intro standing (by
          intro _ _
          exact kernel.admissibility_holds)
    · intro reuseStable
      exact reuseStable.1
  · intro P Q hP hQ act
    exact (hP act).trans (hQ act).symm
  · intro _ _ notStanding _
    exact False.elim (notStanding kernel.standing_holds)

/-- Fixed-domain uniqueness is imported at the kernel repository's exact type. -/
theorem endpointConstructionRegime_kernelUnique
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (corpus : KernelFirstCorpusMachinery S) :
    KernelUniqueOnFixedDomain
      (endpointConstructionRegime endpointUse corpus) := by
  apply PaperKernelUniquenessOnFixedDomainStatement
  intro alternative realization
  exact realization.2.2

/--
The executable cross-repository dependency certificate.  It records what the
kernel import proves and deliberately contains no sunflower population field.
-/
structure MechanizedKernelDependencyCertificate
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (corpus : KernelFirstCorpusMachinery S) : Prop where
  targetPhenomenon :
    TargetPhenomenon
      (endpointConstructionRegime endpointUse corpus)
  kernelPackage :
    MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.KernelPackage
      (endpointConstructionRegime endpointUse corpus)
  fixedDomainClosure :
    FixedDomainClosurePacket
      (endpointConstructionRegime endpointUse corpus)
  fixedDomainUniqueness :
    KernelUniqueOnFixedDomain
      (endpointConstructionRegime endpointUse corpus)
  noDerivationBelow :
    NoDerivationBelowKernel
      (endpointConstructionRegime endpointUse corpus)
  noFaithfulLowerGenerator :
    Not (FaithfulLowerGenerator
      (endpointConstructionRegime endpointUse corpus))
  globalSynthesis :
    KernelGlobalSynthesisUnderCorpusClosures
      (endpointConstructionRegime endpointUse corpus)

/-- Construct the certificate using the separately mechanized kernel theorems. -/
def mechanizedKernelDependencyCertificate
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (corpus : KernelFirstCorpusMachinery S) :
    MechanizedKernelDependencyCertificate endpointUse corpus := by
  let kernelPackage :=
    endpointConstructionRegime_kernelPackage endpointUse corpus
  let fixedDomainClosure :=
    endpointConstructionRegime_fixedDomainClosure endpointUse corpus
  let fixedDomainUniqueness :=
    endpointConstructionRegime_kernelUnique endpointUse corpus
  exact
    { targetPhenomenon :=
        endpointConstructionRegime_targetPhenomenon endpointUse corpus
      kernelPackage := kernelPackage
      fixedDomainClosure := fixedDomainClosure
      fixedDomainUniqueness := fixedDomainUniqueness
      noDerivationBelow :=
        PaperNothingDerivableBelowKernelStatement
          (endpointConstructionRegime endpointUse corpus)
          kernelPackage
      noFaithfulLowerGenerator :=
        PaperNoFaithfulLowerGeneratorStatement
          (endpointConstructionRegime endpointUse corpus)
          kernelPackage
      globalSynthesis :=
        PaperGlobalSynthesisUnderCorpusClosuresClosedStatement
          (endpointConstructionRegime endpointUse corpus)
          kernelPackage
          fixedDomainClosure
          fixedDomainUniqueness }

/-- Any same-domain governance-equivalent replacement inherits the kernel. -/
theorem governanceEquivalentReplacement_hasKernel
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    {corpus : KernelFirstCorpusMachinery S}
    (certificate : MechanizedKernelDependencyCertificate endpointUse corpus)
    (alternative : ConstructionRegime S.Family S.Family)
    (equivalent : GovernanceEquivalent
      (endpointConstructionRegime endpointUse corpus) alternative) :
    MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.KernelPackage
      alternative :=
  PaperKernelPackageTransfersAcrossGovernanceEquivalenceStatement
    (endpointConstructionRegime endpointUse corpus)
    alternative
    certificate.kernelPackage
    equivalent

end MechanizedKernelImport
end V2
end SunflowerAASC
