import SunflowerAASC.V2.GeneratedTerminalKernelGovernance
import SunflowerAASC.V2.MechanizedKernelImport
import SunflowerAASC.V2.TerminalRoleOccupancyCloseout

namespace SunflowerAASC
namespace V2
namespace KernelNecessityRoleOccupancy

open ExplicitReductionPotential
open FixedIdentityPopulation
open InternalTensorProfiles
open MechanizedKernelImport
open TerminalRoleOccupancyCloseout
open MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction

/-!
This module makes the dependency from kernel necessity to terminal role
occupancy explicit.

Combinatorics may generate five candidate dispositions for a same-identity
collision: skin, bounded certificate, tensor split, sunflower, or an attempted
independent authorizer. The mechanized fixed-domain kernel theorem removes the
fifth candidate. Canonical endpoint skin is quotient-final. Reduction
minimality then excludes the three remaining non-skin certificate branches.
Fixed identity is therefore downstream of:

* determinate endpoint adequacy and carrier nondegeneracy;
* the forced kernel package and licensed sameness;
* admissibility bivalence and fixed-domain closure;
* generated finite disposition witnesses; and
* literal reduction certificates.

Kernel necessity does not generate the combinatorial witnesses. It governs
their exhaustive use and makes the independent-authority escape impossible.
-/

/-- A canonical, role-sensitive cost for denying one of the four kernel roles. -/
def canonicalKernelDenialCost
    (S : SunflowerCarrier) :
    KernelRole -> KernelDenialCost S
  | .admissibility =>
      { deniedRole := .admissibility
        destroysFixedTargetOrCarrier := False
        destroysStandingForce := True
        importsExternalSelectorOrRepair := False
        changesEndpointAct := False
        costIsExhaustive := Or.inr (Or.inl trivial) }
  | .standing =>
      { deniedRole := .standing
        destroysFixedTargetOrCarrier := False
        destroysStandingForce := True
        importsExternalSelectorOrRepair := False
        changesEndpointAct := False
        costIsExhaustive := Or.inr (Or.inl trivial) }
  | .reference =>
      { deniedRole := .reference
        destroysFixedTargetOrCarrier := True
        destroysStandingForce := False
        importsExternalSelectorOrRepair := False
        changesEndpointAct := False
        costIsExhaustive := Or.inl trivial }
  | .irreversibility =>
      { deniedRole := .irreversibility
        destroysFixedTargetOrCarrier := False
        destroysStandingForce := False
        importsExternalSelectorOrRepair := False
        changesEndpointAct := True
        costIsExhaustive := Or.inr (Or.inr (Or.inr trivial)) }

/-- Every canonical denial has a real typed endpoint cost. -/
theorem canonicalKernelDenialCost_isRealCost
    (S : SunflowerCarrier)
    (role : KernelRole) :
    (canonicalKernelDenialCost S role).isRealCost :=
  (canonicalKernelDenialCost S role).isRealCost_holds

/--
The complete necessity-rooted governance packet at one determinate endpoint.
There is no `kernelApplies` field: endpoint adequacy and nondegeneracy already
place the construction under kernel governance.
-/
structure NecessityRootedEndpointGovernance
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (corpus : KernelFirstCorpusMachinery S) : Prop where
  carrierNondegenerate : S.nondegenerate
  dependency :
    MechanizedKernelDependencyCertificate endpointUse corpus

/-- Construct necessity-rooted governance from the endpoint and corpus data. -/
def necessityRootedEndpointGovernance
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (corpus : KernelFirstCorpusMachinery S) :
    NecessityRootedEndpointGovernance endpointUse corpus where
  carrierNondegenerate := corpus.kernelNecessity.carrierNondegenerate
  dependency := mechanizedKernelDependencyCertificate endpointUse corpus

/--
Every combinatorially generated terminal incidence lands directly in a
necessity-rooted kernel-governed endpoint. No optional applicability bridge is
inserted between generation and governance.
-/
def generatedTerminalIncidence_governance
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (GeneratedSeedCapacity.InitialCarrier F)}
    (_incidence :
      GeneratedTerminalKernelGovernance.GeneratedTerminalIncidence F cell) :
    NecessityRootedEndpointGovernance
      (GeneratedTerminalKernelGovernance.terminalNoSunflowerEndpointUse
        alpha baseRank)
      (GeneratedTerminalKernelGovernance.terminalKernelFirstCorpusMachinery
        alpha baseRank) :=
  necessityRootedEndpointGovernance
    (GeneratedTerminalKernelGovernance.terminalNoSunflowerEndpointUse
      alpha baseRank)
    (GeneratedTerminalKernelGovernance.terminalKernelFirstCorpusMachinery
      alpha baseRank)

/-- Target adequacy is intrinsic to the live endpoint use. -/
theorem NecessityRootedEndpointGovernance.targetAdequacy
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    {corpus : KernelFirstCorpusMachinery S}
    (_Governance : NecessityRootedEndpointGovernance endpointUse corpus) :
    endpointUse.targetAdequate :=
  endpointUse.targetAdequate_holds

/-- All four local kernel roles are supplied by the necessity source. -/
theorem NecessityRootedEndpointGovernance.localKernelRoles
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    {corpus : KernelFirstCorpusMachinery S}
    (_Governance : NecessityRootedEndpointGovernance endpointUse corpus) :
    (corpus.kernelAtEndpointUse endpointUse).allRolesHold :=
  corpus.kernelRolesHoldAtEndpointUse endpointUse

/-- Meaningful sameness is downstream of those forced kernel roles. -/
theorem NecessityRootedEndpointGovernance.samenessMeaningful
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    {corpus : KernelFirstCorpusMachinery S}
    (_Governance : NecessityRootedEndpointGovernance endpointUse corpus) :
    (corpus.samenessAtEndpointUse endpointUse).sameness :=
  corpus.samenessMeaningfulAtEndpointUse endpointUse

/--
The attempted independent-authorizer branch is excluded by the mechanized
fixed-domain closure packet, not by an additional occupancy premise.
-/
theorem NecessityRootedEndpointGovernance.noIndependentAuthorizer
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    {corpus : KernelFirstCorpusMachinery S}
    (Governance : NecessityRootedEndpointGovernance endpointUse corpus)
    (factor : S.StandingFactor) :
    Not (corpus.fixedDomainClosure.disposition factor =
      SameScopeFactorDisposition.independentAuthorizer) :=
  Governance.dependency.fixedDomainClosure.2.1 factor

/-- Admissibility bivalence is a forced consequence of the kernel packet. -/
theorem NecessityRootedEndpointGovernance.admissibilityBivalent
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    {corpus : KernelFirstCorpusMachinery S}
    (Governance : NecessityRootedEndpointGovernance endpointUse corpus) :
    AdmissibilityBivalent
      (endpointConstructionRegime endpointUse corpus) :=
  (PaperNecessityAndBivalenceOfAdmissibilityStatement
    (endpointConstructionRegime endpointUse corpus)
    Governance.dependency.kernelPackage
    Governance.dependency.fixedDomainClosure).2

/-- The entire fixed-domain interface follows from the same kernel dependency. -/
theorem NecessityRootedEndpointGovernance.fixedDomainInterfaceShape
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    {corpus : KernelFirstCorpusMachinery S}
    (Governance : NecessityRootedEndpointGovernance endpointUse corpus) :
    FixedDomainInterfaceShape
      (endpointConstructionRegime endpointUse corpus) :=
  PaperFixedDomainInterfaceShapeStatement
    (endpointConstructionRegime endpointUse corpus)
    Governance.dependency.fixedDomainClosure

/-- No governance-faithful construction lies below the forced kernel. -/
theorem NecessityRootedEndpointGovernance.noDerivationBelowKernel
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    {corpus : KernelFirstCorpusMachinery S}
    (Governance : NecessityRootedEndpointGovernance endpointUse corpus) :
    NoDerivationBelowKernel
      (endpointConstructionRegime endpointUse corpus) :=
  Governance.dependency.noDerivationBelow

/-- A faithful lower generator is impossible on the same governed endpoint. -/
theorem NecessityRootedEndpointGovernance.noFaithfulLowerGenerator
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    {corpus : KernelFirstCorpusMachinery S}
    (Governance : NecessityRootedEndpointGovernance endpointUse corpus) :
    Not (FaithfulLowerGenerator
      (endpointConstructionRegime endpointUse corpus)) :=
  Governance.dependency.noFaithfulLowerGenerator

/-- The fixed-domain kernel synthesis theorem is available at the endpoint. -/
theorem NecessityRootedEndpointGovernance.globalSynthesis
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    {corpus : KernelFirstCorpusMachinery S}
    (Governance : NecessityRootedEndpointGovernance endpointUse corpus) :
    KernelGlobalSynthesisUnderCorpusClosures
      (endpointConstructionRegime endpointUse corpus) :=
  Governance.dependency.globalSynthesis

/--
The generated local population before fixed-domain kernel exclusion. A
same-identity collision may expose four lawful dispositions or attempt to
introduce an independent standing authorizer.
-/
structure KernelGovernedGeneratedFourRolePopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {branch : Concrete.UniformSetFamily alpha (r + 1) -> Prop}
    {endpointUse : LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k) branch}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Governance : NecessityRootedEndpointGovernance endpointUse corpus)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) where
  tensorProfileBound_positive : 0 < tensorProfileBound
  identityOf :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      RefinedConstraintSignature tensorProfileBound
  boundedCertificateOutcome :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  tensorSplitOutcome :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  sameIdentityCandidateExhaustive :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩ ->
      identityOf left = identityOf right ->
      MinimalBlocker.EndpointSkinEquivalent F left right ∨
        boundedCertificateOutcome left right ∨
        tensorSplitOutcome left right ∨
        Concrete.HasSunflower k F ∨
        Exists (fun factor :
          (Concrete.concreteSunflowerCarrier alpha (r + 1) k).StandingFactor =>
          corpus.fixedDomainClosure.disposition factor =
            SameScopeFactorDisposition.independentAuthorizer)

/--
Kernel necessity removes the attempted independent-authorizer branch, while
canonical endpoint skin supplies quotient finality. The result is the explicit
four-role population used by terminal closeout.
-/
def KernelGovernedGeneratedFourRolePopulation.toAASCFourRoleIdentityPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {branch : Concrete.UniformSetFamily alpha (r + 1) -> Prop}
    {endpointUse : LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k) branch}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    {Governance : NecessityRootedEndpointGovernance endpointUse corpus}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Population : KernelGovernedGeneratedFourRolePopulation
      (tensorProfileBound := tensorProfileBound)
      Governance F noSunflower) :
    AASCFourRoleIdentityPopulation
      (tensorProfileBound := tensorProfileBound) F noSunflower where
  tensorProfileBound_positive := Population.tensorProfileBound_positive
  identityOf := Population.identityOf
  skinEquivalent := MinimalBlocker.EndpointSkinEquivalent F
  boundedCertificateOutcome := Population.boundedCertificateOutcome
  tensorSplitOutcome := Population.tensorSplitOutcome
  sameIdentityExhaustive := by
    intro left right sameSupport sameIdentity
    rcases Population.sameIdentityCandidateExhaustive
        left right sameSupport sameIdentity with skin | remaining
    · exact Or.inl skin
    · rcases remaining with bounded | remaining
      · exact Or.inr (Or.inl bounded)
      · rcases remaining with tensor | remaining
        · exact Or.inr (Or.inr (Or.inl tensor))
        · rcases remaining with sunflower | independent
          · exact Or.inr (Or.inr (Or.inr sunflower))
          · rcases independent with ⟨factor, independent⟩
            exact False.elim <|
              Governance.noIndependentAuthorizer factor independent
  skinFinality := MinimalBlocker.eq_of_endpointSkinEquivalent F

/--
Literal reduction certificates for all non-skin branches. Terminality is
derived from reduction minimality rather than imported as a free premise.
-/
structure ReductionMinimalFourRoleCertificatePipeline
    {Pkg alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    (measure : Pkg -> ReductionPotential)
    (Endpoint : Pkg -> Prop)
    (PreservesTargetScope : Pkg -> List Pkg -> Prop)
    (SunflowerCertificate : Pkg -> Prop)
    (P : Pkg)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (Population : AASCFourRoleIdentityPopulation
      (tensorProfileBound := tensorProfileBound) F noSunflower) where
  sunflowerSettles :
    forall Q : Pkg, SunflowerCertificate Q -> Endpoint Q
  reductionMinimal :
    ReductionMinimalCountercase measure Endpoint P
  boundedCertificate :
    forall left right,
      Population.boundedCertificateOutcome left right ->
      Nonempty (DirectCloseoutCertificate measure Endpoint P)
  tensorSplitCertificate :
    forall left right,
      Population.tensorSplitOutcome left right ->
      Nonempty
        (EndpointFaithfulSplit measure Endpoint PreservesTargetScope P)
  sunflowerCertificate :
    Concrete.HasSunflower k F -> SunflowerCertificate P

/-- Reduction minimality makes the active package certificate-terminal. -/
def ReductionMinimalFourRoleCertificatePipeline.terminal
    {Pkg alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {measure : Pkg -> ReductionPotential}
    {Endpoint : Pkg -> Prop}
    {PreservesTargetScope : Pkg -> List Pkg -> Prop}
    {SunflowerCertificate : Pkg -> Prop}
    {P : Pkg}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {Population : AASCFourRoleIdentityPopulation
      (tensorProfileBound := tensorProfileBound) F noSunflower}
    (Pipeline : ReductionMinimalFourRoleCertificatePipeline measure Endpoint
      PreservesTargetScope SunflowerCertificate P F noSunflower Population) :
    TerminalPackage measure Endpoint PreservesTargetScope
      SunflowerCertificate P :=
  reductionMinimal_countercase_terminal
    measure Endpoint PreservesTargetScope SunflowerCertificate
    Pipeline.sunflowerSettles Pipeline.reductionMinimal

/-- The reduction pipeline realizes every non-skin branch as a certificate. -/
def ReductionMinimalFourRoleCertificatePipeline.branchRealization
    {Pkg alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {measure : Pkg -> ReductionPotential}
    {Endpoint : Pkg -> Prop}
    {PreservesTargetScope : Pkg -> List Pkg -> Prop}
    {SunflowerCertificate : Pkg -> Prop}
    {P : Pkg}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {Population : AASCFourRoleIdentityPopulation
      (tensorProfileBound := tensorProfileBound) F noSunflower}
    (Pipeline : ReductionMinimalFourRoleCertificatePipeline measure Endpoint
      PreservesTargetScope SunflowerCertificate P F noSunflower Population) :
    CertifiedAASCFourRoleBranchRealization measure Endpoint
      PreservesTargetScope SunflowerCertificate P F noSunflower Population where
  boundedCertificate := Pipeline.boundedCertificate
  tensorSplitCertificate := Pipeline.tensorSplitCertificate
  sunflowerCertificate := Pipeline.sunflowerCertificate

/-- Reduction certificates plus minimality mechanically give branch closeout. -/
def ReductionMinimalFourRoleCertificatePipeline.identityCloseout
    {Pkg alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {measure : Pkg -> ReductionPotential}
    {Endpoint : Pkg -> Prop}
    {PreservesTargetScope : Pkg -> List Pkg -> Prop}
    {SunflowerCertificate : Pkg -> Prop}
    {P : Pkg}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {Population : AASCFourRoleIdentityPopulation
      (tensorProfileBound := tensorProfileBound) F noSunflower}
    (Pipeline : ReductionMinimalFourRoleCertificatePipeline measure Endpoint
      PreservesTargetScope SunflowerCertificate P F noSunflower Population) :
    AASCFourRoleIdentityCloseout Population :=
  Pipeline.branchRealization.toIdentityCloseout Pipeline.terminal

/--
The complete witness pipeline. Its governance parameter is constructed from
kernel necessity; its fields are only generated finite classifications and
literal reduction certificates.
-/
structure KernelNecessityAnchoredFourRoleWitnessPipeline
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {branch : Concrete.UniformSetFamily alpha (r + 1) -> Prop}
    {endpointUse : LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k) branch}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Governance : NecessityRootedEndpointGovernance endpointUse corpus)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) where
  generated :
    KernelGovernedGeneratedFourRolePopulation
      (tensorProfileBound := tensorProfileBound)
      Governance F noSunflower
  Pkg : Type
  measure : Pkg -> ReductionPotential
  Endpoint : Pkg -> Prop
  PreservesTargetScope : Pkg -> List Pkg -> Prop
  SunflowerCertificate : Pkg -> Prop
  package : Pkg
  certificates :
    ReductionMinimalFourRoleCertificatePipeline measure Endpoint
      PreservesTargetScope SunflowerCertificate package F noSunflower
      generated.toAASCFourRoleIdentityPopulation

/-- The necessity-anchored witness pipeline constructs the four-role closure. -/
def KernelNecessityAnchoredFourRoleWitnessPipeline.fourRoleIdentityClosure
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {branch : Concrete.UniformSetFamily alpha (r + 1) -> Prop}
    {endpointUse : LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k) branch}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    {Governance : NecessityRootedEndpointGovernance endpointUse corpus}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Pipeline : KernelNecessityAnchoredFourRoleWitnessPipeline
      (tensorProfileBound := tensorProfileBound)
      Governance F noSunflower) :
    AASCFourRoleIdentityClosure
      (tensorProfileBound := tensorProfileBound) F noSunflower where
  population := Pipeline.generated.toAASCFourRoleIdentityPopulation
  closeout := Pipeline.certificates.identityCloseout

/-- Fixed identity is a derived consequence of the full necessity-rooted chain. -/
def KernelNecessityAnchoredFourRoleWitnessPipeline.fixedIdentityRealization
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {branch : Concrete.UniformSetFamily alpha (r + 1) -> Prop}
    {endpointUse : LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k) branch}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    {Governance : NecessityRootedEndpointGovernance endpointUse corpus}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Pipeline : KernelNecessityAnchoredFourRoleWitnessPipeline
      (tensorProfileBound := tensorProfileBound)
      Governance F noSunflower) :
    KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower :=
  Pipeline.fourRoleIdentityClosure.toFixedIdentityRealization

/-- Audit-facing trace from kernel necessity through terminal fixed identity. -/
structure KernelNecessityToFixedIdentityTrace
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {branch : Concrete.UniformSetFamily alpha (r + 1) -> Prop}
    {endpointUse : LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k) branch}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Governance : NecessityRootedEndpointGovernance endpointUse corpus)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) : Prop where
  targetAdequacy : endpointUse.targetAdequate
  carrierNondegenerate :
    (Concrete.concreteSunflowerCarrier alpha (r + 1) k).nondegenerate
  kernelRoles : (corpus.kernelAtEndpointUse endpointUse).allRolesHold
  samenessMeaningful : (corpus.samenessAtEndpointUse endpointUse).sameness
  admissibilityBivalent :
    AdmissibilityBivalent (endpointConstructionRegime endpointUse corpus)
  fixedDomainInterface :
    FixedDomainInterfaceShape (endpointConstructionRegime endpointUse corpus)
  noDerivationBelow :
    NoDerivationBelowKernel (endpointConstructionRegime endpointUse corpus)
  globalSynthesis :
    KernelGlobalSynthesisUnderCorpusClosures
      (endpointConstructionRegime endpointUse corpus)
  fixedIdentity :
    Nonempty (KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower)

/-- Construct the complete audit trace from one witness pipeline. -/
def KernelNecessityAnchoredFourRoleWitnessPipeline.dependencyTrace
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {branch : Concrete.UniformSetFamily alpha (r + 1) -> Prop}
    {endpointUse : LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k) branch}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    {Governance : NecessityRootedEndpointGovernance endpointUse corpus}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Pipeline : KernelNecessityAnchoredFourRoleWitnessPipeline
      (tensorProfileBound := tensorProfileBound)
      Governance F noSunflower) :
    KernelNecessityToFixedIdentityTrace
      (tensorProfileBound := tensorProfileBound)
      Governance F noSunflower where
  targetAdequacy := Governance.targetAdequacy
  carrierNondegenerate := Governance.carrierNondegenerate
  kernelRoles := Governance.localKernelRoles
  samenessMeaningful := Governance.samenessMeaningful
  admissibilityBivalent := Governance.admissibilityBivalent
  fixedDomainInterface := Governance.fixedDomainInterfaceShape
  noDerivationBelow := Governance.noDerivationBelowKernel
  globalSynthesis := Governance.globalSynthesis
  fixedIdentity := ⟨Pipeline.fixedIdentityRealization⟩

end KernelNecessityRoleOccupancy
end V2
end SunflowerAASC
