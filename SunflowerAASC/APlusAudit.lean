import SunflowerAASC.Transfer

namespace SunflowerAASC

/-- Manuscript theorem-spine obligations for the Sunflower A+ audit. -/
inductive SunflowerAPlusObligation where
  | proofClassLock
  | standingObjection
  | targetAdequacyForcesKernel
  | kernelConcession
  | objectToCountercaseBridge
  | localResidualUse
  | costOfKernelDenial
  | noThirdKernelPosition
  | corePetalEquivalence
  | minimalSpreadReduction
  | certificateLanguage
  | rawMotifCertification
  | completenessRecord
  | boundedMotifCertificate
  | certifiedBranchBound
  | rawCertifiedEntropyCeiling
  | productTransversalCalibration
  | cycleMotifCalibration
  | calibratedResidualBranch
  | objectiveCertificateFailure
  | BMFSupportOnly
  | nonBMFStatusWork
  | residualNotArbitraryNegation
  | calibratedCountercaseSplit
  | residualStatusWork
  | noIndependentDiscriminator
  | noResidualSeparatorStanding
  | kernelForcedTransfer
  | endpointCloseout
  | proofClassBoundary
  | adversarialAudit
deriving DecidableEq, Repr

def sunflowerAPlusObligations : List SunflowerAPlusObligation :=
  [ .proofClassLock
  , .standingObjection
  , .targetAdequacyForcesKernel
  , .kernelConcession
  , .objectToCountercaseBridge
  , .localResidualUse
  , .costOfKernelDenial
  , .noThirdKernelPosition
  , .corePetalEquivalence
  , .minimalSpreadReduction
  , .certificateLanguage
  , .rawMotifCertification
  , .completenessRecord
  , .boundedMotifCertificate
  , .certifiedBranchBound
  , .rawCertifiedEntropyCeiling
  , .productTransversalCalibration
  , .cycleMotifCalibration
  , .calibratedResidualBranch
  , .objectiveCertificateFailure
  , .BMFSupportOnly
  , .nonBMFStatusWork
  , .residualNotArbitraryNegation
  , .calibratedCountercaseSplit
  , .residualStatusWork
  , .noIndependentDiscriminator
  , .noResidualSeparatorStanding
  , .kernelForcedTransfer
  , .endpointCloseout
  , .proofClassBoundary
  , .adversarialAudit
  ]

def sunflowerAPlusObligationTitle : SunflowerAPlusObligation -> String
  | .proofClassLock => "Proof-class lock"
  | .standingObjection => "Standing objection"
  | .targetAdequacyForcesKernel => "Target adequacy forces kernel"
  | .kernelConcession => "Kernel concession"
  | .objectToCountercaseBridge => "Object-to-countercase bridge"
  | .localResidualUse => "Local residual separator use"
  | .costOfKernelDenial => "Cost of kernel denial"
  | .noThirdKernelPosition => "No third kernel position"
  | .corePetalEquivalence => "Core-petal endpoint equivalence"
  | .minimalSpreadReduction => "Minimal spread reduction"
  | .certificateLanguage => "Certificate language"
  | .rawMotifCertification => "Raw motif certification"
  | .completenessRecord => "Completeness record"
  | .boundedMotifCertificate => "Bounded motif certificate"
  | .certifiedBranchBound => "Certified branch bound"
  | .rawCertifiedEntropyCeiling => "Raw certified entropy ceiling"
  | .productTransversalCalibration => "Product-transversal calibration"
  | .cycleMotifCalibration => "Cycle-motif calibration"
  | .calibratedResidualBranch => "Calibrated residual branch"
  | .objectiveCertificateFailure => "Objective certificate failure"
  | .BMFSupportOnly => "BMF support only"
  | .nonBMFStatusWork => "Objective non-BMF status work"
  | .residualNotArbitraryNegation => "Residual is not arbitrary negation"
  | .calibratedCountercaseSplit => "Calibrated countercase split"
  | .residualStatusWork => "Residual status work"
  | .noIndependentDiscriminator => "No independent discriminator"
  | .noResidualSeparatorStanding => "No residual separator standing"
  | .kernelForcedTransfer => "Kernel-forced transfer"
  | .endpointCloseout => "Endpoint closeout"
  | .proofClassBoundary => "Proof-class boundary"
  | .adversarialAudit => "Adversarial audit"

def sunflowerAPlusObligationTitles : List String :=
  sunflowerAPlusObligations.map sunflowerAPlusObligationTitle

theorem sunflowerAPlusObligationCount_eq :
    sunflowerAPlusObligations.length = 31 := by
  rfl

def sunflowerAPlusObligationTitlesPopulated : Bool :=
  sunflowerAPlusObligationTitles.all (fun title => !title.isEmpty)

theorem sunflowerAPlusObligationTitlesPopulated_eq_true :
    sunflowerAPlusObligationTitlesPopulated = true := by
  rfl

structure SunflowerAPlusAuditCertificate
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) where
  kernelNecessity : KernelNecessitySource S
  fixedDomainClosure : FixedDomainAPlusClosureSource S
  governance : KernelForcedGovernance S
  residualBridge : ResidualSeparatorBridge S C H
  completeness : CompletenessRecord S C H
  objectiveMotifCompleteness : ObjectiveMotifCompletenessSource S C H
  branchSplit :
    forall F : S.Family,
      S.noSunflower F -> BMF S C H F \/ ObjectiveNonBMF S C H F
  carrierNondegenerate : S.nondegenerate

def SunflowerAPlusAuditCertificate.kernelFirstCorpusMachinery
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (A : SunflowerAPlusAuditCertificate S C H) :
    KernelFirstCorpusMachinery S :=
  { kernelNecessity := A.kernelNecessity
    fixedDomainClosure := A.fixedDomainClosure }

def SunflowerAPlusAuditCertificate.auditSurfaceComplete
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (A : SunflowerAPlusAuditCertificate S C H) : Prop :=
  sunflowerAPlusObligations.length = 31 /\
  sunflowerAPlusObligationTitlesPopulated = true /\
  completenessCalibrationObligations.length = 4 /\
  kernelRoles.length = 4 /\
  C.finiteLanguage /\
  A.completeness.ready /\
  S.nondegenerate

theorem SunflowerAPlusAuditCertificate.auditSurfaceComplete_holds
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (A : SunflowerAPlusAuditCertificate S C H) :
    A.auditSurfaceComplete := by
  exact
    And.intro sunflowerAPlusObligationCount_eq
      (And.intro sunflowerAPlusObligationTitlesPopulated_eq_true
        (And.intro completenessCalibrationObligationCount_eq
          (And.intro kernelRoles_length_eq
            (And.intro C.finiteLanguage_holds
              (And.intro (CompletenessRecord.ready_holds A.completeness)
                A.carrierNondegenerate)))))

theorem SunflowerAPlusAuditCertificate.discharge_residual
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (A : SunflowerAPlusAuditCertificate S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    Not (ResidualSeparator S C H F) := by
  exact
    kernel_forced_discharge_of_calibrated_residual_separator
      A.governance
      A.residualBridge
      E

theorem SunflowerAPlusAuditCertificate.transfer_to_BMF
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (A : SunflowerAPlusAuditCertificate S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact
    local_endpoint_transfer_to_BMF
      A.governance
      A.residualBridge
      E
      (A.branchSplit F)

end SunflowerAASC
