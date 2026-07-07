import SunflowerAASC.Kernel

namespace SunflowerAASC

/-- Finite certificate language used for calibrated bounded motif factorization. -/
structure CertificateLanguage (S : SunflowerCarrier) where
  Code : Type
  rawMotif : Code -> Prop
  endpointPreserving : Code -> Prop
  rankAccounting : Code -> Prop
  finiteLanguage : Prop
  finiteLanguage_holds : finiteLanguage

/-- Completeness record for the fixed proof instance. -/
structure CompletenessRecord
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) where
  completeForBoundedCertificates : Prop
  calibratedCeiling : Prop
  noDeferredRepair : Prop
  endpointInertSupportOnly : Prop
  completeForBoundedCertificates_holds : completeForBoundedCertificates
  calibratedCeiling_holds : calibratedCeiling
  noDeferredRepair_holds : noDeferredRepair
  endpointInertSupportOnly_holds : endpointInertSupportOnly

def CompletenessRecord.ready
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (R : CompletenessRecord S C H) : Prop :=
  R.completeForBoundedCertificates /\
  R.calibratedCeiling /\
  R.noDeferredRepair /\
  R.endpointInertSupportOnly

theorem CompletenessRecord.ready_holds
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (R : CompletenessRecord S C H) :
    R.ready := by
  exact
    And.intro R.completeForBoundedCertificates_holds
      (And.intro R.calibratedCeiling_holds
        (And.intro R.noDeferredRepair_holds
          R.endpointInertSupportOnly_holds))

/-- Bounded motif factorization certificate for a family on the fixed carrier. -/
structure BoundedMotifCertificate
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat)
    (F : S.Family) where
  code : C.Code
  rawMotif_holds : C.rawMotif code
  endpointPreserving_holds : C.endpointPreserving code
  rankAccounting_holds : C.rankAccounting code
  entropyBound : Prop
  entropyBound_holds : entropyBound

def BMF
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat)
    (F : S.Family) : Prop :=
  Nonempty (BoundedMotifCertificate S C H F)

/-- Objective certificate failure, distinct from merely not having found a record. -/
structure ObjectiveNonBMF
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat)
    (F : S.Family) where
  noCertificateInFixedLanguage : Not (BMF S C H F)
  completenessReady :
    forall R : CompletenessRecord S C H, R.ready

def ResidualSeparator
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat)
    (F : S.Family) : Prop :=
  S.noSunflower F /\ ObjectiveNonBMF S C H F

theorem residual_separator_contains_no_sunflower
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    {F : S.Family} :
    ResidualSeparator S C H F -> S.noSunflower F := by
  intro h
  exact h.left

theorem residual_separator_contains_objective_nonBMF
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    {F : S.Family} :
    ResidualSeparator S C H F -> ObjectiveNonBMF S C H F := by
  intro h
  exact h.right

/-- The certified branch is support-level: it supplies a bounded certificate. -/
theorem BMF_is_support_not_endpoint_authority
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    {F : S.Family}
    (h : BMF S C H F) :
    BMF S C H F := by
  exact h

end SunflowerAASC
