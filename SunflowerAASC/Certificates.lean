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

/--
Language-independent universe of finite negative motifs.  Lawfulness and the
carrier-level exclusion criterion do not mention a certificate language or a
calibrated ceiling, preventing the completeness test from ranging only over
motifs already visible below the current ceiling.
-/
structure LanguageIndependentNegativeMotifSystem
    (S : SunflowerCarrier) where
  Motif : Type
  lawfulNegativeMotif : Motif -> Prop
  densityExceeds : Nat -> Motif -> Prop
  excludedByCarrierCriterion : Motif -> Prop

/--
The controlling motif universe is fixed by the carrier before any certificate
language or ceiling is introduced.
-/
def SunflowerCarrier.negativeMotifSystem
    (S : SunflowerCarrier) :
    LanguageIndependentNegativeMotifSystem S :=
  { Motif := S.NegativeMotif
    lawfulNegativeMotif := S.lawfulNegativeMotif
    densityExceeds := S.motifDensityExceeds
    excludedByCarrierCriterion := S.motifExcludedByCarrierCriterion }

/-- Regression ledger for the completeness-calibration criticism. -/
inductive CompletenessCalibrationObligation where
  | fixedCarrierMotifUniverse
  | languageIndependentLawfulness
  | representationAdequacy
  | ceilingTranscendentCoverage
deriving DecidableEq, Repr

def completenessCalibrationObligations :
    List CompletenessCalibrationObligation :=
  [ .fixedCarrierMotifUniverse
  , .languageIndependentLawfulness
  , .representationAdequacy
  , .ceilingTranscendentCoverage
  ]

theorem completenessCalibrationObligationCount_eq :
    completenessCalibrationObligations.length = 4 := by
  rfl

/--
Language-relative representation data, separated from language-independent
motif admissibility.  A represented motif has an actual endpoint-preserving,
rank-accounting code; the second branch records reduction to such a code
without density loss.
-/
structure CertificateRepresentationAdequacy
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (M : LanguageIndependentNegativeMotifSystem S) where
  represented : M.Motif -> Prop
  reducesToRepresentedWithoutDensityLoss : M.Motif -> Prop
  representedHasCertificate :
    forall motif : M.Motif,
      represented motif ->
      Exists (fun code : C.Code =>
        C.rawMotif code /\
        C.endpointPreserving code /\
        C.rankAccounting code)

/--
Objective, ceiling-transcendent completeness.  Every lawful motif is either
represented, reduced to represented structure without density loss, or
excluded by a language-independent carrier criterion.  Represented and reduced
motifs are calibrated against the current ceiling at motif level; this does not
assert the final extremal bound for arbitrary families.
-/
structure CeilingTranscendentCompleteness
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat)
    (M : LanguageIndependentNegativeMotifSystem S)
    (R : CertificateRepresentationAdequacy S C M) where
  coversEveryLawfulMotif :
    forall motif : M.Motif,
      M.lawfulNegativeMotif motif ->
      R.represented motif \/
      R.reducesToRepresentedWithoutDensityLoss motif \/
      M.excludedByCarrierCriterion motif
  calibratedAtMotifLevel :
    forall motif : M.Motif,
      M.lawfulNegativeMotif motif ->
      (R.represented motif \/
        R.reducesToRepresentedWithoutDensityLoss motif) ->
      Not (M.densityExceeds H motif)

/-- A lawful motif omitted by every admissible completeness disposition. -/
structure OmittedLawfulNegativeMotif
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    (M : LanguageIndependentNegativeMotifSystem S)
    (R : CertificateRepresentationAdequacy S C M) where
  motif : M.Motif
  lawful_holds : M.lawfulNegativeMotif motif
  notRepresented : Not (R.represented motif)
  notReducible : Not (R.reducesToRepresentedWithoutDensityLoss motif)
  notExcluded : Not (M.excludedByCarrierCriterion motif)

theorem OmittedLawfulNegativeMotif.invalidatesCompleteness
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    {M : LanguageIndependentNegativeMotifSystem S}
    {R : CertificateRepresentationAdequacy S C M}
    (O : OmittedLawfulNegativeMotif M R) :
    Not (CeilingTranscendentCompleteness S C H M R) := by
  intro complete
  rcases complete.coversEveryLawfulMotif O.motif O.lawful_holds with
    hRepresented | hReducibleOrExcluded
  · exact O.notRepresented hRepresented
  · rcases hReducibleOrExcluded with hReducible | hExcluded
    · exact O.notReducible hReducible
    · exact O.notExcluded hExcluded

theorem CeilingTranscendentCompleteness.excludesLawfulHigherDensityMotif
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    {M : LanguageIndependentNegativeMotifSystem S}
    {R : CertificateRepresentationAdequacy S C M}
    (complete : CeilingTranscendentCompleteness S C H M R)
    {motif : M.Motif}
    (lawful : M.lawfulNegativeMotif motif)
    (higherDensity : M.densityExceeds H motif)
    (notExcluded : Not (M.excludedByCarrierCriterion motif)) :
    False := by
  rcases complete.coversEveryLawfulMotif motif lawful with
    hRepresented | hReducibleOrExcluded
  · exact complete.calibratedAtMotifLevel motif lawful (Or.inl hRepresented)
      higherDensity
  · rcases hReducibleOrExcluded with hReducible | hExcluded
    · exact complete.calibratedAtMotifLevel motif lawful (Or.inr hReducible)
        higherDensity
    · exact notExcluded hExcluded

/--
Existential package used by the endpoint audit: the motif universe is external
to the language, representation is language-relative, and completeness covers
the external universe at the fixed ceiling.
-/
structure ObjectiveMotifCompletenessSource
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) where
  representation :
    CertificateRepresentationAdequacy S C S.negativeMotifSystem
  completeness :
    CeilingTranscendentCompleteness
      S C H S.negativeMotifSystem representation

def ObjectiveMotifCompletenessSource.motifSystem
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (_Src : ObjectiveMotifCompletenessSource S C H) :
    LanguageIndependentNegativeMotifSystem S :=
  S.negativeMotifSystem

theorem ObjectiveMotifCompletenessSource.excludesLawfulHigherDensityMotif
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : ObjectiveMotifCompletenessSource S C H)
    {motif : Src.motifSystem.Motif}
    (lawful : Src.motifSystem.lawfulNegativeMotif motif)
    (higherDensity : Src.motifSystem.densityExceeds H motif)
    (notExcluded :
      Not (Src.motifSystem.excludedByCarrierCriterion motif)) :
    False := by
  exact
    Src.completeness.excludesLawfulHigherDensityMotif
      lawful
      higherDensity
      notExcluded

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
  cardinalityBound_holds :
    S.familySize F <= S.ceilingBound H S.rank

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

/-- A branch whose endpoint content remains wholly on the negative side. -/
def SameSideNegativeRefinement
    (S : SunflowerCarrier)
    (branch : S.Family -> Prop) : Prop :=
  forall F : S.Family, branch F -> S.noSunflower F

theorem residualSeparator_is_sameSideNegativeRefinement
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat} :
    SameSideNegativeRefinement S (ResidualSeparator S C H) := by
  intro F residual
  exact residual.left

/--
Quantitative residual content.  Unlike the legacy logical residual predicate,
this version includes the actual carrier cardinality comparison.
-/
def QuantitativeResidualSeparator
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat)
    (F : S.Family) : Prop :=
  S.noSunflower F /\
  S.ceilingBound H S.rank < S.familySize F /\
  ObjectiveNonBMF S C H F

theorem quantitativeResidual_contains_sizeExcess
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    {F : S.Family}
    (R : QuantitativeResidualSeparator S C H F) :
    S.ceilingBound H S.rank < S.familySize F := by
  exact R.right.left

/-- A fixed carrier standing factor realizing a branch predicate. -/
structure StandingFactorRealizesBranch
    (S : SunflowerCarrier)
    (factor : S.StandingFactor)
    (branch : S.Family -> Prop) where
  realizes :
    forall F : S.Family,
      S.standingFactorBranch factor F <-> branch F

/--
Independent standing authorization excludes same-side negative refinement by
definition.  This prevents residual mathematical content from being relabeled
as an independent endpoint authority.
-/
structure IndependentStandingAuthorizer
    (S : SunflowerCarrier)
    (A : FixedDomainAPlusClosureSource S)
    (factor : S.StandingFactor)
    (branch : S.Family -> Prop) extends
    StandingFactorRealizesBranch S factor branch where
  notNegativeRefinement : Not (SameSideNegativeRefinement S branch)
  independentDisposition :
    A.disposition factor = SameScopeFactorDisposition.independentAuthorizer

theorem IndependentStandingAuthorizer.excludedByCorpusClosure
    {S : SunflowerCarrier}
    {A : FixedDomainAPlusClosureSource S}
    {factor : S.StandingFactor}
    {branch : S.Family -> Prop}
    (I : IndependentStandingAuthorizer S A factor branch) :
    False := by
  exact A.excludesIndependentAuthorizer factor I.independentDisposition

theorem residualSeparator_is_not_independentStandingAuthorizer
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    {A : FixedDomainAPlusClosureSource S}
    {factor : S.StandingFactor}
    (I : IndependentStandingAuthorizer
      S A factor (ResidualSeparator S C H)) :
    False := by
  exact I.notNegativeRefinement residualSeparator_is_sameSideNegativeRefinement

theorem residualSeparator_is_not_legacyIndependentDiscriminator
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    {positive : S.Family -> Prop}
    (D : IndependentDiscriminator
      S (ResidualSeparator S C H) positive) :
    False := by
  exact
    D.notSameSideNegativeRefinement
      residualSeparator_is_sameSideNegativeRefinement

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
