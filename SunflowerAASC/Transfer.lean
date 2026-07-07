import SunflowerAASC.Certificates

namespace SunflowerAASC

/-- Exact countercase opening for the fixed sunflower endpoint. -/
structure ExactCountercaseUse
    (S : SunflowerCarrier)
    (F : S.Family) where
  openedAsLiveCountercase : Prop
  noSunflower_holds : S.noSunflower F
  openedAsLiveCountercase_holds : openedAsLiveCountercase

/-- Residual separator status work: the residual branch yields a discriminator. -/
structure ResidualStatusWork
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat)
    (F : S.Family) where
  use :
    LocalEndpointUse S (ResidualSeparator S C H)
  discriminator :
    IndependentDiscriminator
      S
      (ResidualSeparator S C H)
      S.positiveEndpoint

structure ResidualSeparatorBridge
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) where
  exactCountercaseGivesLocalUse :
    forall F : S.Family,
      ExactCountercaseUse S F ->
      ResidualSeparator S C H F ->
      LocalEndpointUse S (ResidualSeparator S C H)
  residualUseGivesStatusWork :
    forall F : S.Family,
      ExactCountercaseUse S F ->
      ResidualSeparator S C H F ->
      ResidualStatusWork S C H F

def local_residual_separator_use
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (B : ResidualSeparatorBridge S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F)
    (R : ResidualSeparator S C H F) :
    LocalEndpointUse S (ResidualSeparator S C H) := by
  exact B.exactCountercaseGivesLocalUse F E R

def residual_separator_induces_local_endpoint_status_work
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (B : ResidualSeparatorBridge S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F)
    (R : ResidualSeparator S C H F) :
    ResidualStatusWork S C H F := by
  exact B.residualUseGivesStatusWork F E R

theorem no_local_endpoint_standing_residual_separator
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (G : KernelForcedGovernance S)
    (B : ResidualSeparatorBridge S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F)
    (R : ResidualSeparator S C H F) :
    False := by
  let W := residual_separator_induces_local_endpoint_status_work B E R
  exact
    local_endpoint_use_excludes_independent_discriminator
      G
      W.use
      W.discriminator

theorem kernel_forced_discharge_of_calibrated_residual_separator
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (G : KernelForcedGovernance S)
    (B : ResidualSeparatorBridge S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    Not (ResidualSeparator S C H F) := by
  intro R
  exact no_local_endpoint_standing_residual_separator G B E R

/--
Under the fixed branch split, if the residual branch is discharged then
no-sunflower countercase use must lie in the certified branch.
-/
theorem local_endpoint_transfer_to_BMF
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (G : KernelForcedGovernance S)
    (B : ResidualSeparatorBridge S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F)
    (split : S.noSunflower F -> BMF S C H F \/ ObjectiveNonBMF S C H F) :
    BMF S C H F := by
  have hn : S.noSunflower F := E.noSunflower_holds
  cases split hn with
  | inl hbmf => exact hbmf
  | inr hnon =>
      have R : ResidualSeparator S C H F := And.intro hn hnon
      exact False.elim (kernel_forced_discharge_of_calibrated_residual_separator G B E R)

end SunflowerAASC
