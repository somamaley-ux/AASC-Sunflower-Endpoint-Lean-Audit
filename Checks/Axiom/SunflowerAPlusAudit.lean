import SunflowerAASC.APlusAudit

namespace SunflowerAASC

theorem sunflower_a_plus_audit_obligation_count :
    sunflowerAPlusObligations.length = 31 := by
  exact sunflowerAPlusObligationCount_eq

theorem sunflower_a_plus_audit_titles_populated :
    sunflowerAPlusObligationTitlesPopulated = true := by
  exact sunflowerAPlusObligationTitlesPopulated_eq_true

theorem sunflower_kernel_role_count :
    kernelRoles.length = 4 := by
  exact kernelRoles_length_eq

theorem sunflower_a_plus_certificate_surface
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (A : SunflowerAPlusAuditCertificate S C H) :
    A.auditSurfaceComplete := by
  exact A.auditSurfaceComplete_holds

theorem sunflower_a_plus_transfer_surface
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (A : SunflowerAPlusAuditCertificate S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact A.transfer_to_BMF E

end SunflowerAASC
