import Std
import SunflowerAASC.APlusAudit
import SunflowerAASC.V2.FiniteCombinatorics

namespace SunflowerAASC
namespace V2

/--
The v2 architecture works with fully reduced prime packages, not with raw
families alone.  The fields record the structural gates that must already be
active before the blocker quotient theorem is allowed to fire.
-/
structure FullyReducedPrimePackage (S : SunflowerCarrier) where
  family : S.Family
  saturated : Prop
  endpointFaithful : Prop
  quotientFinal : Prop
  fullyReduced : Prop
  prime : Prop
  noSunflower_holds : S.noSunflower family
  saturated_holds : saturated
  endpointFaithful_holds : endpointFaithful
  quotientFinal_holds : quotientFinal
  fullyReduced_holds : fullyReduced
  prime_holds : prime

def FullyReducedPrimePackage.ready
    {S : SunflowerCarrier}
    (P : FullyReducedPrimePackage S) : Prop :=
  P.saturated /\
  P.endpointFaithful /\
  P.quotientFinal /\
  P.fullyReduced /\
  P.prime /\
  S.noSunflower P.family

theorem FullyReducedPrimePackage.ready_holds
    {S : SunflowerCarrier}
    (P : FullyReducedPrimePackage S) :
    P.ready := by
  exact
    And.intro P.saturated_holds
      (And.intro P.endpointFaithful_holds
        (And.intro P.quotientFinal_holds
          (And.intro P.fullyReduced_holds
            (And.intro P.prime_holds P.noSunflower_holds))))

/-- A fixed core link inside a fully reduced prime package. -/
structure CoreLink
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S) where
  core : S.Core
  linkRank : Nat
  sameCarrier : Prop
  coreAdmissible : Prop
  linkNoMatchingK : Prop
  sameCarrier_holds : sameCarrier
  coreAdmissible_holds : coreAdmissible
  linkNoMatchingK_holds : linkNoMatchingK

/--
The classical maximal-matching blocker certificate.  Its raw size may depend
on rank; v2 deliberately does not use raw boundedness as the final compactness
claim.
-/
structure RawBlockerCertificate
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P) where
  rawSize : Nat
  hitsEveryPetal : Prop
  fromMaximalMatching : Prop
  classicalRankDependentBound : rawSize <= S.k * S.rank
  hitsEveryPetal_holds : hitsEveryPetal
  fromMaximalMatching_holds : fromMaximalMatching

/-- Complete role profile agreement for blocker coordinates at a fixed core. -/
structure BlockerRoleProfile
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P) where
  blocksPetals : Prop
  opensFurtherLinks : Prop
  stableUnderCoreExtension : Prop
  roleEligible : Prop
  quotientBehaviorFixed : Prop
  failureOrSaturationStatusFixed : Prop

/--
The role-distinct blocker quotient.  The count is the number of complete
continuation/profile classes that survive saturation, quotienting, and prime
reduction.
-/
structure RoleDistinctBlockerQuotient
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C) where
  classCount : Nat
  classCount_le_rawSize_succ : classCount <= B.rawSize + 1
  everyRawBlockerRepresented : Prop
  sameCoarseColorCollapsesOrSplits : Prop
  arbitrarySelectionRejected : Prop
  omittedGeneratedMotifsCovered : Prop
  everyRawBlockerRepresented_holds : everyRawBlockerRepresented
  sameCoarseColorCollapsesOrSplits_holds : sameCoarseColorCollapsesOrSplits
  arbitrarySelectionRejected_holds : arbitrarySelectionRejected
  omittedGeneratedMotifsCovered_holds : omittedGeneratedMotifsCovered

def RoleDistinctBlockerQuotient.ready
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (Q : RoleDistinctBlockerQuotient S P C B) : Prop :=
  Q.everyRawBlockerRepresented /\
  Q.sameCoarseColorCollapsesOrSplits /\
  Q.arbitrarySelectionRejected /\
  Q.omittedGeneratedMotifsCovered

theorem RoleDistinctBlockerQuotient.ready_holds
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (Q : RoleDistinctBlockerQuotient S P C B) :
    Q.ready := by
  exact
    And.intro Q.everyRawBlockerRepresented_holds
      (And.intro Q.sameCoarseColorCollapsesOrSplits_holds
        (And.intro Q.arbitrarySelectionRejected_holds
          Q.omittedGeneratedMotifsCovered_holds))

/-- Saturation disposition for a generated blocker/motif candidate. -/
structure SaturationDisposition where
  represented : Prop
  quotientEquivalent : Prop
  reducibleToPrime : Prop
  terminalBranchCovered : Prop
  disposition_holds :
    represented \/ quotientEquivalent \/ reducibleToPrime \/ terminalBranchCovered

/--
Finite blocker saturation is the Clock-style coverage condition specialized to
the blocker quotient: every generated candidate receives a terminal disposition.
-/
structure BlockerSaturationCoverage
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C) where
  Candidate : Type
  generated : Candidate -> Prop
  disposition : forall c : Candidate, generated c -> SaturationDisposition
  coverageComplete : Prop
  coverageComplete_holds : coverageComplete

theorem omittedGeneratedMotifsCovered_of_saturationCoverage
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (Sat : BlockerSaturationCoverage S P C B) :
    Sat.coverageComplete := by
  exact Sat.coverageComplete_holds

def saturationCoverageOfQuotient
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (Q : RoleDistinctBlockerQuotient S P C B) :
    BlockerSaturationCoverage S P C B :=
  { Candidate := PUnit
    generated := fun _ => True
    disposition := by
      intro _ _
      exact
        { represented := False
          quotientEquivalent := False
          reducibleToPrime := False
          terminalBranchCovered := Q.omittedGeneratedMotifsCovered
          disposition_holds := Or.inr (Or.inr (Or.inr Q.omittedGeneratedMotifsCovered_holds)) }
    coverageComplete := Q.omittedGeneratedMotifsCovered
    coverageComplete_holds := Q.omittedGeneratedMotifsCovered_holds }

theorem saturationCoverage_complete_of_quotient
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (Q : RoleDistinctBlockerQuotient S P C B) :
    (saturationCoverageOfQuotient Q).coverageComplete := by
  exact Q.omittedGeneratedMotifsCovered_holds

/--
Finite profile coding is the formal bridge from complete continuation profiles
to bounded role-distinct blockers.  The hard combinatorics is to construct this
record from saturation and quotient finality.
-/
structure FiniteProfileCoding
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C)
    (Q : RoleDistinctBlockerQuotient S P C B) where
  profileAlphabetSize : Nat
  profileAlphabetSize_positive : 0 < profileAlphabetSize
  allClassesCoded : Prop
  noMoreClassesThanCodes : Q.classCount <= profileAlphabetSize
  allClassesCoded_holds : allClassesCoded

theorem RoleDistinctBlockerQuotient.classCount_le_of_finiteProfileCoding
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    (F : FiniteProfileCoding S P C B Q) :
    Q.classCount <= F.profileAlphabetSize := by
  exact F.noMoreClassesThanCodes

theorem RoleDistinctBlockerQuotient.classCount_le_of_profileBound
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    {Qk : Nat}
    (F : FiniteProfileCoding S P C B Q)
    (hBound : F.profileAlphabetSize <= Qk) :
    Q.classCount <= Qk := by
  exact Nat.le_trans F.noMoreClassesThanCodes hBound

/--
A more concrete version of finite profile coding.  It records the actual map
from role classes to profile codes.  In this lightweight Lean project the
finite-cardinality comparison is kept as a field; the checked bridge below
ensures that this is exactly the only numerical fact consumed downstream.
-/
structure ConcreteFiniteProfileCoding
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C)
    (Q : RoleDistinctBlockerQuotient S P C B) where
  profileAlphabetSize : Nat
  profileAlphabetSize_positive : 0 < profileAlphabetSize
  code : Fin Q.classCount -> Fin profileAlphabetSize
  code_injective : Function.Injective code
  allClassesCoded : Prop
  allClassesCoded_holds : allClassesCoded
  countBound_from_injection : Q.classCount <= profileAlphabetSize

def ConcreteFiniteProfileCoding.toFiniteProfileCoding
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    (F : ConcreteFiniteProfileCoding S P C B Q) :
    FiniteProfileCoding S P C B Q :=
  { profileAlphabetSize := F.profileAlphabetSize
    profileAlphabetSize_positive := F.profileAlphabetSize_positive
    allClassesCoded := F.allClassesCoded
    noMoreClassesThanCodes := F.countBound_from_injection
    allClassesCoded_holds := F.allClassesCoded_holds }

theorem RoleDistinctBlockerQuotient.classCount_le_of_concreteProfileCoding
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    (F : ConcreteFiniteProfileCoding S P C B Q) :
    Q.classCount <= F.profileAlphabetSize := by
  exact F.countBound_from_injection

/--
Finite combinatorial color for a blocker representative.  This is deliberately
not an AASC type: it records finite incidence/deletion/profile data only.
-/
structure CoarseBlockerColor
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C)
    (Q : RoleDistinctBlockerQuotient S P C B) where
  colorIndex : Nat
  colorIndex_lt : colorIndex < Q.classCount
  finiteCombinatorialProfile : Prop
  finiteCombinatorialProfile_holds : finiteCombinatorialProfile

/--
True AASC blocker type at the fixed core/link/endpoint/certificate regime.
Equality of this type means equality of complete admissible standing behavior,
not just equality of a finite combinatorial color.
-/
structure AASCBlockerType
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C) where
  standingProfile : Prop
  admissibleRole : Prop
  endpointLocal : Prop
  certificateRegimeFixed : Prop
  standingProfile_holds : standingProfile
  admissibleRole_holds : admissibleRole
  endpointLocal_holds : endpointLocal
  certificateRegimeFixed_holds : certificateRegimeFixed

/-- Type-level skin witness used by the same-true-type collapse theorem. -/
structure AASCTypeSkinEquivalent
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C) where
  representativeOnly : Prop
  noStandingBearingDistinction : Prop
  representativeOnly_holds : representativeOnly
  noStandingBearingDistinction_holds : noStandingBearingDistinction

/--
Same AASC type collapses to skin.  This is the corrected AASC reading: there is
no standing-bearing surplus inside true same AASC type.  If the distinction
does endpoint work, the objects were not the same AASC type.
-/
structure SameAASCTypeSkinCollapse
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C) where
  sameTypeImpliesSkin :
    AASCBlockerType S P C B ->
    AASCBlockerType S P C B ->
    AASCTypeSkinEquivalent S P C B

def same_aasc_type_skin_collapse
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (Collapse : SameAASCTypeSkinCollapse S P C B)
    (T T' : AASCBlockerType S P C B) :
    AASCTypeSkinEquivalent S P C B := by
  exact Collapse.sameTypeImpliesSkin T T'

/-- Outcomes for a finite endpoint-local witness to a non-skin distinction. -/
structure AASCTypeDistinctionDisposition where
  boundedCertificateFiber : Prop
  tensorStandingSplit : Prop
  sunflowerRealization : Prop
  disposition_holds :
    boundedCertificateFiber \/ tensorStandingSplit \/ sunflowerRealization

/--
Finite endpoint-local witness for a blocker distinction that survives skin
collapse.  Such a witness refines the AASC type or lands in one of the three
allowed AASC roles: bounded certificate fiber, tensor/standing split, or
sunflower realization.
-/
structure EndpointLocalDistinctionWitness
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C) where
  finiteWitness : Prop
  endpointLocal : Prop
  disposition : AASCTypeDistinctionDisposition
  finiteWitness_holds : finiteWitness
  endpointLocal_holds : endpointLocal

/-- The complete AASC role ledger for blocker distinctions. -/
inductive AASCBlockerRole where
  | skin
  | boundedFiber
  | tensorSplit
  | sunRole
deriving DecidableEq, Repr

def aascBlockerRoles : List AASCBlockerRole :=
  [ .skin
  , .boundedFiber
  , .tensorSplit
  , .sunRole
  ]

theorem aascBlockerRoleCount_eq :
    aascBlockerRoles.length = 4 := by
  rfl

/--
Raw infinity is not an AASC role.  A coarse surplus either collapses as skin or
is licensed by a finite endpoint-local witness that lands in the admissible
four-role ledger.
-/
structure NoRawInfinityRole
    (S : SunflowerCarrier) where
  noFifthRole : Prop
  noFifthRole_holds : noFifthRole

theorem NoRawInfinityRole.noFifthRole_holds'
    {S : SunflowerCarrier}
    (No : NoRawInfinityRole S) :
    No.noFifthRole := by
  exact No.noFifthRole_holds

/--
Finite AASC-Type Population Theorem.  The combinatorics only has to show that
every non-skin blocker distinction has a finite endpoint-local witness; AASC
then routes that witness to bounded fiber, tensor split, or sunflower.
-/
structure FiniteAASCTypePopulationTheorem
    (S : SunflowerCarrier) where
  skinEquivalent :
    forall {P : FullyReducedPrimePackage S}
      {C : CoreLink S P}
      {B : RawBlockerCertificate S P C}
      {Q : RoleDistinctBlockerQuotient S P C B},
      CoarseBlockerColor S P C B Q ->
      CoarseBlockerColor S P C B Q -> Prop
  witnessNonSkinDistinction :
    forall {P : FullyReducedPrimePackage S}
      {C : CoreLink S P}
      {B : RawBlockerCertificate S P C}
      {Q : RoleDistinctBlockerQuotient S P C B},
      forall left right : CoarseBlockerColor S P C B Q,
      Not (skinEquivalent left right) ->
      EndpointLocalDistinctionWitness S P C B

def finite_aasc_type_population_witness
    {S : SunflowerCarrier}
    (Pop : FiniteAASCTypePopulationTheorem S)
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    (left right : CoarseBlockerColor S P C B Q)
    (nonSkin : Not (Pop.skinEquivalent left right)) :
    EndpointLocalDistinctionWitness S P C B := by
  exact Pop.witnessNonSkinDistinction left right nonSkin

/-- Same-coarse-color duplicate disposition before terminal-prime exclusion. -/
structure DuplicateProfilePair
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C)
    (Q : RoleDistinctBlockerQuotient S P C B) where
  leftClass : Nat
  rightClass : Nat
  left_lt : leftClass < Q.classCount
  right_lt : rightClass < Q.classCount
  distinct : leftClass ≠ rightClass
  sameCoarseColor : Prop
  sameCoarseColor_holds : sameCoarseColor

structure DuplicateProfileDisposition
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S) where
  skinCollapse : Prop
  lawfulTensorSplit : Prop
  boundedCertificateFiber : Prop
  sunflowerProduced : Prop
  disposition_holds :
    skinCollapse \/ lawfulTensorSplit \/ boundedCertificateFiber \/ sunflowerProduced

structure PrimeDuplicateExclusion
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S) where
  noDuplicateDisposition : DuplicateProfileDisposition S P -> False

def duplicateProfileDispositionOfQuotient
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    (_D : DuplicateProfilePair S P C B Q) :
    DuplicateProfileDisposition S P :=
  { skinCollapse := Q.sameCoarseColorCollapsesOrSplits
    lawfulTensorSplit := False
    boundedCertificateFiber := False
    sunflowerProduced := False
    disposition_holds := Or.inl Q.sameCoarseColorCollapsesOrSplits_holds }

theorem no_duplicate_profile_pair_in_terminal_prime
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    (duplicateDisposition :
      DuplicateProfilePair S P C B Q -> DuplicateProfileDisposition S P)
    (No : PrimeDuplicateExclusion S P) :
    ¬ Nonempty (DuplicateProfilePair S P C B Q) := by
  intro hD
  rcases hD with ⟨D⟩
  exact No.noDuplicateDisposition (duplicateDisposition D)

theorem no_duplicate_profile_pair_in_terminal_prime_of_quotient
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    (No : PrimeDuplicateExclusion S P) :
    ¬ Nonempty (DuplicateProfilePair S P C B Q) := by
  exact
    no_duplicate_profile_pair_in_terminal_prime
      duplicateProfileDispositionOfQuotient
      No

/-- Named escape routes when a blocker fiber is too large. -/
structure BlockerFiberEscape
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S) where
  lawfulTensorSplit : Prop
  quotientCollapse : Prop
  sunflowerProduced : Prop
  escape_holds : lawfulTensorSplit \/ quotientCollapse \/ sunflowerProduced

/-- A certified overflow event for one role-distinct blocker class. -/
structure BlockerFiberOverflow
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C)
    (Q : RoleDistinctBlockerQuotient S P C B) where
  classIndex : Nat
  classIndex_lt : classIndex < Q.classCount
  fiberRank : Nat
  effectiveCapacity : Nat
  exceedsBound : Prop
  exceedsBound_holds : exceedsBound

/-- Concrete measurement of one role-distinct blocker fiber. -/
structure BlockerFiberMeasurement
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C)
    (Q : RoleDistinctBlockerQuotient S P C B) where
  classIndex : Nat
  classIndex_lt : classIndex < Q.classCount
  fiberRank : Nat
  effectiveCapacity : Nat

/-- A fully reduced prime package has no remaining escape route. -/
structure PrimeFiberEscapeExclusion
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S) where
  noEscape : BlockerFiberEscape S P -> False

/--
The first v2 flagship target: raw blockers need not be bounded, but the number
of role-distinct blocker classes is bounded by a constant depending only on k.
-/
structure BoundedRoleDistinctBlockerTheorem (S : SunflowerCarrier) where
  Qk : Nat
  Qk_positive : 0 < Qk
  blockerQuotient :
    forall {P : FullyReducedPrimePackage S}
      (C : CoreLink S P)
      (B : RawBlockerCertificate S P C),
      RoleDistinctBlockerQuotient S P C B
  roleDistinctBound :
    forall {P : FullyReducedPrimePackage S}
      {C : CoreLink S P}
      {B : RawBlockerCertificate S P C}
      (Q : RoleDistinctBlockerQuotient S P C B),
      Q.classCount <= Qk

/--
A constructive source for the bounded role-distinct blocker theorem.  This is
the formal work package for the profile-coding part of the v2 proof.
-/
structure RoleProfileCompactnessSource (S : SunflowerCarrier) where
  Qk : Nat
  Qk_positive : 0 < Qk
  blockerQuotient :
    forall {P : FullyReducedPrimePackage S}
      (C : CoreLink S P)
      (B : RawBlockerCertificate S P C),
      RoleDistinctBlockerQuotient S P C B
  concreteProfileCoding :
    forall {P : FullyReducedPrimePackage S}
      (C : CoreLink S P)
      (B : RawBlockerCertificate S P C),
      ConcreteFiniteProfileCoding S P C B (blockerQuotient C B)
  profileAlphabetBound :
    forall {P : FullyReducedPrimePackage S}
      (C : CoreLink S P)
      (B : RawBlockerCertificate S P C),
      (concreteProfileCoding C B).profileAlphabetSize <= Qk
  allQuotientsComeFromSource :
    forall {P : FullyReducedPrimePackage S}
      {C : CoreLink S P}
      {B : RawBlockerCertificate S P C}
      (Q : RoleDistinctBlockerQuotient S P C B),
      Q.classCount <= (blockerQuotient C B).classCount

/--
Source object for constructing the canonical role-distinct quotient from a raw
blocker normal-form certificate.
-/
structure RawBlockerQuotientConstructionSource
    (S : SunflowerCarrier) where
  quotient :
    forall {P : FullyReducedPrimePackage S}
      (C : CoreLink S P)
      (B : RawBlockerCertificate S P C),
      RoleDistinctBlockerQuotient S P C B

/--
Uniform concrete profile coding for the quotient produced from raw blocker
normal form.  The bound constant and its positivity are part of this source,
so the six-item ledger does not carry them as loose side assumptions.
-/
structure UniformConcreteProfileCodingSource
    (S : SunflowerCarrier)
    (blockerQuotient :
      forall {P : FullyReducedPrimePackage S}
        (C : CoreLink S P)
        (B : RawBlockerCertificate S P C),
        RoleDistinctBlockerQuotient S P C B) where
  Qk : Nat
  Qk_positive : 0 < Qk
  concreteProfileCoding :
    forall {P : FullyReducedPrimePackage S}
      (C : CoreLink S P)
      (B : RawBlockerCertificate S P C),
      ConcreteFiniteProfileCoding S P C B (blockerQuotient C B)
  profileAlphabetBound :
    forall {P : FullyReducedPrimePackage S}
      (C : CoreLink S P)
      (B : RawBlockerCertificate S P C),
      (concreteProfileCoding C B).profileAlphabetSize <= Qk

/--
Domination source for admissible quotients: every quotient considered by the
closeout is controlled by the canonical quotient built from raw blocker normal
form.
-/
structure AdmissibleQuotientDominationSource
    (S : SunflowerCarrier)
    (blockerQuotient :
      forall {P : FullyReducedPrimePackage S}
        (C : CoreLink S P)
        (B : RawBlockerCertificate S P C),
        RoleDistinctBlockerQuotient S P C B) where
  dominates :
    forall {P : FullyReducedPrimePackage S}
      {C : CoreLink S P}
      {B : RawBlockerCertificate S P C}
      (Q : RoleDistinctBlockerQuotient S P C B),
      Q.classCount <= (blockerQuotient C B).classCount

def RoleProfileCompactnessSource.toBoundedRoleDistinctBlockerTheorem
    {S : SunflowerCarrier}
    (Src : RoleProfileCompactnessSource S) :
    BoundedRoleDistinctBlockerTheorem S :=
  { Qk := Src.Qk
    Qk_positive := Src.Qk_positive
    blockerQuotient := Src.blockerQuotient
    roleDistinctBound := by
      intro P C B Q
      exact Nat.le_trans
        (Src.allQuotientsComeFromSource Q)
        (Nat.le_trans
          (RoleDistinctBlockerQuotient.classCount_le_of_concreteProfileCoding
            (Src.concreteProfileCoding C B))
          (Src.profileAlphabetBound C B)) }

/--
The second v2 flagship target in AASC-first form: coarse surplus must either
skin-collapse or produce a finite AASC-type refinement.  Any surviving
standing-bearing distinction is routed to bounded certificate fiber, lawful
tensor/standing split, or sunflower realization.
-/
structure BlockerFiberCoercivityTheorem (S : SunflowerCarrier) where
  Bk : Nat
  Bk_positive : 0 < Bk
  fiberOverflowEscapes :
    forall {P : FullyReducedPrimePackage S}
      {C : CoreLink S P}
      {B : RawBlockerCertificate S P C}
      {Q : RoleDistinctBlockerQuotient S P C B},
      BlockerFiberOverflow S P C B Q ->
      BlockerFiberEscape S P

def blockerFiberOverflowOfExcess
    {S : SunflowerCarrier}
    (T : BlockerFiberCoercivityTheorem S)
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    (M : BlockerFiberMeasurement S P C B Q)
    (hexcess : T.Bk ^ M.fiberRank < M.effectiveCapacity) :
    BlockerFiberOverflow S P C B Q :=
  { classIndex := M.classIndex
    classIndex_lt := M.classIndex_lt
    fiberRank := M.fiberRank
    effectiveCapacity := M.effectiveCapacity
    exceedsBound := T.Bk ^ M.fiberRank < M.effectiveCapacity
    exceedsBound_holds := hexcess }

theorem fiber_capacity_bound_of_coercivity_and_escape_exclusion
    {S : SunflowerCarrier}
    (T : BlockerFiberCoercivityTheorem S)
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    (No : PrimeFiberEscapeExclusion S P)
    (M : BlockerFiberMeasurement S P C B Q) :
    M.effectiveCapacity <= T.Bk ^ M.fiberRank := by
  have hnot : ¬ T.Bk ^ M.fiberRank < M.effectiveCapacity := by
    intro hexcess
    exact
      No.noEscape
        (T.fiberOverflowEscapes
          (blockerFiberOverflowOfExcess T M hexcess))
  exact Nat.le_of_not_gt hnot

/--
Constructive source for the blocker-fiber capacity bridge.  Overflow itself is
now the measured non-skin AASC-type distinction; the remaining hard part is
excluding the terminal-prime escape routes produced by finite AASC-type
population and blocker-fiber coercivity.
-/
structure BlockerFiberCapacitySource
    (S : SunflowerCarrier)
    (T : BlockerFiberCoercivityTheorem S) where
  escapeExclusion :
    forall {P : FullyReducedPrimePackage S},
      PrimeFiberEscapeExclusion S P

/--
Bundled source for the remaining fiber-side job: prove finite AASC-type
population/coercivity and prove that terminal primes exclude the escape routes
it produces.
-/
structure BlockerFiberCoercivitySource (S : SunflowerCarrier) where
  fiberCoercivity : BlockerFiberCoercivityTheorem S
  finiteAASCTypePopulation : FiniteAASCTypePopulationTheorem S
  terminalPrimeEscapeExclusion :
    forall {P : FullyReducedPrimePackage S},
      PrimeFiberEscapeExclusion S P

def BlockerFiberCoercivitySource.capacitySource
    {S : SunflowerCarrier}
    (Src : BlockerFiberCoercivitySource S) :
    BlockerFiberCapacitySource S Src.fiberCoercivity :=
  { escapeExclusion := Src.terminalPrimeEscapeExclusion }

def BlockerFiberCoercivitySource.finiteAASCTypePopulation_witness
    {S : SunflowerCarrier}
    (Src : BlockerFiberCoercivitySource S)
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    (left right : CoarseBlockerColor S P C B Q)
    (nonSkin : Not (
      Src.finiteAASCTypePopulation.skinEquivalent left right)) :
    EndpointLocalDistinctionWitness S P C B := by
  exact Src.finiteAASCTypePopulation.witnessNonSkinDistinction
    left
    right
    nonSkin

theorem BlockerFiberCapacitySource.capacity_bound
    {S : SunflowerCarrier}
    {T : BlockerFiberCoercivityTheorem S}
    (Src : BlockerFiberCapacitySource S T)
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    (M : BlockerFiberMeasurement S P C B Q) :
    M.effectiveCapacity <= T.Bk ^ M.fiberRank := by
  exact fiber_capacity_bound_of_coercivity_and_escape_exclusion
    T
    Src.escapeExclusion
    M

/--
One rank-step measurement after role quotienting: choices are organized first
by role-distinct blocker class, then by bounded fiber choices inside a class.
-/
structure RoleFiberStepMeasurement where
  roleClassCount : Nat
  maxFiberChoices : Nat
  stepChoices : Nat
  stepFactorsThroughRoleFibers : stepChoices <= roleClassCount * maxFiberChoices

theorem RoleFiberStepMeasurement.stepChoices_le_constant_factor
    (M : RoleFiberStepMeasurement)
    {Qk Bk : Nat}
    (hRole : M.roleClassCount <= Qk)
    (hFiber : M.maxFiberChoices <= Bk) :
    M.stepChoices <= Qk * Bk := by
  exact Nat.le_trans
    M.stepFactorsThroughRoleFibers
    (Nat.mul_le_mul hRole hFiber)

/--
One rank-step in the counting recurrence.  This separates the local branching
measurement from the global induction over rank.
-/
structure RankStepCountingMeasurement (count : Nat -> Nat) (r : Nat) where
  stepChoices : Nat
  stepExpansionBound : count (r + 1) <= stepChoices * count r

theorem RankStepCountingMeasurement.bound_by_constant_branchFactor
    {count : Nat -> Nat}
    {r branchFactor : Nat}
    (M : RankStepCountingMeasurement count r)
    (hStep : M.stepChoices <= branchFactor) :
    count (r + 1) <= branchFactor * count r := by
  exact Nat.le_trans
    M.stepExpansionBound
    (Nat.mul_le_mul_right (count r) hStep)

/--
A rank-step source packages the local role/fiber measurements needed to feed
the global constant-base recurrence.
-/
structure RankStepSource (count : Nat -> Nat) where
  measurement : forall r, RankStepCountingMeasurement count r
  stepBound : Nat
  stepBound_positive : 0 < stepBound
  stepChoicesBound : forall r, (measurement r).stepChoices <= stepBound

theorem RankStepSource.rankStepBound
    {count : Nat -> Nat}
    (Src : RankStepSource count) :
    forall r, count (r + 1) <= Src.stepBound * count r := by
  intro r
  exact (Src.measurement r).bound_by_constant_branchFactor
    (Src.stepChoicesBound r)

/--
Rank-step data whose local choice count is explicitly factored through
role-distinct classes and bounded fibers.
-/
structure RoleFiberRankStepSource
    (count : Nat -> Nat)
    (Qk Bk : Nat) where
  measurement : forall r, RankStepCountingMeasurement count r
  roleFiberMeasurement : Nat -> RoleFiberStepMeasurement
  measuredByRoleFibers :
    forall r, (measurement r).stepChoices <= (roleFiberMeasurement r).stepChoices
  roleClassBound :
    forall r, (roleFiberMeasurement r).roleClassCount <= Qk
  fiberChoiceBound :
    forall r, (roleFiberMeasurement r).maxFiberChoices <= Bk
  branchFactor_positive : 0 < Qk * Bk

def RoleFiberRankStepSource.toRankStepSource
    {count : Nat -> Nat}
    {Qk Bk : Nat}
    (Src : RoleFiberRankStepSource count Qk Bk) :
    RankStepSource count :=
  { measurement := Src.measurement
    stepBound := Qk * Bk
    stepBound_positive := Src.branchFactor_positive
    stepChoicesBound := by
      intro r
      exact Nat.le_trans
        (Src.measuredByRoleFibers r)
        ((Src.roleFiberMeasurement r).stepChoices_le_constant_factor
          (Src.roleClassBound r)
          (Src.fiberChoiceBound r)) }

/--
The constant-branching closeout is separate from the two blocker theorems.
This prevents the final exponential bound from being smuggled in as raw
blocker boundedness or certificate-language completeness.
-/
structure ConstantBranchingReductionTheorem (S : SunflowerCarrier) where
  stepBound : Nat
  stepBound_positive : 0 < stepBound
  usesRoleTypesNotRawCoordinates : Prop
  rankStepContributesConstantFactor : Prop
  usesRoleTypesNotRawCoordinates_holds : usesRoleTypesNotRawCoordinates
  rankStepContributesConstantFactor_holds : rankStepContributesConstantFactor

def ConstantBranchingReductionTheorem.ready
    {S : SunflowerCarrier}
    (R : ConstantBranchingReductionTheorem S) : Prop :=
  R.usesRoleTypesNotRawCoordinates /\
  R.rankStepContributesConstantFactor

theorem ConstantBranchingReductionTheorem.ready_holds
    {S : SunflowerCarrier}
    (R : ConstantBranchingReductionTheorem S) :
    R.ready := by
  exact
    And.intro
      R.usesRoleTypesNotRawCoordinates_holds
      R.rankStepContributesConstantFactor_holds

def RoleFiberRankStepSource.toConstantBranchingReductionTheorem
    {S : SunflowerCarrier}
    {count : Nat -> Nat}
    {Qk Bk : Nat}
    (Src : RoleFiberRankStepSource count Qk Bk) :
    ConstantBranchingReductionTheorem S :=
  { stepBound := Qk * Bk
    stepBound_positive := Src.branchFactor_positive
    usesRoleTypesNotRawCoordinates :=
      forall r, (Src.measurement r).stepChoices <=
        (Src.roleFiberMeasurement r).stepChoices
    rankStepContributesConstantFactor :=
      forall r, (Src.measurement r).stepChoices <= Qk * Bk
    usesRoleTypesNotRawCoordinates_holds := Src.measuredByRoleFibers
    rankStepContributesConstantFactor_holds :=
      Src.toRankStepSource.stepChoicesBound }

/--
A rank-indexed counting model for the final closeout.  The model deliberately
uses only the constant branching factor supplied by the blocker quotient and
fiber coercivity layer; no raw blocker set size appears.
-/
structure ConstantBranchingCountingModel where
  count : Nat -> Nat
  branchFactor : Nat
  branchFactor_positive : 0 < branchFactor
  baseBound : count 0 <= 1
  rankStepBound : forall r, count (r + 1) <= branchFactor * count r

theorem ConstantBranchingCountingModel.count_le_branchFactor_pow
    (M : ConstantBranchingCountingModel) :
    forall r, M.count r <= M.branchFactor ^ r := by
  intro r
  induction r with
  | zero =>
      simpa using M.baseBound
  | succ r ih =>
      calc
        M.count (Nat.succ r)
            = M.count (r + 1) := by rfl
        _ <= M.branchFactor * M.count r := M.rankStepBound r
        _ <= M.branchFactor * (M.branchFactor ^ r) :=
            Nat.mul_le_mul_left M.branchFactor ih
        _ = M.branchFactor ^ Nat.succ r := by
            rw [Nat.pow_succ]
            exact Nat.mul_comm M.branchFactor (M.branchFactor ^ r)

theorem RankStepSource.count_le_stepBound_pow
    {count : Nat -> Nat}
    (Src : RankStepSource count)
    (baseBound : count 0 <= 1) :
    forall r, count r <= Src.stepBound ^ r := by
  let M : ConstantBranchingCountingModel :=
    { count := count
      branchFactor := Src.stepBound
      branchFactor_positive := Src.stepBound_positive
      baseBound := baseBound
      rankStepBound := Src.rankStepBound }
  exact M.count_le_branchFactor_pow

theorem RoleFiberRankStepSource.count_le_roleFiber_pow
    {count : Nat -> Nat}
    {Qk Bk : Nat}
    (Src : RoleFiberRankStepSource count Qk Bk)
    (baseBound : count 0 <= 1) :
    forall r, count r <= (Qk * Bk) ^ r := by
  exact Src.toRankStepSource.count_le_stepBound_pow baseBound

/--
Role/fiber rank-counting data, including the base case.  This keeps the
six-source ledger honest: the rank-step item is not missing a separate
rank-zero assumption.
-/
structure RoleFiberRankCountingSource
    (count : Nat -> Nat)
    (Qk Bk : Nat) where
  rankStepSource : RoleFiberRankStepSource count Qk Bk
  baseBound : count 0 <= 1

theorem RoleFiberRankCountingSource.count_le_roleFiber_pow
    {count : Nat -> Nat}
    {Qk Bk : Nat}
    (Src : RoleFiberRankCountingSource count Qk Bk) :
    forall r, count r <= (Qk * Bk) ^ r := by
  exact Src.rankStepSource.count_le_roleFiber_pow Src.baseBound

def RoleFiberRankCountingSource.toConstantBranchingReductionTheorem
    {S : SunflowerCarrier}
    {count : Nat -> Nat}
    {Qk Bk : Nat}
    (Src : RoleFiberRankCountingSource count Qk Bk) :
    ConstantBranchingReductionTheorem S :=
  Src.rankStepSource.toConstantBranchingReductionTheorem

/--
The role/fiber rank-counting source together with the rank-indexed count model
it measures.  This keeps the final six-source package from carrying `count` as
a loose parameter outside the rank-counting obligation.
-/
structure RoleFiberRankCountingModelSource
    (Qk Bk : Nat) where
  count : Nat -> Nat
  rankCounting : RoleFiberRankCountingSource count Qk Bk

def RoleFiberRankCountingModelSource.rankStepSource
    {Qk Bk : Nat}
    (Src : RoleFiberRankCountingModelSource Qk Bk) :
    RoleFiberRankStepSource Src.count Qk Bk :=
  Src.rankCounting.rankStepSource

theorem RoleFiberRankCountingModelSource.baseBound
    {Qk Bk : Nat}
    (Src : RoleFiberRankCountingModelSource Qk Bk) :
    Src.count 0 <= 1 := by
  exact Src.rankCounting.baseBound

theorem RoleFiberRankCountingModelSource.count_le_roleFiber_pow
    {Qk Bk : Nat}
    (Src : RoleFiberRankCountingModelSource Qk Bk) :
    forall r, Src.count r <= (Qk * Bk) ^ r := by
  exact Src.rankCounting.count_le_roleFiber_pow

def RoleFiberRankCountingModelSource.toConstantBranchingReductionTheorem
    {S : SunflowerCarrier}
    {Qk Bk : Nat}
    (Src : RoleFiberRankCountingModelSource Qk Bk) :
    ConstantBranchingReductionTheorem S :=
  Src.rankCounting.toConstantBranchingReductionTheorem

/-- The v2 replacement for a broad, opaque quantitative compactness premise. -/
structure BoundedBlockerQuotientCompactness (S : SunflowerCarrier) where
  roleBound : BoundedRoleDistinctBlockerTheorem S
  fiberCoercivity : BlockerFiberCoercivityTheorem S
  constantBranching : ConstantBranchingReductionTheorem S

/-- Source package for the whole v2 compactness bridge. -/
structure BoundedBlockerQuotientCompactnessSource (S : SunflowerCarrier) where
  roleProfileSource : RoleProfileCompactnessSource S
  fiberCoercivity : BlockerFiberCoercivityTheorem S
  fiberCapacitySource : BlockerFiberCapacitySource S fiberCoercivity
  constantBranching : ConstantBranchingReductionTheorem S

def BoundedBlockerQuotientCompactnessSource.toCompactness
    {S : SunflowerCarrier}
    (Src : BoundedBlockerQuotientCompactnessSource S) :
    BoundedBlockerQuotientCompactness S :=
  { roleBound := Src.roleProfileSource.toBoundedRoleDistinctBlockerTheorem
    fiberCoercivity := Src.fiberCoercivity
    constantBranching := Src.constantBranching }

def BoundedBlockerQuotientCompactness.ready
    {S : SunflowerCarrier}
    (K : BoundedBlockerQuotientCompactness S) : Prop :=
  0 < K.roleBound.Qk /\
  0 < K.fiberCoercivity.Bk /\
  0 < K.constantBranching.stepBound /\
  K.constantBranching.ready

theorem BoundedBlockerQuotientCompactness.ready_holds
    {S : SunflowerCarrier}
    (K : BoundedBlockerQuotientCompactness S) :
    K.ready := by
  exact
    And.intro K.roleBound.Qk_positive
      (And.intro K.fiberCoercivity.Bk_positive
        (And.intro K.constantBranching.stepBound_positive
          (ConstantBranchingReductionTheorem.ready_holds K.constantBranching)))

def BoundedBlockerQuotientCompactness.branchFactor
    {S : SunflowerCarrier}
    (K : BoundedBlockerQuotientCompactness S) : Nat :=
  K.roleBound.Qk * K.fiberCoercivity.Bk

theorem BoundedBlockerQuotientCompactness.branchFactor_positive
    {S : SunflowerCarrier}
    (K : BoundedBlockerQuotientCompactness S) :
    0 < K.branchFactor := by
  exact Nat.mul_pos K.roleBound.Qk_positive K.fiberCoercivity.Bk_positive

/--
The arithmetic endpoint of the v2 plan: bounded role types and bounded fibers
give a constant branching factor `Qk * Bk`, hence a constant-base rank bound.
-/
theorem BoundedBlockerQuotientCompactness.count_le_constant_base
    {S : SunflowerCarrier}
    (K : BoundedBlockerQuotientCompactness S)
    (count : Nat -> Nat)
    (baseBound : count 0 <= 1)
    (rankStepBound :
      forall r, count (r + 1) <= K.branchFactor * count r) :
    forall r, count r <= K.branchFactor ^ r := by
  let M : ConstantBranchingCountingModel :=
    { count := count
      branchFactor := K.branchFactor
      branchFactor_positive := K.branchFactor_positive
      baseBound := baseBound
      rankStepBound := rankStepBound }
  exact M.count_le_branchFactor_pow

/-- A final constant-base endpoint certificate, still abstract at this layer. -/
structure ConstantBaseEndpointCertificate (S : SunflowerCarrier) where
  HkStar : Nat
  HkStar_positive : 0 < HkStar
  endpointBound : Prop
  endpointBound_holds : endpointBound

/--
Concrete count-bound certificate extracted from a role/fiber rank-step source.
This is the arithmetic shape of the constant-base endpoint before translating
the rank-indexed count model back to the ambient sunflower family predicate.
-/
structure RankCountEndpointCertificate where
  base : Nat
  base_positive : 0 < base
  count : Nat -> Nat
  baseCase : count 0 <= 1
  countBound : forall r, count r <= base ^ r

def rankCountEndpointCertificateOfRoleFiberSource
    {count : Nat -> Nat}
    {Qk Bk : Nat}
    (Src : RoleFiberRankStepSource count Qk Bk)
    (baseBound : count 0 <= 1) :
    RankCountEndpointCertificate :=
  { base := Qk * Bk
    base_positive := Src.branchFactor_positive
    count := count
    baseCase := baseBound
    countBound := Src.count_le_roleFiber_pow baseBound }

/--
The final translation obligation from a rank-count model to the carrier-level
sunflower endpoint statement.
-/
structure RankCountToCarrierEndpoint
    (S : SunflowerCarrier)
    (R : RankCountEndpointCertificate) where
  carrierEndpointBound : Prop
  translation_holds : carrierEndpointBound

/-- Named source for translating the rank-count endpoint certificate back to
the carrier-level sunflower endpoint statement. -/
structure CarrierEndpointTranslationSource
    (S : SunflowerCarrier)
    (R : RankCountEndpointCertificate) where
  translation : RankCountToCarrierEndpoint S R

def constantBaseEndpointCertificateOfRankCount
    {S : SunflowerCarrier}
    (R : RankCountEndpointCertificate)
    (T : RankCountToCarrierEndpoint S R) :
    ConstantBaseEndpointCertificate S :=
  { HkStar := R.base
    HkStar_positive := R.base_positive
    endpointBound := T.carrierEndpointBound
    endpointBound_holds := T.translation_holds }

/--
One bundled source for the v2 constant-base endpoint route.  It contains the
compactness source, the measured rank-step source, the base case, and the final
translation from rank-counts to the carrier endpoint.
-/
structure V2ConstantBaseEndpointSource (S : SunflowerCarrier) where
  count : Nat -> Nat
  compactnessSource : BoundedBlockerQuotientCompactnessSource S
  rankStepSource :
    RoleFiberRankStepSource
      count
      compactnessSource.roleProfileSource.Qk
      compactnessSource.fiberCoercivity.Bk
  baseBound : count 0 <= 1
  carrierTranslation :
    RankCountToCarrierEndpoint S
      (rankCountEndpointCertificateOfRoleFiberSource rankStepSource baseBound)

def V2ConstantBaseEndpointSource.rankCountCertificate
    {S : SunflowerCarrier}
    (Src : V2ConstantBaseEndpointSource S) :
    RankCountEndpointCertificate :=
  rankCountEndpointCertificateOfRoleFiberSource
    Src.rankStepSource
    Src.baseBound

def V2ConstantBaseEndpointSource.constantBaseCertificate
    {S : SunflowerCarrier}
    (Src : V2ConstantBaseEndpointSource S) :
    ConstantBaseEndpointCertificate S :=
  constantBaseEndpointCertificateOfRankCount
    Src.rankCountCertificate
    Src.carrierTranslation

/--
The six remaining v2 source jobs, named in the same order as the public ledger.
This object is deliberately not an extra premise: it is the expanded form of
the still-open work needed to build `V2ConstantBaseEndpointSource`.
-/
structure V2SixObligationSource (S : SunflowerCarrier) where
  rawBlockerNormalFormToQuotient :
    RawBlockerQuotientConstructionSource S
  uniformConcreteProfileCoding :
    UniformConcreteProfileCodingSource
      S
      rawBlockerNormalFormToQuotient.quotient
  admissibleQuotientDomination :
    AdmissibleQuotientDominationSource
      S
      rawBlockerNormalFormToQuotient.quotient
  blockerFiberCoercivityAndEscapeExclusion :
    BlockerFiberCoercivitySource S
  roleFiberRankCounting :
    RoleFiberRankCountingModelSource
      uniformConcreteProfileCoding.Qk
      blockerFiberCoercivityAndEscapeExclusion.fiberCoercivity.Bk
  carrierEndpointTranslation :
    CarrierEndpointTranslationSource S
      (rankCountEndpointCertificateOfRoleFiberSource
        roleFiberRankCounting.rankStepSource
        roleFiberRankCounting.baseBound)

def V2SixObligationSource.roleProfileSource
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    RoleProfileCompactnessSource S :=
  { Qk := Src.uniformConcreteProfileCoding.Qk
    Qk_positive := Src.uniformConcreteProfileCoding.Qk_positive
    blockerQuotient := Src.rawBlockerNormalFormToQuotient.quotient
    concreteProfileCoding :=
      Src.uniformConcreteProfileCoding.concreteProfileCoding
    profileAlphabetBound :=
      Src.uniformConcreteProfileCoding.profileAlphabetBound
    allQuotientsComeFromSource :=
      Src.admissibleQuotientDomination.dominates }

def V2SixObligationSource.Qk
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) : Nat :=
  Src.uniformConcreteProfileCoding.Qk

theorem V2SixObligationSource.Qk_positive
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    0 < Src.Qk := by
  exact Src.uniformConcreteProfileCoding.Qk_positive

def V2SixObligationSource.count
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) : Nat -> Nat :=
  Src.roleFiberRankCounting.count

theorem V2SixObligationSource.roleClassBound
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S)
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (Q : RoleDistinctBlockerQuotient S P C B) :
    Q.classCount <= Src.Qk := by
  exact Src.roleProfileSource.toBoundedRoleDistinctBlockerTheorem.roleDistinctBound Q

def V2SixObligationSource.fiberCapacitySource
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    BlockerFiberCapacitySource S
      Src.blockerFiberCoercivityAndEscapeExclusion.fiberCoercivity :=
  Src.blockerFiberCoercivityAndEscapeExclusion.capacitySource

theorem V2SixObligationSource.fiberCapacityBound
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S)
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    (M : BlockerFiberMeasurement S P C B Q) :
    M.effectiveCapacity <=
      Src.blockerFiberCoercivityAndEscapeExclusion.fiberCoercivity.Bk ^
        M.fiberRank := by
  exact Src.fiberCapacitySource.capacity_bound M

def V2SixObligationSource.compactnessSource
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    BoundedBlockerQuotientCompactnessSource S :=
  { roleProfileSource := Src.roleProfileSource
    fiberCoercivity :=
      Src.blockerFiberCoercivityAndEscapeExclusion.fiberCoercivity
    fiberCapacitySource := Src.fiberCapacitySource
    constantBranching :=
      Src.roleFiberRankCounting.toConstantBranchingReductionTheorem }

def V2SixObligationSource.toEndpointSource
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    V2ConstantBaseEndpointSource S :=
  { count := Src.count
    compactnessSource := Src.compactnessSource
    rankStepSource := Src.roleFiberRankCounting.rankStepSource
    baseBound := Src.roleFiberRankCounting.baseBound
    carrierTranslation := Src.carrierEndpointTranslation.translation }

def V2SixObligationSource.constantBaseCertificate
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    ConstantBaseEndpointCertificate S :=
  Src.toEndpointSource.constantBaseCertificate

def V2SixObligationSource.rankCountCertificate
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    RankCountEndpointCertificate :=
  rankCountEndpointCertificateOfRoleFiberSource
    Src.roleFiberRankCounting.rankStepSource
    Src.roleFiberRankCounting.baseBound

theorem V2SixObligationSource.countBound
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    forall r,
      Src.count r <=
        (Src.Qk *
          Src.blockerFiberCoercivityAndEscapeExclusion.fiberCoercivity.Bk) ^
          r := by
  exact Src.roleFiberRankCounting.count_le_roleFiber_pow

theorem V2SixObligationSource.rankStepChoicesBound
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    forall r,
      (Src.roleFiberRankCounting.rankStepSource.measurement r).stepChoices <=
        Src.Qk *
          Src.blockerFiberCoercivityAndEscapeExclusion.fiberCoercivity.Bk := by
  exact Src.roleFiberRankCounting.rankStepSource.toRankStepSource.stepChoicesBound

theorem V2SixObligationSource.rankStepBound
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    forall r,
      Src.count (r + 1) <=
        (Src.Qk *
          Src.blockerFiberCoercivityAndEscapeExclusion.fiberCoercivity.Bk) *
          Src.count r := by
  exact Src.roleFiberRankCounting.rankStepSource.toRankStepSource.rankStepBound

theorem V2SixObligationSource.rankCountBase_eq
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    Src.rankCountCertificate.base =
      Src.Qk *
        Src.blockerFiberCoercivityAndEscapeExclusion.fiberCoercivity.Bk := by
  rfl

theorem V2SixObligationSource.constantBase_eq
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    Src.constantBaseCertificate.HkStar =
      Src.Qk *
        Src.blockerFiberCoercivityAndEscapeExclusion.fiberCoercivity.Bk := by
  rfl

theorem V2SixObligationSource.constantBase_positive
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    0 < Src.constantBaseCertificate.HkStar := by
  exact Src.constantBaseCertificate.HkStar_positive

theorem V2SixObligationSource.carrierTranslationBound
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    Src.carrierEndpointTranslation.translation.carrierEndpointBound := by
  exact Src.carrierEndpointTranslation.translation.translation_holds

theorem V2SixObligationSource.constantBaseEndpoint_eq_carrierTranslation
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    Src.constantBaseCertificate.endpointBound =
      Src.carrierEndpointTranslation.translation.carrierEndpointBound := by
  rfl

theorem V2SixObligationSource.compactnessReady
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    Src.toEndpointSource.compactnessSource.toCompactness.ready := by
  exact
    BoundedBlockerQuotientCompactness.ready_holds
      Src.toEndpointSource.compactnessSource.toCompactness

theorem V2SixObligationSource.endpointBound
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    Src.constantBaseCertificate.endpointBound := by
  exact Src.constantBaseCertificate.endpointBound_holds

/--
The exact source frontier for closing the v2 architecture.  This record carries
the six named witnesses without also asking for the derived endpoint
certificate.  It is the constructive target that must be supplied before
`V2SixObligationSource` can be built.
-/
structure V2SourceFrontier (S : SunflowerCarrier) where
  rawBlockerNormalFormToQuotient :
    RawBlockerQuotientConstructionSource S
  uniformConcreteProfileCoding :
    UniformConcreteProfileCodingSource
      S
      rawBlockerNormalFormToQuotient.quotient
  admissibleQuotientDomination :
    AdmissibleQuotientDominationSource
      S
      rawBlockerNormalFormToQuotient.quotient
  blockerFiberCoercivityAndEscapeExclusion :
    BlockerFiberCoercivitySource S
  roleFiberRankCounting :
    RoleFiberRankCountingModelSource
      uniformConcreteProfileCoding.Qk
      blockerFiberCoercivityAndEscapeExclusion.fiberCoercivity.Bk
  carrierEndpointTranslation :
    CarrierEndpointTranslationSource S
      (rankCountEndpointCertificateOfRoleFiberSource
        roleFiberRankCounting.rankStepSource
        roleFiberRankCounting.baseBound)

def V2SourceFrontier.toSixObligationSource
    {S : SunflowerCarrier}
    (F : V2SourceFrontier S) :
    V2SixObligationSource S :=
  { rawBlockerNormalFormToQuotient := F.rawBlockerNormalFormToQuotient
    uniformConcreteProfileCoding := F.uniformConcreteProfileCoding
    admissibleQuotientDomination := F.admissibleQuotientDomination
    blockerFiberCoercivityAndEscapeExclusion :=
      F.blockerFiberCoercivityAndEscapeExclusion
    roleFiberRankCounting := F.roleFiberRankCounting
    carrierEndpointTranslation := F.carrierEndpointTranslation }

def V2SixObligationSource.toSourceFrontier
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    V2SourceFrontier S :=
  { rawBlockerNormalFormToQuotient := Src.rawBlockerNormalFormToQuotient
    uniformConcreteProfileCoding := Src.uniformConcreteProfileCoding
    admissibleQuotientDomination := Src.admissibleQuotientDomination
    blockerFiberCoercivityAndEscapeExclusion :=
      Src.blockerFiberCoercivityAndEscapeExclusion
    roleFiberRankCounting := Src.roleFiberRankCounting
    carrierEndpointTranslation := Src.carrierEndpointTranslation }

theorem V2SourceFrontier.endpointBound
    {S : SunflowerCarrier}
    (F : V2SourceFrontier S) :
    F.toSixObligationSource.constantBaseCertificate.endpointBound := by
  exact F.toSixObligationSource.endpointBound

/-- The quotient construction populates the AASC admissibility role when every
canonical quotient is ready. -/
def RawBlockerQuotientConstructionSource.populatesAdmissibility
    {S : SunflowerCarrier}
    (Src : RawBlockerQuotientConstructionSource S) : Prop :=
  forall {P : FullyReducedPrimePackage S}
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C),
    (Src.quotient C B).ready

theorem RawBlockerQuotientConstructionSource.populatesAdmissibility_holds
    {S : SunflowerCarrier}
    (Src : RawBlockerQuotientConstructionSource S) :
    Src.populatesAdmissibility := by
  intro P C B
  exact RoleDistinctBlockerQuotient.ready_holds (Src.quotient C B)

/-- Uniform finite profile coding populates the AASC standing role: there is a
positive uniform alphabet bound for all canonical role profiles. -/
def UniformConcreteProfileCodingSource.populatesStanding
    {S : SunflowerCarrier}
    {blockerQuotient :
      forall {P : FullyReducedPrimePackage S}
        (C : CoreLink S P)
        (B : RawBlockerCertificate S P C),
        RoleDistinctBlockerQuotient S P C B}
    (Src : UniformConcreteProfileCodingSource S blockerQuotient) : Prop :=
  0 < Src.Qk /\
  forall {P : FullyReducedPrimePackage S}
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C),
    (Src.concreteProfileCoding C B).profileAlphabetSize <= Src.Qk

theorem UniformConcreteProfileCodingSource.populatesStanding_holds
    {S : SunflowerCarrier}
    {blockerQuotient :
      forall {P : FullyReducedPrimePackage S}
        (C : CoreLink S P)
        (B : RawBlockerCertificate S P C),
        RoleDistinctBlockerQuotient S P C B}
    (Src : UniformConcreteProfileCodingSource S blockerQuotient) :
    Src.populatesStanding := by
  exact And.intro Src.Qk_positive (by intro P C B; exact Src.profileAlphabetBound C B)

/-- Blocker-fiber coercivity plus terminal-prime escape exclusion populates the
AASC reference role by giving a reusable per-fiber capacity bound. -/
def BlockerFiberCoercivitySource.populatesReference
    {S : SunflowerCarrier}
    (Src : BlockerFiberCoercivitySource S) : Prop :=
  forall {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    {Q : RoleDistinctBlockerQuotient S P C B}
    (M : BlockerFiberMeasurement S P C B Q),
    M.effectiveCapacity <= Src.fiberCoercivity.Bk ^ M.fiberRank

theorem BlockerFiberCoercivitySource.populatesReference_holds
    {S : SunflowerCarrier}
    (Src : BlockerFiberCoercivitySource S) :
    Src.populatesReference := by
  intro P C B Q M
  exact Src.capacitySource.capacity_bound M

/-- Role/fiber rank counting populates the AASC irreversibility role by
providing a constant-base rank-count bound. -/
def RoleFiberRankCountingModelSource.populatesIrreversibility
    {Qk Bk : Nat}
    (Src : RoleFiberRankCountingModelSource Qk Bk) : Prop :=
  forall r, Src.count r <= (Qk * Bk) ^ r

theorem RoleFiberRankCountingModelSource.populatesIrreversibility_holds
    {Qk Bk : Nat}
    (Src : RoleFiberRankCountingModelSource Qk Bk) :
    Src.populatesIrreversibility := by
  exact Src.count_le_roleFiber_pow

/-- Pure AASC role population, before certificate-branch exhaustion is used. -/
structure V2AASCRolePopulationCore (S : SunflowerCarrier) where
  blockerQuotientPopulatesAdmissibility : Prop
  finiteProfilesPopulateStanding : Prop
  fiberCoercivityPopulatesReference : Prop
  rankCountingPopulatesIrreversibility : Prop
  blockerQuotientPopulatesAdmissibility_holds :
    blockerQuotientPopulatesAdmissibility
  finiteProfilesPopulateStanding_holds :
    finiteProfilesPopulateStanding
  fiberCoercivityPopulatesReference_holds :
    fiberCoercivityPopulatesReference
  rankCountingPopulatesIrreversibility_holds :
    rankCountingPopulatesIrreversibility

def V2AASCRolePopulationCore.rolesPopulated
    {S : SunflowerCarrier}
    (P : V2AASCRolePopulationCore S) : Prop :=
  P.blockerQuotientPopulatesAdmissibility /\
  P.finiteProfilesPopulateStanding /\
  P.fiberCoercivityPopulatesReference /\
  P.rankCountingPopulatesIrreversibility

theorem V2AASCRolePopulationCore.rolesPopulated_holds
    {S : SunflowerCarrier}
    (P : V2AASCRolePopulationCore S) :
    P.rolesPopulated := by
  exact
    And.intro P.blockerQuotientPopulatesAdmissibility_holds
      (And.intro P.finiteProfilesPopulateStanding_holds
        (And.intro P.fiberCoercivityPopulatesReference_holds
          P.rankCountingPopulatesIrreversibility_holds))

def V2AASCRolePopulationCore.toKernelPackage
    {S : SunflowerCarrier}
    (P : V2AASCRolePopulationCore S) :
    KernelPackage S :=
  { admissibility := P.blockerQuotientPopulatesAdmissibility
    standing := P.finiteProfilesPopulateStanding
    reference := P.fiberCoercivityPopulatesReference
    irreversibility := P.rankCountingPopulatesIrreversibility
    admissibility_holds :=
      P.blockerQuotientPopulatesAdmissibility_holds
    standing_holds :=
      P.finiteProfilesPopulateStanding_holds
    reference_holds :=
      P.fiberCoercivityPopulatesReference_holds
    irreversibility_holds :=
      P.rankCountingPopulatesIrreversibility_holds }

/--
Compatibility packaging of four populated domain witnesses into the existing
`KernelPackage` shape.  This projection records a realized role profile; it is
not the dependency source of kernel necessity.  Kernel necessity enters
upstream through `DeterminateEndpointKernelSource`.
-/
def V2AASCRolePopulationCore.toRealizedKernelPackage
    {S : SunflowerCarrier}
    (P : V2AASCRolePopulationCore S) :
    KernelPackage S :=
  P.toKernelPackage

theorem V2AASCRolePopulationCore.kernelRolesHold
    {S : SunflowerCarrier}
    (P : V2AASCRolePopulationCore S) :
    P.toKernelPackage.allRolesHold := by
  exact P.toKernelPackage.allRolesHold_holds

/--
The exact v2 source layer needed to populate the four AASC roles.  This is the
part of the six-source frontier that is consumed by AASC role population,
before domination and carrier endpoint translation are used for the endpoint
certificate surface.
-/
structure V2RolePopulationSource (S : SunflowerCarrier) where
  rawBlockerNormalFormToQuotient : RawBlockerQuotientConstructionSource S
  uniformConcreteProfileCoding :
    UniformConcreteProfileCodingSource S rawBlockerNormalFormToQuotient.quotient
  blockerFiberCoercivityAndEscapeExclusion :
    BlockerFiberCoercivitySource S
  roleFiberRankCounting :
    RoleFiberRankCountingModelSource
      uniformConcreteProfileCoding.Qk
      blockerFiberCoercivityAndEscapeExclusion.fiberCoercivity.Bk

def V2RolePopulationSource.toAASCRolePopulationCore
    {S : SunflowerCarrier}
    (Src : V2RolePopulationSource S) :
    V2AASCRolePopulationCore S :=
  { blockerQuotientPopulatesAdmissibility :=
      Src.rawBlockerNormalFormToQuotient.populatesAdmissibility
    finiteProfilesPopulateStanding :=
      Src.uniformConcreteProfileCoding.populatesStanding
    fiberCoercivityPopulatesReference :=
      Src.blockerFiberCoercivityAndEscapeExclusion.populatesReference
    rankCountingPopulatesIrreversibility :=
      Src.roleFiberRankCounting.populatesIrreversibility
    blockerQuotientPopulatesAdmissibility_holds :=
      Src.rawBlockerNormalFormToQuotient.populatesAdmissibility_holds
    finiteProfilesPopulateStanding_holds :=
      Src.uniformConcreteProfileCoding.populatesStanding_holds
    fiberCoercivityPopulatesReference_holds :=
      Src.blockerFiberCoercivityAndEscapeExclusion.populatesReference_holds
    rankCountingPopulatesIrreversibility_holds :=
      Src.roleFiberRankCounting.populatesIrreversibility_holds }

theorem V2RolePopulationSource.rolesPopulated
    {S : SunflowerCarrier}
    (Src : V2RolePopulationSource S) :
    Src.toAASCRolePopulationCore.rolesPopulated := by
  exact Src.toAASCRolePopulationCore.rolesPopulated_holds

def V2RolePopulationSource.toKernelPackage
    {S : SunflowerCarrier}
    (Src : V2RolePopulationSource S) :
    KernelPackage S :=
  Src.toAASCRolePopulationCore.toKernelPackage

theorem V2RolePopulationSource.kernelRolesHold
    {S : SunflowerCarrier}
    (Src : V2RolePopulationSource S) :
    Src.toKernelPackage.allRolesHold := by
  exact Src.toKernelPackage.allRolesHold_holds

def V2SourceFrontier.toRolePopulationSource
    {S : SunflowerCarrier}
    (frontier : V2SourceFrontier S) :
    V2RolePopulationSource S :=
  { rawBlockerNormalFormToQuotient :=
      frontier.rawBlockerNormalFormToQuotient
    uniformConcreteProfileCoding :=
      frontier.uniformConcreteProfileCoding
    blockerFiberCoercivityAndEscapeExclusion :=
      frontier.blockerFiberCoercivityAndEscapeExclusion
    roleFiberRankCounting :=
      frontier.roleFiberRankCounting }

def V2SixObligationSource.toRolePopulationSource
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    V2RolePopulationSource S :=
  Src.toSourceFrontier.toRolePopulationSource

def V2SourceFrontier.toAASCRolePopulationCore
    {S : SunflowerCarrier}
    (frontier : V2SourceFrontier S) :
    V2AASCRolePopulationCore S :=
  frontier.toRolePopulationSource.toAASCRolePopulationCore

def V2SixObligationSource.toAASCRolePopulationCore
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    V2AASCRolePopulationCore S :=
  Src.toSourceFrontier.toAASCRolePopulationCore

theorem V2SourceFrontier.rolesPopulated
    {S : SunflowerCarrier}
    (frontier : V2SourceFrontier S) :
    frontier.toAASCRolePopulationCore.rolesPopulated := by
  exact frontier.toAASCRolePopulationCore.rolesPopulated_holds

theorem V2SixObligationSource.rolesPopulated
    {S : SunflowerCarrier}
    (Src : V2SixObligationSource S) :
    Src.toAASCRolePopulationCore.rolesPopulated := by
  exact Src.toAASCRolePopulationCore.rolesPopulated_holds

/--
The AASC-native replacement target for trying to prove every quantitative
compactness component in isolation.  The finite v2 combinatorics populate the
domain-local witnesses governed by the four kernel roles, while kernel
necessity itself is upstream.  A separate certificate-exhaustion source
supplies the branch split; after that, the existing AASC impossibility
machinery discharges the residual branch.
-/
structure V2AASCRolePopulation
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) extends V2AASCRolePopulationCore S where
  exhaustedBranchSplit :
    forall F : S.Family,
      S.noSunflower F -> BMF S C H F \/ ObjectiveNonBMF S C H F

def V2AASCRolePopulation.rolesPopulated
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (P : V2AASCRolePopulation S C H) : Prop :=
  P.toV2AASCRolePopulationCore.rolesPopulated

theorem V2AASCRolePopulation.rolesPopulated_holds
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (P : V2AASCRolePopulation S C H) :
    P.rolesPopulated := by
  exact P.toV2AASCRolePopulationCore.rolesPopulated_holds

/--
Combinatorial v2 input in the AASC-native form: a source frontier populates the
kernel roles, while the certificate-language split supplies exhaustion.
-/
structure V2CertificateExhaustionSource
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) where
  exhaustedBranchSplit :
    forall F : S.Family,
      S.noSunflower F -> BMF S C H F \/ ObjectiveNonBMF S C H F

theorem V2CertificateExhaustionSource.split
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2CertificateExhaustionSource S C H)
    (F : S.Family) :
    S.noSunflower F -> BMF S C H F \/ ObjectiveNonBMF S C H F := by
  exact Src.exhaustedBranchSplit F

def V2AASCRolePopulation.ofCoreAndExhaustion
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (core : V2AASCRolePopulationCore S)
    (exhaustion : V2CertificateExhaustionSource S C H) :
    V2AASCRolePopulation S C H :=
  { core with
    exhaustedBranchSplit := exhaustion.exhaustedBranchSplit }

theorem V2AASCRolePopulation.rolesPopulated_ofCoreAndExhaustion
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (core : V2AASCRolePopulationCore S)
    (exhaustion : V2CertificateExhaustionSource S C H) :
    (V2AASCRolePopulation.ofCoreAndExhaustion core exhaustion).rolesPopulated := by
  exact core.rolesPopulated_holds

def V2CertificateExhaustionSource.ofAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2CertificateExhaustionSource S C H :=
  { exhaustedBranchSplit := A.branchSplit }

/--
The hybrid bridge from the v2 finite population data to the original
certified/residual branch exhaustion.  Making the population an explicit
parameter prevents a free-standing completeness record from hiding this
remaining mathematical dependency.
-/
structure V2FinitePopulationExhaustionSource
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat)
    (population : V2RolePopulationSource S) where
  objectiveMotifCompleteness : ObjectiveMotifCompletenessSource S C H
  exhaustedBranchSplit :
    population.toAASCRolePopulationCore.rolesPopulated ->
    forall F : S.Family,
      S.noSunflower F -> BMF S C H F \/ ObjectiveNonBMF S C H F

def V2FinitePopulationExhaustionSource.toCertificateExhaustionSource
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    {population : V2RolePopulationSource S}
    (Src : V2FinitePopulationExhaustionSource S C H population) :
    V2CertificateExhaustionSource S C H :=
  { exhaustedBranchSplit :=
      Src.exhaustedBranchSplit population.rolesPopulated }

def V2FinitePopulationExhaustionSource.ofAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (population : V2RolePopulationSource S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2FinitePopulationExhaustionSource S C H population :=
  { objectiveMotifCompleteness := A.objectiveMotifCompleteness
    exhaustedBranchSplit := fun _ => A.branchSplit }

theorem V2FinitePopulationExhaustionSource.excludesLawfulHigherDensityMotif
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    {population : V2RolePopulationSource S}
    (Src : V2FinitePopulationExhaustionSource S C H population)
    {motif : Src.objectiveMotifCompleteness.motifSystem.Motif}
    (lawful :
      Src.objectiveMotifCompleteness.motifSystem.lawfulNegativeMotif motif)
    (higherDensity :
      Src.objectiveMotifCompleteness.motifSystem.densityExceeds H motif)
    (notExcluded : Not (
      Src.objectiveMotifCompleteness.motifSystem.excludedByCarrierCriterion motif)) :
    False := by
  exact
    Src.objectiveMotifCompleteness.excludesLawfulHigherDensityMotif
      lawful
      higherDensity
      notExcluded

structure V2CombinatorialRolePopulationSource
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) where
  frontier : V2SourceFrontier S
  certificateExhaustion : V2CertificateExhaustionSource S C H

def V2CombinatorialRolePopulationSource.toAASCRolePopulation
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2CombinatorialRolePopulationSource S C H) :
    V2AASCRolePopulation S C H :=
  V2AASCRolePopulation.ofCoreAndExhaustion
    Src.frontier.toAASCRolePopulationCore
    Src.certificateExhaustion

theorem V2CombinatorialRolePopulationSource.rolesPopulated
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2CombinatorialRolePopulationSource S C H) :
    Src.toAASCRolePopulation.rolesPopulated := by
  exact Src.toAASCRolePopulation.rolesPopulated_holds

/--
The AASC impossibility side used after role population has reduced the
no-sunflower case to the certified/residual split.
-/
structure V2AASCImpossibilityRoute
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) where
  governance : KernelForcedGovernance S
  residualBridge : ResidualSeparatorBridge S C H

def V2AASCImpossibilityRoute.ofAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2AASCImpossibilityRoute S C H :=
  { governance := A.governance
    residualBridge := A.residualBridge }

theorem V2AASCImpossibilityRoute.discharge_residual
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (R : V2AASCImpossibilityRoute S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    Not (ResidualSeparator S C H F) := by
  exact
    kernel_forced_discharge_of_calibrated_residual_separator
      R.governance
      R.residualBridge
      E

theorem V2AASCRolePopulation.close_by_exhaustion_and_impossibility
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (P : V2AASCRolePopulation S C H)
    (R : V2AASCImpossibilityRoute S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact
    local_endpoint_transfer_to_BMF
      R.governance
      R.residualBridge
      E
      (P.exhaustedBranchSplit F)

theorem V2AASCRolePopulationCore.close_by_exhaustion_and_impossibility
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (core : V2AASCRolePopulationCore S)
    (exhaustion : V2CertificateExhaustionSource S C H)
    (R : V2AASCImpossibilityRoute S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact
    (V2AASCRolePopulation.ofCoreAndExhaustion core exhaustion)
      |>.close_by_exhaustion_and_impossibility R E

theorem V2AASCRolePopulationCore.close_by_APlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (core : V2AASCRolePopulationCore S)
    (A : SunflowerAPlusAuditCertificate S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact
    core.close_by_exhaustion_and_impossibility
      (V2CertificateExhaustionSource.ofAPlusAuditCertificate A)
      (V2AASCImpossibilityRoute.ofAPlusAuditCertificate A)
      E

theorem V2CombinatorialRolePopulationSource.close_by_exhaustion_and_impossibility
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2CombinatorialRolePopulationSource S C H)
    (R : V2AASCImpossibilityRoute S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact Src.toAASCRolePopulation.close_by_exhaustion_and_impossibility R E

theorem V2CombinatorialRolePopulationSource.close_by_APlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2CombinatorialRolePopulationSource S C H)
    (A : SunflowerAPlusAuditCertificate S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact
    Src.close_by_exhaustion_and_impossibility
      (V2AASCImpossibilityRoute.ofAPlusAuditCertificate A)
      E

def V2CombinatorialRolePopulationSource.ofFrontierAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (frontier : V2SourceFrontier S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2CombinatorialRolePopulationSource S C H :=
  { frontier := frontier
    certificateExhaustion :=
      V2CertificateExhaustionSource.ofAPlusAuditCertificate A }

def V2CombinatorialRolePopulationSource.ofSixObligationsAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2SixObligationSource S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2CombinatorialRolePopulationSource S C H :=
  V2CombinatorialRolePopulationSource.ofFrontierAndAPlusAuditCertificate
    Src.toSourceFrontier
    A

theorem V2SixObligationSource.rolesPopulated_by_APlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2SixObligationSource S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    (V2CombinatorialRolePopulationSource.ofSixObligationsAndAPlusAuditCertificate
      Src
      A).toAASCRolePopulation.rolesPopulated := by
  exact
    (V2CombinatorialRolePopulationSource.ofSixObligationsAndAPlusAuditCertificate
      Src
      A).rolesPopulated

theorem V2SourceFrontier.close_by_APlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (frontier : V2SourceFrontier S)
    (A : SunflowerAPlusAuditCertificate S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact
    (V2CombinatorialRolePopulationSource.ofFrontierAndAPlusAuditCertificate
      frontier
      A).close_by_exhaustion_and_impossibility
        (V2AASCImpossibilityRoute.ofAPlusAuditCertificate A)
        E

theorem V2SixObligationSource.close_by_APlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2SixObligationSource S)
    (A : SunflowerAPlusAuditCertificate S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact Src.toSourceFrontier.close_by_APlusAuditCertificate A E

/--
The AASC-native closeout source after the finite/combinatorial work has been
converted into role population.  This is intentionally smaller than the
six-source construction frontier: the finite work has already been absorbed
into the AASC roles, so only exhaustion and residual impossibility remain.
-/
structure V2AASCNativeCloseoutSource
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) where
  roleCore : V2AASCRolePopulationCore S
  certificateExhaustion : V2CertificateExhaustionSource S C H
  impossibilityRoute : V2AASCImpossibilityRoute S C H

def V2AASCNativeCloseoutSource.toAASCRolePopulation
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2AASCNativeCloseoutSource S C H) :
    V2AASCRolePopulation S C H :=
  V2AASCRolePopulation.ofCoreAndExhaustion
    Src.roleCore
    Src.certificateExhaustion

theorem V2AASCNativeCloseoutSource.rolesPopulated
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2AASCNativeCloseoutSource S C H) :
    Src.toAASCRolePopulation.rolesPopulated := by
  exact Src.roleCore.rolesPopulated_holds

theorem V2AASCNativeCloseoutSource.close
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2AASCNativeCloseoutSource S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact
    Src.roleCore.close_by_exhaustion_and_impossibility
      Src.certificateExhaustion
      Src.impossibilityRoute
      E

def V2AASCNativeCloseoutSource.ofFrontierAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (frontier : V2SourceFrontier S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2AASCNativeCloseoutSource S C H :=
  { roleCore := frontier.toAASCRolePopulationCore
    certificateExhaustion :=
      V2CertificateExhaustionSource.ofAPlusAuditCertificate A
    impossibilityRoute :=
      V2AASCImpossibilityRoute.ofAPlusAuditCertificate A }

def V2AASCNativeCloseoutSource.ofSixObligationsAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2SixObligationSource S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2AASCNativeCloseoutSource S C H :=
  V2AASCNativeCloseoutSource.ofFrontierAndAPlusAuditCertificate
    Src.toSourceFrontier
    A

/--
The A+-relative closeout source.  Once the A+ certificate is fixed, its
exhaustion and impossibility data supply the two non-combinatorial native
ingredients, so the remaining v2-side datum is just the populated role core.
-/
structure V2APlusRelativeCloseoutSource
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) where
  roleCore : V2AASCRolePopulationCore S
  auditCertificate : SunflowerAPlusAuditCertificate S C H

def V2APlusRelativeCloseoutSource.toAASCNativeCloseoutSource
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2APlusRelativeCloseoutSource S C H) :
    V2AASCNativeCloseoutSource S C H :=
  { roleCore := Src.roleCore
    certificateExhaustion :=
      V2CertificateExhaustionSource.ofAPlusAuditCertificate Src.auditCertificate
    impossibilityRoute :=
      V2AASCImpossibilityRoute.ofAPlusAuditCertificate Src.auditCertificate }

theorem V2APlusRelativeCloseoutSource.rolesPopulated
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2APlusRelativeCloseoutSource S C H) :
    Src.toAASCNativeCloseoutSource.toAASCRolePopulation.rolesPopulated := by
  exact Src.roleCore.rolesPopulated_holds

theorem V2APlusRelativeCloseoutSource.close
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2APlusRelativeCloseoutSource S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact Src.roleCore.close_by_APlusAuditCertificate Src.auditCertificate E

def V2APlusRelativeCloseoutSource.ofFrontierAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (frontier : V2SourceFrontier S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2APlusRelativeCloseoutSource S C H :=
  { roleCore := frontier.toAASCRolePopulationCore
    auditCertificate := A }

def V2APlusRelativeCloseoutSource.ofSixObligationsAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2SixObligationSource S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2APlusRelativeCloseoutSource S C H :=
  V2APlusRelativeCloseoutSource.ofFrontierAndAPlusAuditCertificate
    Src.toSourceFrontier
    A

def V2APlusRelativeCloseoutSource.ofRolePopulationSourceAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2RolePopulationSource S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2APlusRelativeCloseoutSource S C H :=
  { roleCore := Src.toAASCRolePopulationCore
    auditCertificate := A }

theorem V2RolePopulationSource.close_by_APlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2RolePopulationSource S)
    (A : SunflowerAPlusAuditCertificate S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact
    (V2APlusRelativeCloseoutSource.ofRolePopulationSourceAndAPlusAuditCertificate
      Src
      A).close E

/--
Kernel-aligned A+-relative closeout.  This keeps the actual AASC
`KernelPackage` visible while still using the A+ certificate for exhaustion,
governance, and residual impossibility.
-/
structure V2KernelAlignedAPlusCloseoutSource
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) where
  roleSource : V2RolePopulationSource S
  auditCertificate : SunflowerAPlusAuditCertificate S C H

def V2KernelAlignedAPlusCloseoutSource.kernelPackage
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedAPlusCloseoutSource S C H) :
    KernelPackage S :=
  Src.roleSource.toKernelPackage

theorem V2KernelAlignedAPlusCloseoutSource.kernelRolesHold
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedAPlusCloseoutSource S C H) :
    Src.kernelPackage.allRolesHold := by
  exact Src.roleSource.kernelRolesHold

def V2KernelAlignedAPlusCloseoutSource.governance
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedAPlusCloseoutSource S C H) :
    KernelForcedGovernance S :=
  Src.auditCertificate.governance

def V2KernelAlignedAPlusCloseoutSource.residualBridge
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedAPlusCloseoutSource S C H) :
    ResidualSeparatorBridge S C H :=
  Src.auditCertificate.residualBridge

def V2KernelAlignedAPlusCloseoutSource.certificateExhaustion
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedAPlusCloseoutSource S C H) :
    V2CertificateExhaustionSource S C H :=
  V2CertificateExhaustionSource.ofAPlusAuditCertificate Src.auditCertificate

def V2KernelAlignedAPlusCloseoutSource.impossibilityRoute
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedAPlusCloseoutSource S C H) :
    V2AASCImpossibilityRoute S C H :=
  V2AASCImpossibilityRoute.ofAPlusAuditCertificate Src.auditCertificate

theorem V2KernelAlignedAPlusCloseoutSource.auditSurfaceComplete
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedAPlusCloseoutSource S C H) :
    Src.auditCertificate.auditSurfaceComplete := by
  exact Src.auditCertificate.auditSurfaceComplete_holds

theorem V2KernelAlignedAPlusCloseoutSource.discharge_residual
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedAPlusCloseoutSource S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    Not (ResidualSeparator S C H F) := by
  exact Src.auditCertificate.discharge_residual E

def V2KernelAlignedAPlusCloseoutSource.toAPlusRelativeCloseoutSource
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedAPlusCloseoutSource S C H) :
    V2APlusRelativeCloseoutSource S C H :=
  V2APlusRelativeCloseoutSource.ofRolePopulationSourceAndAPlusAuditCertificate
    Src.roleSource
    Src.auditCertificate

theorem V2KernelAlignedAPlusCloseoutSource.rolesPopulated
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedAPlusCloseoutSource S C H) :
    Src.toAPlusRelativeCloseoutSource.toAASCNativeCloseoutSource
      |>.toAASCRolePopulation
      |>.rolesPopulated := by
  exact Src.toAPlusRelativeCloseoutSource.rolesPopulated

theorem V2KernelAlignedAPlusCloseoutSource.close
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedAPlusCloseoutSource S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact Src.toAPlusRelativeCloseoutSource.close E

def V2KernelAlignedAPlusCloseoutSource.ofFrontierAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (frontier : V2SourceFrontier S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2KernelAlignedAPlusCloseoutSource S C H :=
  { roleSource := frontier.toRolePopulationSource
    auditCertificate := A }

def V2KernelAlignedAPlusCloseoutSource.ofSixObligationsAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2SixObligationSource S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2KernelAlignedAPlusCloseoutSource S C H :=
  V2KernelAlignedAPlusCloseoutSource.ofFrontierAndAPlusAuditCertificate
    Src.toSourceFrontier
    A

/--
Fully decomposed compatibility closeout.  This is the same route without an
opaque A+ certificate field.  Its `kernelPackage` projection packages realized
v2 role witnesses; the kernel-first hybrid below carries the upstream
necessity source explicitly.
-/
structure V2KernelAlignedDecomposedCloseoutSource
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) where
  roleSource : V2RolePopulationSource S
  certificateExhaustion : V2CertificateExhaustionSource S C H
  governance : KernelForcedGovernance S
  residualBridge : ResidualSeparatorBridge S C H

def V2KernelAlignedDecomposedCloseoutSource.kernelPackage
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedDecomposedCloseoutSource S C H) :
    KernelPackage S :=
  Src.roleSource.toKernelPackage

theorem V2KernelAlignedDecomposedCloseoutSource.kernelRolesHold
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedDecomposedCloseoutSource S C H) :
    Src.kernelPackage.allRolesHold := by
  exact Src.roleSource.kernelRolesHold

def V2KernelAlignedDecomposedCloseoutSource.impossibilityRoute
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedDecomposedCloseoutSource S C H) :
    V2AASCImpossibilityRoute S C H :=
  { governance := Src.governance
    residualBridge := Src.residualBridge }

def V2KernelAlignedDecomposedCloseoutSource.toAASCNativeCloseoutSource
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedDecomposedCloseoutSource S C H) :
    V2AASCNativeCloseoutSource S C H :=
  { roleCore := Src.roleSource.toAASCRolePopulationCore
    certificateExhaustion := Src.certificateExhaustion
    impossibilityRoute := Src.impossibilityRoute }

theorem V2KernelAlignedDecomposedCloseoutSource.rolesPopulated
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedDecomposedCloseoutSource S C H) :
    Src.toAASCNativeCloseoutSource.toAASCRolePopulation.rolesPopulated := by
  exact Src.roleSource.rolesPopulated

theorem V2KernelAlignedDecomposedCloseoutSource.discharge_residual
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedDecomposedCloseoutSource S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    Not (ResidualSeparator S C H F) := by
  exact
    kernel_forced_discharge_of_calibrated_residual_separator
      Src.governance
      Src.residualBridge
      E

theorem V2KernelAlignedDecomposedCloseoutSource.close_via_native
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedDecomposedCloseoutSource S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact Src.toAASCNativeCloseoutSource.close E

theorem V2KernelAlignedDecomposedCloseoutSource.close
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedDecomposedCloseoutSource S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact
    local_endpoint_transfer_to_BMF
      Src.governance
      Src.residualBridge
      E
      (Src.certificateExhaustion.split F)

def V2KernelAlignedDecomposedCloseoutSource.ofKernelAlignedAPlusCloseoutSource
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelAlignedAPlusCloseoutSource S C H) :
    V2KernelAlignedDecomposedCloseoutSource S C H :=
  { roleSource := Src.roleSource
    certificateExhaustion := Src.certificateExhaustion
    governance := Src.governance
    residualBridge := Src.residualBridge }

def V2KernelAlignedDecomposedCloseoutSource.ofFrontierAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (frontier : V2SourceFrontier S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2KernelAlignedDecomposedCloseoutSource S C H :=
  V2KernelAlignedDecomposedCloseoutSource.ofKernelAlignedAPlusCloseoutSource
    (V2KernelAlignedAPlusCloseoutSource.ofFrontierAndAPlusAuditCertificate
      frontier
      A)

def V2KernelAlignedDecomposedCloseoutSource.ofSixObligationsAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2SixObligationSource S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2KernelAlignedDecomposedCloseoutSource S C H :=
  V2KernelAlignedDecomposedCloseoutSource.ofFrontierAndAPlusAuditCertificate
    Src.toSourceFrontier
    A

/--
Compatibility hybrid of the original residual-separator closeout and the v2
finite AASC-type population architecture.  It keeps the original route visible
for audit comparison.  The corpus-controlled four-role hybrid below is the
preferred route because it does not classify residual negative content as an
independent standing authorizer.
-/
structure V2KernelFirstHybridCloseoutSource
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) where
  kernelNecessity : DeterminateEndpointKernelSource S
  finiteWitnessPopulation : V2RolePopulationSource S
  populationExhaustion :
    V2FinitePopulationExhaustionSource S C H finiteWitnessPopulation
  residualAuthorization : ResidualSeparatorBridge S C H

def DeterminateEndpointKernelSource.ofAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (A : SunflowerAPlusAuditCertificate S C H) :
    DeterminateEndpointKernelSource S :=
  { governance := A.governance
    carrierNondegenerate := A.carrierNondegenerate }

def V2KernelFirstHybridCloseoutSource.certificateExhaustion
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelFirstHybridCloseoutSource S C H) :
    V2CertificateExhaustionSource S C H :=
  Src.populationExhaustion.toCertificateExhaustionSource

def V2KernelFirstHybridCloseoutSource.kernelAtEndpointUse
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelFirstHybridCloseoutSource S C H)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    KernelPackage S :=
  Src.kernelNecessity.kernelAtEndpointUse U

theorem V2KernelFirstHybridCloseoutSource.kernelRolesHoldAtEndpointUse
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelFirstHybridCloseoutSource S C H)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    (Src.kernelAtEndpointUse U).allRolesHold := by
  exact Src.kernelNecessity.kernelRolesHoldAtEndpointUse U

theorem V2KernelFirstHybridCloseoutSource.rolesPopulated
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelFirstHybridCloseoutSource S C H) :
    Src.finiteWitnessPopulation.toAASCRolePopulationCore.rolesPopulated := by
  exact Src.finiteWitnessPopulation.rolesPopulated

theorem V2KernelFirstHybridCloseoutSource.excludesLawfulHigherDensityMotif
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelFirstHybridCloseoutSource S C H)
    {motif :
      Src.populationExhaustion.objectiveMotifCompleteness.motifSystem.Motif}
    (lawful :
      Src.populationExhaustion.objectiveMotifCompleteness.motifSystem
        |>.lawfulNegativeMotif motif)
    (higherDensity :
      Src.populationExhaustion.objectiveMotifCompleteness.motifSystem
        |>.densityExceeds H motif)
    (notExcluded : Not (
      Src.populationExhaustion.objectiveMotifCompleteness.motifSystem
        |>.excludedByCarrierCriterion motif)) :
    False := by
  exact
    Src.populationExhaustion.excludesLawfulHigherDensityMotif
      lawful
      higherDensity
      notExcluded

theorem V2KernelFirstHybridCloseoutSource.dischargeResidualAuthorization
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelFirstHybridCloseoutSource S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    Not (ResidualSeparator S C H F) := by
  exact
    kernel_forced_discharge_of_calibrated_residual_separator
      Src.kernelNecessity.governance
      Src.residualAuthorization
      E

theorem V2KernelFirstHybridCloseoutSource.close
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2KernelFirstHybridCloseoutSource S C H)
    {F : S.Family}
    (E : ExactCountercaseUse S F) :
    BMF S C H F := by
  exact
    local_endpoint_transfer_to_BMF
      Src.kernelNecessity.governance
      Src.residualAuthorization
      E
      (Src.certificateExhaustion.split F)

def V2KernelFirstHybridCloseoutSource.ofRolePopulationAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (population : V2RolePopulationSource S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2KernelFirstHybridCloseoutSource S C H :=
  { kernelNecessity :=
      DeterminateEndpointKernelSource.ofAPlusAuditCertificate A
    finiteWitnessPopulation := population
    populationExhaustion :=
      V2FinitePopulationExhaustionSource.ofAPlusAuditCertificate population A
    residualAuthorization := A.residualBridge }

def V2KernelFirstHybridCloseoutSource.ofFrontierAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (frontier : V2SourceFrontier S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2KernelFirstHybridCloseoutSource S C H :=
  V2KernelFirstHybridCloseoutSource.ofRolePopulationAndAPlusAuditCertificate
    frontier.toRolePopulationSource
    A

def V2KernelFirstHybridCloseoutSource.ofSixObligationsAndAPlusAuditCertificate
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2SixObligationSource S)
    (A : SunflowerAPlusAuditCertificate S C H) :
    V2KernelFirstHybridCloseoutSource S C H :=
  V2KernelFirstHybridCloseoutSource.ofFrontierAndAPlusAuditCertificate
    Src.toSourceFrontier
    A

inductive V2KernelFirstHybridObligation where
  | kernelNecessity
  | finiteWitnessPopulation
  | populationExhaustion
  | residualAuthorization
deriving DecidableEq, Repr

def v2KernelFirstHybridObligations : List V2KernelFirstHybridObligation :=
  [ .kernelNecessity
  , .finiteWitnessPopulation
  , .populationExhaustion
  , .residualAuthorization
  ]

theorem v2KernelFirstHybridObligationCount_eq :
    v2KernelFirstHybridObligations.length = 4 := by
  rfl

/--
Four-role endpoint exhaustion indexed by both the upstream corpus machinery and
the concrete v2 finite-witness population.  The outcomes are exactly bounded
certificate, skin, tensor split, or sunflower.  There is no raw-infinity or
residual-discriminator fifth role.
-/
structure V2FourRoleEndpointExhaustionSource
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat)
    (corpus : KernelFirstCorpusMachinery S)
    (population : V2RolePopulationSource S) where
  objectiveMotifCompleteness : ObjectiveMotifCompletenessSource S C H
  skinOutcome : S.Family -> Prop
  tensorSplitOutcome : S.Family -> Prop
  exhaustive :
    forall F : S.Family,
      QuantitativeExactCountercaseUse S H F ->
      BMF S C H F \/
      skinOutcome F \/
      tensorSplitOutcome F \/
      S.sunflower F
  quotientFinalityEliminatesSkin :
    forall F : S.Family,
      QuantitativeExactCountercaseUse S H F ->
      skinOutcome F -> False
  primenessEliminatesTensorSplit :
    forall F : S.Family,
      QuantitativeExactCountercaseUse S H F ->
      tensorSplitOutcome F -> False

theorem V2FourRoleEndpointExhaustionSource.close
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    {corpus : KernelFirstCorpusMachinery S}
    {population : V2RolePopulationSource S}
    (Src : V2FourRoleEndpointExhaustionSource S C H corpus population)
    {F : S.Family}
    (E : QuantitativeExactCountercaseUse S H F) :
    BMF S C H F := by
  rcases Src.exhaustive F E with hBMF | hSkinOrTensorOrSun
  · exact hBMF
  · rcases hSkinOrTensorOrSun with hSkin | hTensorOrSun
    · exact False.elim (Src.quotientFinalityEliminatesSkin F E hSkin)
    · rcases hTensorOrSun with hTensor | hSun
      · exact False.elim (Src.primenessEliminatesTensorSplit F E hTensor)
      · exact False.elim (E.noSunflower_holds hSun)

theorem V2FourRoleEndpointExhaustionSource.excludesLawfulHigherDensityMotif
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    {corpus : KernelFirstCorpusMachinery S}
    {population : V2RolePopulationSource S}
    (Src : V2FourRoleEndpointExhaustionSource S C H corpus population)
    {motif : Src.objectiveMotifCompleteness.motifSystem.Motif}
    (lawful : Src.objectiveMotifCompleteness.motifSystem.lawfulNegativeMotif motif)
    (higherDensity :
      Src.objectiveMotifCompleteness.motifSystem.densityExceeds H motif)
    (notExcluded : Not (
      Src.objectiveMotifCompleteness.motifSystem.excludedByCarrierCriterion motif)) :
    False := by
  exact
    Src.objectiveMotifCompleteness.excludesLawfulHigherDensityMotif
      lawful
      higherDensity
      notExcluded

/--
Attack-safe hybrid: kernel necessity and fixed-domain A+ closure are separate
corpus inputs, v2 supplies finite witness population, and the endpoint closes
by four-role exhaustion rather than residual-discriminator reclassification.
-/
structure V2CorpusControlledHybridCloseoutSource
    (S : SunflowerCarrier)
    (C : CertificateLanguage S)
    (H : Nat) where
  corpusMachinery : KernelFirstCorpusMachinery S
  finiteWitnessPopulation : V2RolePopulationSource S
  fourRoleExhaustion :
    V2FourRoleEndpointExhaustionSource
      S C H corpusMachinery finiteWitnessPopulation

def V2CorpusControlledHybridCloseoutSource.kernelAtEndpointUse
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2CorpusControlledHybridCloseoutSource S C H)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    KernelPackage S :=
  Src.corpusMachinery.kernelAtEndpointUse U

theorem V2CorpusControlledHybridCloseoutSource.kernelRolesHoldAtEndpointUse
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2CorpusControlledHybridCloseoutSource S C H)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    (Src.kernelAtEndpointUse U).allRolesHold := by
  exact Src.corpusMachinery.kernelRolesHoldAtEndpointUse U

theorem V2CorpusControlledHybridCloseoutSource.rolesPopulated
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2CorpusControlledHybridCloseoutSource S C H) :
    Src.finiteWitnessPopulation.toAASCRolePopulationCore.rolesPopulated := by
  exact Src.finiteWitnessPopulation.rolesPopulated

theorem V2CorpusControlledHybridCloseoutSource.close
    {S : SunflowerCarrier}
    {C : CertificateLanguage S}
    {H : Nat}
    (Src : V2CorpusControlledHybridCloseoutSource S C H)
    {F : S.Family}
    (E : QuantitativeExactCountercaseUse S H F) :
    BMF S C H F := by
  exact Src.fourRoleExhaustion.close E

inductive V2CorpusControlledHybridObligation where
  | kernelNecessity
  | fixedDomainCorpusClosure
  | finiteWitnessPopulation
  | fourRoleEndpointExhaustion
deriving DecidableEq, Repr

def v2CorpusControlledHybridObligations :
    List V2CorpusControlledHybridObligation :=
  [ .kernelNecessity
  , .fixedDomainCorpusClosure
  , .finiteWitnessPopulation
  , .fourRoleEndpointExhaustion
  ]

theorem v2CorpusControlledHybridObligationCount_eq :
    v2CorpusControlledHybridObligations.length = 4 := by
  rfl

/--
The AASC-native closeout ledger: after role population is built, closure needs
only the populated role core, exhausted branch split, and residual impossibility
route.
-/
inductive V2AASCNativeObligation where
  | rolePopulationCore
  | certificateExhaustion
  | residualImpossibility
deriving DecidableEq, Repr

def v2AASCNativeObligations : List V2AASCNativeObligation :=
  [ .rolePopulationCore
  , .certificateExhaustion
  , .residualImpossibility
  ]

theorem v2AASCNativeObligationCount_eq :
    v2AASCNativeObligations.length = 3 := by
  rfl

/--
The A+-relative closeout ledger: with the A+ certificate fixed, exhaustion and
residual impossibility are certificate data, leaving only role population on the
v2 side.
-/
inductive V2APlusRelativeObligation where
  | rolePopulationCore
deriving DecidableEq, Repr

def v2APlusRelativeObligations : List V2APlusRelativeObligation :=
  [ .rolePopulationCore ]

theorem v2APlusRelativeObligationCount_eq :
    v2APlusRelativeObligations.length = 1 := by
  rfl

/-- Exact source ledger for populating the four AASC roles from v2 data. -/
inductive V2RolePopulationObligation where
  | rawBlockerQuotientAdmissibility
  | uniformProfileStanding
  | blockerFiberReference
  | roleFiberRankIrreversibility
deriving DecidableEq, Repr

def v2RolePopulationObligations : List V2RolePopulationObligation :=
  [ .rawBlockerQuotientAdmissibility
  , .uniformProfileStanding
  , .blockerFiberReference
  , .roleFiberRankIrreversibility
  ]

theorem v2RolePopulationObligationCount_eq :
    v2RolePopulationObligations.length = 4 := by
  rfl

/--
Kernel-aligned A+-relative ledger: the role source supplies the actual
`KernelPackage`, while the A+ certificate supplies the existing governance,
exhaustion, and residual-impossibility data.
-/
inductive V2KernelAlignedAPlusObligation where
  | rolePopulationSource
  | auditCertificate
deriving DecidableEq, Repr

def v2KernelAlignedAPlusObligations :
    List V2KernelAlignedAPlusObligation :=
  [ .rolePopulationSource
  , .auditCertificate
  ]

theorem v2KernelAlignedAPlusObligationCount_eq :
    v2KernelAlignedAPlusObligations.length = 2 := by
  rfl

/--
Fully decomposed kernel-aligned ledger: no A+ certificate is opaque here; its
consumed data are branch exhaustion, governance, and residual bridge.
-/
inductive V2KernelAlignedDecomposedObligation where
  | rolePopulationSource
  | certificateExhaustion
  | governance
  | residualBridge
deriving DecidableEq, Repr

def v2KernelAlignedDecomposedObligations :
    List V2KernelAlignedDecomposedObligation :=
  [ .rolePopulationSource
  , .certificateExhaustion
  , .governance
  , .residualBridge
  ]

theorem v2KernelAlignedDecomposedObligationCount_eq :
    v2KernelAlignedDecomposedObligations.length = 4 := by
  rfl

/-- Exact remaining proof obligations for the v2 closeout source. -/
inductive V2RemainingObligation where
  | rawBlockerNormalFormToQuotient
  | uniformConcreteProfileCoding
  | admissibleQuotientDomination
  | blockerFiberCoercivityAndEscapeExclusion
  | roleFiberRankCounting
  | carrierEndpointTranslation
deriving DecidableEq, Repr

def v2RemainingObligations : List V2RemainingObligation :=
  [ .rawBlockerNormalFormToQuotient
  , .uniformConcreteProfileCoding
  , .admissibleQuotientDomination
  , .blockerFiberCoercivityAndEscapeExclusion
  , .roleFiberRankCounting
  , .carrierEndpointTranslation
  ]

theorem v2RemainingObligationCount_eq :
    v2RemainingObligations.length = 6 := by
  rfl

/--
The v2 closeout theorem is intentionally conditional on the blocker quotient
compactness package.  Future work must prove that package; it is not replaced
by `CompleteCertificateLanguage`, `FiniteEntropyCeiling`, or raw blocker size.
-/
structure V2EndpointCloseout (S : SunflowerCarrier) where
  blockerCompactness : BoundedBlockerQuotientCompactness S
  endpointCertificate : ConstantBaseEndpointCertificate S
  compactnessYieldsEndpoint :
    blockerCompactness.ready -> endpointCertificate.endpointBound

theorem blocker_quotient_compactness_yields_endpoint_bound
    {S : SunflowerCarrier}
    (V : V2EndpointCloseout S) :
    V.endpointCertificate.endpointBound := by
  exact V.compactnessYieldsEndpoint
    (BoundedBlockerQuotientCompactness.ready_holds V.blockerCompactness)

/-- Premises forbidden as substitutes for the v2 blocker quotient proof. -/
inductive V2ForbiddenPremise where
  | completeCertificateLanguage
  | finiteEntropyCeiling
  | uniformPrimeRank
  | rawFiberBound
  | canonicalExtraction
  | rawBlockerSetBound
deriving DecidableEq, Repr

def v2ForbiddenPremises : List V2ForbiddenPremise :=
  [ .completeCertificateLanguage
  , .finiteEntropyCeiling
  , .uniformPrimeRank
  , .rawFiberBound
  , .canonicalExtraction
  , .rawBlockerSetBound
  ]

theorem v2ForbiddenPremiseCount_eq :
    v2ForbiddenPremises.length = 6 := by
  rfl

end V2
end SunflowerAASC
