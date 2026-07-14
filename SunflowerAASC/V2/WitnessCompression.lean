import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Image
import SunflowerAASC.V2.ConcreteGeometry
import SunflowerAASC.V2.RolePopulation

namespace SunflowerAASC
namespace V2
namespace WitnessCompression

instance : Fintype AASCBlockerRole where
  elems := { .skin, .boundedFiber, .tensorSplit, .sunRole }
  complete := by
    intro role
    cases role <;> simp

theorem aascBlockerRole_card : Fintype.card AASCBlockerRole = 4 := by
  decide

/-- A true type is coded by matching-petal support and one of four AASC roles. -/
abbrev WitnessSignature (k : Nat) := Finset (Fin k) × AASCBlockerRole

def witnessAlphabetSize (k : Nat) : Nat := 4 * 2 ^ k

theorem witnessSignature_card (k : Nat) :
    Fintype.card (WitnessSignature k) = witnessAlphabetSize k := by
  simp [WitnessSignature, witnessAlphabetSize, Fintype.card_finset,
    aascBlockerRole_card, Nat.mul_comm]

theorem witnessAlphabetSize_positive (k : Nat) :
    0 < witnessAlphabetSize k := by
  exact Nat.mul_pos (by decide) (Nat.two_pow_pos k)

noncomputable def witnessSignatureEquivFin (k : Nat) :
    WitnessSignature k ≃ Fin (witnessAlphabetSize k) :=
  Fintype.equivFinOfCardEq (witnessSignature_card k)

noncomputable def roleOfWitnessCode
    (k : Nat)
    (code : Fin (witnessAlphabetSize k)) : AASCBlockerRole :=
  (witnessSignatureEquivFin k).symm code |>.2

/-- Inject the petals of a matching with at most `k` members into `Fin k`. -/
noncomputable def matchingPetalEmbedding
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : Concrete.FiniteCoreLinkMatching F core)
    (hcard : M.petals.card <= k) :
    {edge // edge ∈ M.petals} ↪ Fin k :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe M.petals)).toEmbedding.trans
    ⟨Fin.castLE hcard, Fin.castLE_injective hcard⟩

/-- An endpoint-local type witness supported on petals of one finite matching. -/
structure MatchingSupportedSignature
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : Concrete.FiniteCoreLinkMatching F core) where
  support : Finset {edge // edge ∈ M.petals}
  role : AASCBlockerRole

noncomputable def MatchingSupportedSignature.toWitnessSignature
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    {core : Finset alpha}
    {M : Concrete.FiniteCoreLinkMatching F core}
    (hcard : M.petals.card <= k)
    (W : MatchingSupportedSignature M) : WitnessSignature k :=
  (W.support.map (matchingPetalEmbedding M hcard), W.role)

theorem MatchingSupportedSignature.toWitnessSignature_injective
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    {core : Finset alpha}
    {M : Concrete.FiniteCoreLinkMatching F core}
    (hcard : M.petals.card <= k) :
    Function.Injective
      (MatchingSupportedSignature.toWitnessSignature (M := M) hcard) := by
  intro left right h
  cases left with
  | mk leftSupport leftRole =>
      cases right with
      | mk rightSupport rightRole =>
          have hsupport :
              leftSupport.map (matchingPetalEmbedding M hcard) =
                rightSupport.map (matchingPetalEmbedding M hcard) :=
            congrArg Prod.fst h
          have hrole : leftRole = rightRole := congrArg Prod.snd h
          have : leftSupport = rightSupport :=
            Finset.map_injective (matchingPetalEmbedding M hcard) hsupport
          cases this
          cases hrole
          rfl

theorem MatchingSupportedSignature.support_card_lt_k
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    {core : Finset alpha}
    {M : Concrete.FiniteCoreLinkMatching F core}
    (matchingSize_lt : M.petals.card < k)
    (W : MatchingSupportedSignature M) :
    W.support.card < k := by
  exact Nat.lt_of_le_of_lt
    (by
      have h := Finset.card_le_univ W.support
      simpa using h)
    matchingSize_lt

/--
The endpoint-local compression premise in non-vacuous relational form.  Equal
finite signatures imply skin, and quotient finality identifies skin-equivalent
survivors.
-/
structure WitnessCompressedQuotientPackage
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C) where
  quotient : RoleDistinctBlockerQuotient S P C B
  skinEquivalent :
    Fin quotient.classCount -> Fin quotient.classCount -> Prop
  signature : Fin quotient.classCount -> WitnessSignature S.k
  equalSignatureImpliesSkin :
    forall left right, signature left = signature right ->
      skinEquivalent left right
  quotientFinality :
    forall left right, skinEquivalent left right -> left = right

noncomputable def WitnessCompressedQuotientPackage.toTypeFinalQuotient
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (Package : WitnessCompressedQuotientPackage S P C B) :
    RolePopulation.TypeFinalQuotient
      (witnessAlphabetSize S.k)
      (roleOfWitnessCode S.k)
      S P C B where
  quotient := Package.quotient
  typeCode := fun representative =>
    witnessSignatureEquivFin S.k (Package.signature representative)
  typeCode_injective := by
    intro left right hcode
    apply Package.quotientFinality left right
    apply Package.equalSignatureImpliesSkin left right
    exact (witnessSignatureEquivFin S.k).injective hcode

theorem WitnessCompressedQuotientPackage.classCount_le_witnessAlphabet
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (Package : WitnessCompressedQuotientPackage S P C B) :
    Package.quotient.classCount <= witnessAlphabetSize S.k := by
  exact Package.toTypeFinalQuotient.classCount_le_Qk

/-- Uniform endpoint-local witness compression over every prime/core/blocker. -/
structure UniformEndpointLocalWitnessCompressionSource
    (S : SunflowerCarrier) where
  compress :
    forall {P : FullyReducedPrimePackage S}
      (C : CoreLink S P)
      (B : RawBlockerCertificate S P C),
      WitnessCompressedQuotientPackage S P C B

noncomputable def UniformEndpointLocalWitnessCompressionSource.toTypePopulation
    {S : SunflowerCarrier}
    (Src : UniformEndpointLocalWitnessCompressionSource S) :
    RolePopulation.UniformTypeFinalQuotientSource S where
  Qk := witnessAlphabetSize S.k
  Qk_positive := witnessAlphabetSize_positive S.k
  roleOfType := roleOfWitnessCode S.k
  populate := fun C B => (Src.compress C B).toTypeFinalQuotient

def concreteCore
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {P : FullyReducedPrimePackage
      (Concrete.concreteSunflowerCarrier alpha n k)}
    (C : CoreLink (Concrete.concreteSunflowerCarrier alpha n k) P) :
    Finset alpha :=
  C.core

noncomputable def canonicalCoreMatching
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {P : FullyReducedPrimePackage
      (Concrete.concreteSunflowerCarrier alpha n k)}
    (C : CoreLink (Concrete.concreteSunflowerCarrier alpha n k) P) :
    Concrete.MaximalFiniteCoreLinkMatching P.family (concreteCore C) :=
  Concrete.maximalFiniteCoreLinkMatching P.family (concreteCore C)

theorem canonicalCoreMatching_size_lt
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {P : FullyReducedPrimePackage
      (Concrete.concreteSunflowerCarrier alpha n k)}
    (C : CoreLink (Concrete.concreteSunflowerCarrier alpha n k) P) :
    (canonicalCoreMatching C).matching.petals.card < k := by
  exact Concrete.finiteCoreLinkMatching_card_lt_of_noSunflower
    P.noSunflower_holds
    (canonicalCoreMatching C).matching

/--
The exact local AASC population datum over the canonical maximal matching.
All finite support and cardinality work is already discharged around it.
-/
structure ConcreteMatchingWitnessPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (P : FullyReducedPrimePackage
      (Concrete.concreteSunflowerCarrier alpha n k))
    (C : CoreLink (Concrete.concreteSunflowerCarrier alpha n k) P)
    (B : RawBlockerCertificate
      (Concrete.concreteSunflowerCarrier alpha n k) P C) where
  quotient : RoleDistinctBlockerQuotient
    (Concrete.concreteSunflowerCarrier alpha n k) P C B
  skinEquivalent :
    Fin quotient.classCount -> Fin quotient.classCount -> Prop
  witness :
    Fin quotient.classCount ->
      MatchingSupportedSignature (canonicalCoreMatching C).matching
  equalWitnessImpliesSkin :
    forall left right, witness left = witness right ->
      skinEquivalent left right
  quotientFinality :
    forall left right, skinEquivalent left right -> left = right

noncomputable def ConcreteMatchingWitnessPopulation.toCompressedPackage
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {P : FullyReducedPrimePackage
      (Concrete.concreteSunflowerCarrier alpha n k)}
    {C : CoreLink (Concrete.concreteSunflowerCarrier alpha n k) P}
    {B : RawBlockerCertificate
      (Concrete.concreteSunflowerCarrier alpha n k) P C}
    (Population : ConcreteMatchingWitnessPopulation P C B) :
    WitnessCompressedQuotientPackage
      (Concrete.concreteSunflowerCarrier alpha n k) P C B := by
  have hcard :
      (canonicalCoreMatching C).matching.petals.card <= k :=
    Nat.le_of_lt (canonicalCoreMatching_size_lt C)
  exact
    { quotient := Population.quotient
      skinEquivalent := Population.skinEquivalent
      signature := fun representative =>
        (Population.witness representative).toWitnessSignature hcard
      equalSignatureImpliesSkin := by
        intro left right hsignature
        apply Population.equalWitnessImpliesSkin left right
        exact MatchingSupportedSignature.toWitnessSignature_injective
          hcard
          hsignature
      quotientFinality := Population.quotientFinality }

/-- Uniform local witness population for every concrete prime/core/blocker. -/
structure UniformConcreteMatchingWitnessPopulationSource
    (alpha : Type)
    [DecidableEq alpha]
    (n k : Nat) where
  populate :
    forall {P : FullyReducedPrimePackage
      (Concrete.concreteSunflowerCarrier alpha n k)}
      (C : CoreLink (Concrete.concreteSunflowerCarrier alpha n k) P)
      (B : RawBlockerCertificate
        (Concrete.concreteSunflowerCarrier alpha n k) P C),
      ConcreteMatchingWitnessPopulation P C B

noncomputable def UniformConcreteMatchingWitnessPopulationSource.toCompressionSource
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (Src : UniformConcreteMatchingWitnessPopulationSource alpha n k) :
    UniformEndpointLocalWitnessCompressionSource
      (Concrete.concreteSunflowerCarrier alpha n k) where
  compress := fun C B => (Src.populate C B).toCompressedPackage

noncomputable def UniformConcreteMatchingWitnessPopulationSource.toTypePopulation
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (Src : UniformConcreteMatchingWitnessPopulationSource alpha n k) :
    RolePopulation.UniformTypeFinalQuotientSource
      (Concrete.concreteSunflowerCarrier alpha n k) :=
  Src.toCompressionSource.toTypePopulation

/--
Corpus-controlled collision rule.  A same-signature distinction that is still
non-skin would have to produce a fixed-domain independent authorizer.  The
corpus closure excludes that fifth route.
-/
structure CorpusControlledWitnessAssignment
    {S : SunflowerCarrier}
    (corpus : KernelFirstCorpusMachinery S)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C) where
  quotient : RoleDistinctBlockerQuotient S P C B
  skinEquivalent :
    Fin quotient.classCount -> Fin quotient.classCount -> Prop
  signature : Fin quotient.classCount -> WitnessSignature S.k
  nonSkinSameSignatureCreatesIndependentAuthorizer :
    forall left right,
      signature left = signature right ->
      Not (skinEquivalent left right) ->
      Exists (fun factor : S.StandingFactor =>
        corpus.fixedDomainClosure.disposition factor =
          SameScopeFactorDisposition.independentAuthorizer)
  quotientFinality :
    forall left right, skinEquivalent left right -> left = right

theorem CorpusControlledWitnessAssignment.equalSignatureImpliesSkin
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (Assignment : CorpusControlledWitnessAssignment corpus P C B)
    (left right : Fin Assignment.quotient.classCount)
    (sameSignature : Assignment.signature left = Assignment.signature right) :
    Assignment.skinEquivalent left right := by
  apply Classical.byContradiction
  intro nonSkin
  rcases Assignment.nonSkinSameSignatureCreatesIndependentAuthorizer
      left right sameSignature nonSkin with ⟨factor, independent⟩
  exact corpus.fixedDomainClosure.excludesIndependentAuthorizer
    factor
    independent

noncomputable def CorpusControlledWitnessAssignment.toCompressedPackage
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (Assignment : CorpusControlledWitnessAssignment corpus P C B) :
    WitnessCompressedQuotientPackage S P C B where
  quotient := Assignment.quotient
  skinEquivalent := Assignment.skinEquivalent
  signature := Assignment.signature
  equalSignatureImpliesSkin := Assignment.equalSignatureImpliesSkin
  quotientFinality := Assignment.quotientFinality

/-- Uniform corpus-controlled witness assignment over every local package. -/
structure UniformCorpusControlledWitnessAssignmentSource
    {S : SunflowerCarrier}
    (corpus : KernelFirstCorpusMachinery S) where
  assign :
    forall {P : FullyReducedPrimePackage S}
      (C : CoreLink S P)
      (B : RawBlockerCertificate S P C),
      CorpusControlledWitnessAssignment corpus P C B

noncomputable def UniformCorpusControlledWitnessAssignmentSource.toCompressionSource
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    (Src : UniformCorpusControlledWitnessAssignmentSource corpus) :
    UniformEndpointLocalWitnessCompressionSource S where
  compress := fun C B => (Src.assign C B).toCompressedPackage

noncomputable def UniformCorpusControlledWitnessAssignmentSource.toTypePopulation
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    (Src : UniformCorpusControlledWitnessAssignmentSource corpus) :
    RolePopulation.UniformTypeFinalQuotientSource S :=
  Src.toCompressionSource.toTypePopulation

end WitnessCompression
end V2
end SunflowerAASC
