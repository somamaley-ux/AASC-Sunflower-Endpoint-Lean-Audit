import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import SunflowerAASC.V2.BlockerQuotient
import SunflowerAASC.V2.ConcreteCarrier

namespace SunflowerAASC
namespace V2
namespace RolePopulation

/--
A quotient-final population by a finite alphabet of true AASC types.  The
alphabet may depend on `k`; its codes map into the four outcome roles, but the
role map is not assumed injective.
-/
structure TypeFinalQuotient
    (Qk : Nat)
    (roleOfType : Fin Qk -> AASCBlockerRole)
    (S : SunflowerCarrier)
    (P : FullyReducedPrimePackage S)
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C) where
  quotient : RoleDistinctBlockerQuotient S P C B
  typeCode : Fin quotient.classCount -> Fin Qk
  typeCode_injective : Function.Injective typeCode

theorem TypeFinalQuotient.classCount_le_Qk
    {Qk : Nat}
    {roleOfType : Fin Qk -> AASCBlockerRole}
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (T : TypeFinalQuotient Qk roleOfType S P C B) :
    T.quotient.classCount <= Qk := by
  simpa using Fintype.card_le_of_injective T.typeCode T.typeCode_injective

/-- The quotient-final representatives carrying one true AASC type code. -/
def TypeFinalQuotient.typeFiber
    {Qk : Nat}
    {roleOfType : Fin Qk -> AASCBlockerRole}
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (T : TypeFinalQuotient Qk roleOfType S P C B)
    (code : Fin Qk) : Finset (Fin T.quotient.classCount) :=
  Finset.univ.filter (fun i => T.typeCode i = code)

theorem TypeFinalQuotient.typeFiber_card_le_one
    {Qk : Nat}
    {roleOfType : Fin Qk -> AASCBlockerRole}
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (T : TypeFinalQuotient Qk roleOfType S P C B)
    (code : Fin Qk) :
    (T.typeFiber code).card <= 1 := by
  apply Finset.card_le_one.mpr
  intro left hleft right hright
  apply T.typeCode_injective
  have left_code : T.typeCode left = code := (Finset.mem_filter.mp hleft).2
  have right_code : T.typeCode right = code := (Finset.mem_filter.mp hright).2
  exact left_code.trans right_code.symm

/-- The true type code determines one of the four AASC outcome roles. -/
def TypeFinalQuotient.roleOfRepresentative
    {Qk : Nat}
    {roleOfType : Fin Qk -> AASCBlockerRole}
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (T : TypeFinalQuotient Qk roleOfType S P C B)
    (representative : Fin T.quotient.classCount) : AASCBlockerRole :=
  roleOfType (T.typeCode representative)

/-- The actual type assignment is the rank-independent finite profile code. -/
def TypeFinalQuotient.profileCoding
    {Qk : Nat}
    {roleOfType : Fin Qk -> AASCBlockerRole}
    {S : SunflowerCarrier}
    {P : FullyReducedPrimePackage S}
    {C : CoreLink S P}
    {B : RawBlockerCertificate S P C}
    (Qk_positive : 0 < Qk)
    (T : TypeFinalQuotient Qk roleOfType S P C B) :
    ConcreteFiniteProfileCoding S P C B T.quotient where
  profileAlphabetSize := Qk
  profileAlphabetSize_positive := Qk_positive
  code := T.typeCode
  code_injective := T.typeCode_injective
  allClassesCoded := forall i : Fin T.quotient.classCount,
    Exists (fun code : Fin Qk => T.typeCode i = code)
  allClassesCoded_holds := by
    intro i
    exact ⟨T.typeCode i, rfl⟩
  countBound_from_injection := T.classCount_le_Qk

/--
The finite AASC-type population theorem in its constructive uniform form.
`Qk` is fixed before any rank-indexed family is processed.
-/
structure UniformTypeFinalQuotientSource (S : SunflowerCarrier) where
  Qk : Nat
  Qk_positive : 0 < Qk
  roleOfType : Fin Qk -> AASCBlockerRole
  populate :
    forall {P : FullyReducedPrimePackage S}
      (C : CoreLink S P)
      (B : RawBlockerCertificate S P C),
      TypeFinalQuotient Qk roleOfType S P C B

def UniformTypeFinalQuotientSource.toRawQuotientSource
    {S : SunflowerCarrier}
    (Src : UniformTypeFinalQuotientSource S) :
    RawBlockerQuotientConstructionSource S where
  quotient := fun C B => (Src.populate C B).quotient

def UniformTypeFinalQuotientSource.toProfileCodingSource
    {S : SunflowerCarrier}
    (Src : UniformTypeFinalQuotientSource S) :
    UniformConcreteProfileCodingSource S
      Src.toRawQuotientSource.quotient where
  Qk := Src.Qk
  Qk_positive := Src.Qk_positive
  concreteProfileCoding := fun C B =>
    (Src.populate C B).profileCoding Src.Qk_positive
  profileAlphabetBound := by
    intro P C B
    exact Nat.le_refl Src.Qk

theorem UniformTypeFinalQuotientSource.uniformClassBound
    {S : SunflowerCarrier}
    (Src : UniformTypeFinalQuotientSource S)
    {P : FullyReducedPrimePackage S}
    (C : CoreLink S P)
    (B : RawBlockerCertificate S P C) :
    (Src.populate C B).quotient.classCount <= Src.Qk := by
  exact (Src.populate C B).classCount_le_Qk

/--
An actual rank trace: every family member receives one true AASC type code at
each deletion coordinate.  The four-role outcome is read from each code, but
the numerical bound counts type codes rather than role labels.
-/
structure AASCTypeTraceCoding
    {alpha : Type}
    [DecidableEq alpha]
    {n Qk : Nat}
    (F : Concrete.UniformSetFamily alpha n) where
  trace : {edge // edge ∈ F.edges} -> (Fin n -> Fin Qk)
  trace_injective : Function.Injective trace

theorem AASCTypeTraceCoding.family_card_le_type_pow_rank
    {alpha : Type}
    [DecidableEq alpha]
    {n Qk : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    (Coding : AASCTypeTraceCoding (Qk := Qk) F) :
    F.edges.card <= Qk ^ n := by
  have hcard :=
    Fintype.card_le_of_injective Coding.trace Coding.trace_injective
  simpa using hcard

/-- The exact recursive population object still required for endpoint closure. -/
structure KernelFaithfulTypeTraceSource
    (alpha : Type)
    [DecidableEq alpha]
    (n k Qk : Nat) where
  Qk_positive : 0 < Qk
  roleOfType : Fin Qk -> AASCBlockerRole
  traceCoding :
    forall F : Concrete.UniformSetFamily alpha n,
      Not (Concrete.HasSunflower k F) ->
      AASCTypeTraceCoding (Qk := Qk) F

theorem sunflower_of_card_gt_type_pow_rank
    {alpha : Type}
    [DecidableEq alpha]
    {n k Qk : Nat}
    (Src : KernelFaithfulTypeTraceSource alpha n k Qk)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess : Qk ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  by_contra noSunflower
  exact Nat.not_lt_of_ge
    (Src.traceCoding F noSunflower).family_card_le_type_pow_rank
    sizeExcess

theorem KernelFaithfulTypeTraceSource.excludesQuantitativeCountercase
    {alpha : Type}
    [DecidableEq alpha]
    {n k Qk : Nat}
    (Src : KernelFaithfulTypeTraceSource alpha n k Qk)
    {F : Concrete.UniformSetFamily alpha n}
    (E : QuantitativeExactCountercaseUse
      (Concrete.concreteSunflowerCarrier alpha n k) Qk F) :
    False := by
  exact Nat.not_lt_of_ge
    (Src.traceCoding F E.noSunflower_holds).family_card_le_type_pow_rank
    E.sizeExcess_holds

/-- The rank-one product-transversal lower-bound family with `k - 1` choices. -/
def rankOneTransversalFamily (k : Nat) :
    Concrete.UniformSetFamily (Fin (k - 1)) 1 where
  edges := (Finset.univ : Finset (Fin (k - 1))).image
    (fun i => ({i} : Finset (Fin (k - 1))))
  uniform := by
    intro edge hedge
    rcases Finset.mem_image.mp hedge with ⟨i, _, rfl⟩
    simp

theorem rankOneTransversalFamily_card (k : Nat) :
    (rankOneTransversalFamily k).edges.card = k - 1 := by
  change ((Finset.univ : Finset (Fin (k - 1))).image
    (fun i => ({i} : Finset (Fin (k - 1))))).card = k - 1
  rw [Finset.card_image_of_injective]
  · simp
  · intro left right h
    exact Finset.singleton_inj.mp h

theorem rankOneTransversalFamily_noSunflower
    {k : Nat}
    (k_positive : 0 < k) :
    Not (Concrete.HasSunflower k (rankOneTransversalFamily k)) := by
  intro hasSunflower
  rcases hasSunflower with ⟨core, ⟨witness⟩⟩
  let selected : Fin k ->
      {edge // edge ∈ (rankOneTransversalFamily k).edges} :=
    fun i => ⟨witness.petals i, witness.petals_mem i⟩
  have selected_injective : Function.Injective selected := by
    intro i j hij
    apply witness.petals_injective
    exact congrArg Subtype.val hij
  have hcard := Fintype.card_le_of_injective selected selected_injective
  have hle : k <= k - 1 := by
    simpa [rankOneTransversalFamily_card] using hcard
  exact (Nat.not_le_of_lt (Nat.sub_lt k_positive (by decide))) hle

/-- Any uniform type alphabet compatible with the rank-one lower bound has at least `k - 1` codes. -/
theorem typeAlphabet_ge_k_sub_one
    {k Qk : Nat}
    (k_positive : 0 < k)
    (Src : KernelFaithfulTypeTraceSource (Fin (k - 1)) 1 k Qk) :
    k - 1 <= Qk := by
  have coding := Src.traceCoding
    (rankOneTransversalFamily k)
    (rankOneTransversalFamily_noSunflower k_positive)
  have hbound := coding.family_card_le_type_pow_rank
  simpa [rankOneTransversalFamily_card] using hbound

end RolePopulation
end V2
end SunflowerAASC
