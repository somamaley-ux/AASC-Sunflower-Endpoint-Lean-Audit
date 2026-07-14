import SunflowerAASC.V2.GovernedStructuralForms
import SunflowerAASC.V2.PrivateWitnessReduction
import SunflowerAASC.V2.TraceAssembly

namespace SunflowerAASC
namespace V2
namespace GovernedDeletion

open GovernedStructuralForms

/--
Structural rank deletion before any numerical coding is chosen. A same-parent,
same-form collision is either skin or creates an endpoint-forbidden novelty.
-/
structure GovernedRankDeletionSystem
    {S : SunflowerCarrier}
    (corpus : KernelFirstCorpusMachinery S)
    (Form : Type)
    [Fintype Form]
    [Nonempty Form] where
  State : Nat -> Type
  baseSubsingleton : forall left right : State 0, left = right
  form : forall r : Nat, State (r + 1) -> Form
  predecessor : forall r : Nat, State (r + 1) -> State r
  skinEquivalent :
    forall r : Nat, State (r + 1) -> State (r + 1) -> Prop
  tensorSplit :
    forall r : Nat, State (r + 1) -> State (r + 1) -> Prop
  sunflowerRealization :
    forall r : Nat, State (r + 1) -> State (r + 1) -> Prop
  nonSkinCollisionExhaustive :
    forall r : Nat, forall left right : State (r + 1),
      predecessor r left = predecessor r right ->
      form r left = form r right ->
      Not (skinEquivalent r left right) ->
      tensorSplit r left right \/
      sunflowerRealization r left right \/
      Exists (fun factor : S.StandingFactor =>
        corpus.fixedDomainClosure.disposition factor =
          SameScopeFactorDisposition.independentAuthorizer)
  skinFinality :
    forall r : Nat, forall left right : State (r + 1),
      skinEquivalent r left right -> left = right
  tensorSplitExcluded :
    forall r : Nat, forall left right : State (r + 1),
      tensorSplit r left right -> False
  sunflowerExcluded :
    forall r : Nat, forall left right : State (r + 1),
      sunflowerRealization r left right -> False

/-- The local AASC exhaustion theorem, stated before quotient finality is used. -/
theorem GovernedRankDeletionSystem.skin_or_forbidden
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    (System : GovernedRankDeletionSystem corpus Form)
    (r : Nat)
    (left right : System.State (r + 1))
    (samePredecessor :
      System.predecessor r left = System.predecessor r right)
    (sameForm : System.form r left = System.form r right) :
    System.skinEquivalent r left right \/
    System.tensorSplit r left right \/
    System.sunflowerRealization r left right \/
    Exists (fun factor : S.StandingFactor =>
      corpus.fixedDomainClosure.disposition factor =
        SameScopeFactorDisposition.independentAuthorizer) := by
  by_cases skin : System.skinEquivalent r left right
  · exact Or.inl skin
  · exact Or.inr <|
      System.nonSkinCollisionExhaustive
        r left right samePredecessor sameForm skin

/-- Same deletion parent and same governed form force equality. -/
theorem GovernedRankDeletionSystem.collision
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    (System : GovernedRankDeletionSystem corpus Form)
    (r : Nat)
    (left right : System.State (r + 1))
    (samePredecessor :
      System.predecessor r left = System.predecessor r right)
    (sameForm : System.form r left = System.form r right) :
    left = right := by
  rcases System.skin_or_forbidden r left right samePredecessor sameForm with
    skin | tensorOrSunOrIndependent
  · exact System.skinFinality r left right skin
  · rcases tensorOrSunOrIndependent with tensor | sunOrIndependent
    · exact False.elim (System.tensorSplitExcluded r left right tensor)
    · rcases sunOrIndependent with sunflower | independent
      · exact False.elim (System.sunflowerExcluded r left right sunflower)
      · rcases independent with ⟨factor, forbidden⟩
        exact False.elim <|
          corpus.fixedDomainClosure.excludesIndependentAuthorizer
            factor forbidden

/-- Numerical head codes are introduced only after structural injectivity. -/
noncomputable def GovernedRankDeletionSystem.toRankDeletionSystem
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    (System : GovernedRankDeletionSystem corpus Form) :
    TraceAssembly.RankDeletionSystem (governedFormCard Form) where
  State := System.State
  baseSubsingleton := System.baseSubsingleton
  headCode := fun r state => governedFormEquivFin Form (System.form r state)
  predecessor := System.predecessor
  step_injective := by
    intro r left right sameCode
    apply System.collision r left right
    · exact congrArg Prod.snd sameCode
    · apply (governedFormEquivFin Form).injective
      exact congrArg Prod.fst sameCode

/-- A governed rank-deletion system whose top states contain one family. -/
structure FamilyGovernedRankDeletionSystem
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    {S : SunflowerCarrier}
    (corpus : KernelFirstCorpusMachinery S)
    (Form : Type)
    [Fintype Form]
    [Nonempty Form]
    (F : Concrete.UniformSetFamily alpha n) where
  system : GovernedRankDeletionSystem corpus Form
  topState : {edge // edge ∈ F.edges} -> system.State n
  topState_injective : Function.Injective topState

noncomputable def FamilyGovernedRankDeletionSystem.toFamilyRankDeletionSystem
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    {F : Concrete.UniformSetFamily alpha n}
    (System : FamilyGovernedRankDeletionSystem corpus Form F) :
    TraceAssembly.FamilyRankDeletionSystem
      (Qk := governedFormCard Form) F where
  system := System.system.toRankDeletionSystem
  topState := System.topState
  topState_injective := System.topState_injective

/-- Uniform governed deletion is the structural source consumed by the trace. -/
structure KernelFaithfulGovernedRankDeletionSource
    (alpha : Type)
    [DecidableEq alpha]
    (n k : Nat)
    (Form : Type)
    [Fintype Form]
    [Nonempty Form]
    (corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha n k)) where
  semantics : GovernedFormSemantics Form
  deletionSystem :
    forall F : Concrete.UniformSetFamily alpha n,
      Not (Concrete.HasSunflower k F) ->
      FamilyGovernedRankDeletionSystem corpus Form F

noncomputable def KernelFaithfulGovernedRankDeletionSource.toRankDeletionSource
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha n k)}
    (Src : KernelFaithfulGovernedRankDeletionSource
      alpha n k Form corpus) :
    TraceAssembly.KernelFaithfulRankDeletionSource
      alpha n k (governedFormCard Form) where
  Qk_positive := governedFormCard_positive Form
  roleOfType := fun code =>
    Src.semantics.role ((governedFormEquivFin Form).symm code)
  deletionSystem := fun F noSunflower =>
    (Src.deletionSystem F noSunflower).toFamilyRankDeletionSystem

/-- The endpoint estimate is a corollary of governed deletion, not its input. -/
theorem sunflower_of_governedRankDeletion
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha n k)}
    (Src : KernelFaithfulGovernedRankDeletionSource
      alpha n k Form corpus)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess : governedFormCard Form ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  exact TraceAssembly.sunflower_of_rankDeletionSystem
    Src.toRankDeletionSource F sizeExcess

/--
Bivalent standing inheritance for true AASC forms. Admissible deletion cannot
create a second standing-bearing form over one inherited lower-rank form.
-/
structure AdmissibleBivalentFormInheritance
    {S : SunflowerCarrier}
    (corpus : KernelFirstCorpusMachinery S) where
  Form : Nat -> Type
  formFintype : forall r, Fintype (Form r)
  semantics : forall r, GovernedFormSemantics (Form r)
  inheritedForm : forall r, Form (r + 1) -> Form r
  skinEquivalent :
    forall r, Form (r + 1) -> Form (r + 1) -> Prop
  tensorSplit :
    forall r, Form (r + 1) -> Form (r + 1) -> Prop
  sunflowerRealization :
    forall r, Form (r + 1) -> Form (r + 1) -> Prop
  sameInheritedFormExhaustive :
    forall r, forall left right : Form (r + 1),
      inheritedForm r left = inheritedForm r right ->
      skinEquivalent r left right \/
      tensorSplit r left right \/
      sunflowerRealization r left right \/
      Exists (fun factor : S.StandingFactor =>
        corpus.fixedDomainClosure.disposition factor =
          SameScopeFactorDisposition.independentAuthorizer)
  skinFinality :
    forall r, forall left right : Form (r + 1),
      skinEquivalent r left right -> left = right
  tensorSplitExcluded :
    forall r, forall left right : Form (r + 1),
      tensorSplit r left right -> False
  sunflowerExcluded :
    forall r, forall left right : Form (r + 1),
      sunflowerRealization r left right -> False

def AdmissibleBivalentFormInheritance.StandingBearing
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    (System : AdmissibleBivalentFormInheritance corpus)
    (r : Nat)
    (form : System.Form r) : Prop :=
  (System.semantics r).StandingBearing form

/-- Standing is decided bivalently at every rank; it is not a graded datum. -/
theorem AdmissibleBivalentFormInheritance.standingBearing_or_not
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    (System : AdmissibleBivalentFormInheritance corpus)
    (r : Nat)
    (form : System.Form r) :
    System.StandingBearing r form \/
      Not (System.StandingBearing r form) := by
  exact Classical.em _

/-- A same inherited form has no surviving non-skin successor distinction. -/
theorem AdmissibleBivalentFormInheritance.inheritedForm_injective
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    (System : AdmissibleBivalentFormInheritance corpus)
    (r : Nat) :
    Function.Injective (System.inheritedForm r) := by
  intro left right sameInheritedForm
  rcases System.sameInheritedFormExhaustive
      r left right sameInheritedForm with skin | forbidden
  · exact System.skinFinality r left right skin
  · rcases forbidden with tensor | sunOrIndependent
    · exact False.elim (System.tensorSplitExcluded r left right tensor)
    · rcases sunOrIndependent with sunflower | independent
      · exact False.elim (System.sunflowerExcluded r left right sunflower)
      · rcases independent with ⟨factor, forbidden⟩
        exact False.elim <|
          corpus.fixedDomainClosure.excludesIndependentAuthorizer
            factor forbidden

noncomputable def AdmissibleBivalentFormInheritance.transition
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    (System : AdmissibleBivalentFormInheritance corpus)
    (r : Nat) :
    System.Form (r + 1) ↪ System.Form r where
  toFun := System.inheritedForm r
  inj' := System.inheritedForm_injective r

def AdmissibleBivalentFormInheritance.formCard
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    (System : AdmissibleBivalentFormInheritance corpus)
    (r : Nat) : Nat :=
  @Fintype.card (System.Form r) (System.formFintype r)

/-- Bivalent admissible inheritance introduces no new higher-rank types. -/
theorem AdmissibleBivalentFormInheritance.formCard_succ_le
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    (System : AdmissibleBivalentFormInheritance corpus)
    (r : Nat) :
    System.formCard (r + 1) <= System.formCard r := by
  letI := System.formFintype (r + 1)
  letI := System.formFintype r
  exact Fintype.card_le_of_injective
    (System.inheritedForm r) (System.inheritedForm_injective r)

/-- Every higher-rank true-type population inherits the base cardinal bound. -/
theorem AdmissibleBivalentFormInheritance.formCard_le_base
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    (System : AdmissibleBivalentFormInheritance corpus)
    (r : Nat) :
    System.formCard r <= System.formCard 0 := by
  induction r with
  | zero => exact Nat.le_refl _
  | succ r =>
      exact (System.formCard_succ_le r).trans (by assumption)

/-- A combinatorial seed bound is inherited unchanged at every higher rank. -/
theorem AdmissibleBivalentFormInheritance.formCard_le_of_baseBound
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    (System : AdmissibleBivalentFormInheritance corpus)
    {B : Nat}
    (baseBound : System.formCard 0 <= B)
    (r : Nat) :
    System.formCard r <= B := by
  exact (System.formCard_le_base r).trans baseBound

/-- Compatibility with the four-role structural ledger; the direct bound above is stronger. -/
noncomputable def AdmissibleBivalentFormInheritance.toRankIndexedGovernedForms
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    (System : AdmissibleBivalentFormInheritance corpus) :
    RankIndexedGovernedForms where
  Form := System.Form
  formFintype := System.formFintype
  transition := fun r =>
    { toFun := fun form => (System.inheritedForm r form, .boundedFiber)
      inj' := by
        intro left right same
        exact System.inheritedForm_injective r (congrArg Prod.fst same) }

/--
Fixed-object standing inheritance with primitive contact exposed. Skin has no
authority to create standing. A standing distinction absent from the inherited
form requires fresh primitive contact, and fresh contact changes the determinate
object rather than refining the same one.
-/
structure FixedObjectPrimitiveContactInheritance where
  Form : Nat -> Type
  formFintype : forall r, Fintype (Form r)
  semantics : forall r, GovernedFormSemantics (Form r)
  inheritedForm : forall r, Form (r + 1) -> Form r
  skinEquivalent :
    forall r, Form (r + 1) -> Form (r + 1) -> Prop
  standingDistinction :
    forall r, Form (r + 1) -> Form (r + 1) -> Prop
  sameDeterminateObject :
    forall r, Form (r + 1) -> Form (r + 1) -> Prop
  primitiveContact :
    forall r, Form (r + 1) -> Form (r + 1) -> Prop
  skinHasNoStandingAuthority :
    forall r, forall left right : Form (r + 1),
      skinEquivalent r left right ->
      Not (standingDistinction r left right)
  nonSkinIsStandingBearing :
    forall r, forall left right : Form (r + 1),
      Not (skinEquivalent r left right) ->
      standingDistinction r left right
  sameInheritedFormPreservesObject :
    forall r, forall left right : Form (r + 1),
      inheritedForm r left = inheritedForm r right ->
      sameDeterminateObject r left right
  nonInheritedStandingRequiresPrimitiveContact :
    forall r, forall left right : Form (r + 1),
      inheritedForm r left = inheritedForm r right ->
      standingDistinction r left right ->
      primitiveContact r left right
  primitiveContactChangesDeterminateObject :
    forall r, forall left right : Form (r + 1),
      primitiveContact r left right ->
      Not (sameDeterminateObject r left right)
  skinFinality :
    forall r, forall left right : Form (r + 1),
      skinEquivalent r left right -> left = right

/-- Standing distinction is bivalent because it is a proposition. -/
theorem FixedObjectPrimitiveContactInheritance.standingDistinction_or_not
    (System : FixedObjectPrimitiveContactInheritance)
    (r : Nat)
    (left right : System.Form (r + 1)) :
    System.standingDistinction r left right \/
      Not (System.standingDistinction r left right) := by
  exact Classical.em _

/-- Skin cannot be used as a primitive standing-producing route. -/
theorem FixedObjectPrimitiveContactInheritance.skin_cannot_create_standing
    (System : FixedObjectPrimitiveContactInheritance)
    (r : Nat)
    (left right : System.Form (r + 1))
    (skin : System.skinEquivalent r left right) :
    Not (System.standingDistinction r left right) := by
  exact System.skinHasNoStandingAuthority r left right skin

/--
Same inherited form fixes the determinate object. A non-skin distinction would
need primitive contact and thereby change that object, so only skin remains.
-/
theorem FixedObjectPrimitiveContactInheritance.sameInheritedForm_implies_skin
    (System : FixedObjectPrimitiveContactInheritance)
    (r : Nat)
    (left right : System.Form (r + 1))
    (sameInheritedForm :
      System.inheritedForm r left = System.inheritedForm r right) :
    System.skinEquivalent r left right := by
  apply Classical.byContradiction
  intro nonSkin
  have standing : System.standingDistinction r left right :=
    System.nonSkinIsStandingBearing r left right nonSkin
  have contact : System.primitiveContact r left right :=
    System.nonInheritedStandingRequiresPrimitiveContact
      r left right sameInheritedForm standing
  have sameObject : System.sameDeterminateObject r left right :=
    System.sameInheritedFormPreservesObject
      r left right sameInheritedForm
  exact System.primitiveContactChangesDeterminateObject
    r left right contact sameObject

/-- Fixed-object inheritance is injective before any cardinality is taken. -/
theorem FixedObjectPrimitiveContactInheritance.inheritedForm_injective
    (System : FixedObjectPrimitiveContactInheritance)
    (r : Nat) :
    Function.Injective (System.inheritedForm r) := by
  intro left right sameInheritedForm
  exact System.skinFinality r left right <|
    System.sameInheritedForm_implies_skin
      r left right sameInheritedForm

/--
The fixed-object primitive-contact theorem populates the skin branch of the
earlier four-way inheritance surface directly.
-/
noncomputable def
    FixedObjectPrimitiveContactInheritance.toAdmissibleBivalentFormInheritance
    {S : SunflowerCarrier}
    (System : FixedObjectPrimitiveContactInheritance)
    (corpus : KernelFirstCorpusMachinery S) :
    AdmissibleBivalentFormInheritance corpus where
  Form := System.Form
  formFintype := System.formFintype
  semantics := System.semantics
  inheritedForm := System.inheritedForm
  skinEquivalent := System.skinEquivalent
  tensorSplit := fun _ _ _ => False
  sunflowerRealization := fun _ _ _ => False
  sameInheritedFormExhaustive := by
    intro r left right sameInheritedForm
    exact Or.inl <|
      System.sameInheritedForm_implies_skin
        r left right sameInheritedForm
  skinFinality := System.skinFinality
  tensorSplitExcluded := fun _ _ _ impossible => impossible
  sunflowerExcluded := fun _ _ _ impossible => impossible

/-- A lower-rank seed bound is inherited unchanged by the fixed object. -/
theorem FixedObjectPrimitiveContactInheritance.formCard_le_of_baseBound
    {S : SunflowerCarrier}
    (System : FixedObjectPrimitiveContactInheritance)
    (corpus : KernelFirstCorpusMachinery S)
    {B : Nat}
    (baseBound :
      (System.toAdmissibleBivalentFormInheritance corpus).formCard 0 <= B)
    (r : Nat) :
    (System.toAdmissibleBivalentFormInheritance corpus).formCard r <= B := by
  exact (System.toAdmissibleBivalentFormInheritance corpus).formCard_le_of_baseBound
    baseBound r

/--
Kernel-faithful inheritance with determinate identity made explicit. Identity
comparison is licensed by the endpoint kernel, and the stability equation says
that rank deletion preserves the identity carried by the inherited form.
-/
structure KernelFaithfulStableIdentityInheritance
    {S : SunflowerCarrier}
    (corpus : KernelFirstCorpusMachinery S)
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch) where
  Form : Nat -> Type
  formFintype : forall r, Fintype (Form r)
  semantics : forall r, GovernedFormSemantics (Form r)
  inheritedForm : forall r, Form (r + 1) -> Form r
  Identity : Type
  determinateIdentity : forall r, Form r -> Identity
  identityStable :
    forall r, forall form : Form (r + 1),
      determinateIdentity (r + 1) form =
        determinateIdentity r (inheritedForm r form)
  skinEquivalent :
    forall r, Form (r + 1) -> Form (r + 1) -> Prop
  standingDistinction :
    forall r, Form (r + 1) -> Form (r + 1) -> Prop
  primitiveContact :
    forall r, Form (r + 1) -> Form (r + 1) -> Prop
  skinHasNoStandingAuthority :
    forall r, forall left right : Form (r + 1),
      skinEquivalent r left right ->
      Not (standingDistinction r left right)
  nonSkinIsStandingBearing :
    forall r, forall left right : Form (r + 1),
      Not (skinEquivalent r left right) ->
      standingDistinction r left right
  nonInheritedStandingRequiresPrimitiveContact :
    forall r, forall left right : Form (r + 1),
      inheritedForm r left = inheritedForm r right ->
      standingDistinction r left right ->
      primitiveContact r left right
  primitiveContactChangesIdentity :
    forall r, forall left right : Form (r + 1),
      primitiveContact r left right ->
      determinateIdentity (r + 1) left ≠
        determinateIdentity (r + 1) right
  skinFinality :
    forall r, forall left right : Form (r + 1),
      skinEquivalent r left right -> left = right

def KernelFaithfulStableIdentityInheritance.kernelLicense
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    (_System : KernelFaithfulStableIdentityInheritance corpus endpointUse) :
    KernelLicensedSameness S :=
  corpus.samenessAtEndpointUse endpointUse

/-- Identity comparison is downstream of the kernel rather than primitive. -/
theorem KernelFaithfulStableIdentityInheritance.identityLicensed
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    (System : KernelFaithfulStableIdentityInheritance corpus endpointUse) :
    System.kernelLicense.identity := by
  exact System.kernelLicense.identity_holds

theorem KernelFaithfulStableIdentityInheritance.samenessMeaningful
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    (System : KernelFaithfulStableIdentityInheritance corpus endpointUse) :
    System.kernelLicense.sameness := by
  exact System.kernelLicense.sameness_holds

/-- Stable inherited identity turns equal inherited forms into one object. -/
theorem KernelFaithfulStableIdentityInheritance.sameInheritedForm_preservesIdentity
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    (System : KernelFaithfulStableIdentityInheritance corpus endpointUse)
    (r : Nat)
    (left right : System.Form (r + 1))
    (sameInheritedForm :
      System.inheritedForm r left = System.inheritedForm r right) :
    System.determinateIdentity (r + 1) left =
      System.determinateIdentity (r + 1) right := by
  calc
    System.determinateIdentity (r + 1) left =
        System.determinateIdentity r (System.inheritedForm r left) :=
      System.identityStable r left
    _ = System.determinateIdentity r (System.inheritedForm r right) :=
      congrArg (System.determinateIdentity r) sameInheritedForm
    _ = System.determinateIdentity (r + 1) right :=
      (System.identityStable r right).symm

/-- The stable identity source discharges the former object-preservation field. -/
noncomputable def
    KernelFaithfulStableIdentityInheritance.toFixedObjectPrimitiveContactInheritance
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    (System : KernelFaithfulStableIdentityInheritance corpus endpointUse) :
    FixedObjectPrimitiveContactInheritance where
  Form := System.Form
  formFintype := System.formFintype
  semantics := System.semantics
  inheritedForm := System.inheritedForm
  skinEquivalent := System.skinEquivalent
  standingDistinction := System.standingDistinction
  sameDeterminateObject := fun r left right =>
    System.determinateIdentity (r + 1) left =
      System.determinateIdentity (r + 1) right
  primitiveContact := System.primitiveContact
  skinHasNoStandingAuthority := System.skinHasNoStandingAuthority
  nonSkinIsStandingBearing := System.nonSkinIsStandingBearing
  sameInheritedFormPreservesObject := by
    intro r left right sameInheritedForm
    exact System.sameInheritedForm_preservesIdentity
      r left right sameInheritedForm
  nonInheritedStandingRequiresPrimitiveContact :=
    System.nonInheritedStandingRequiresPrimitiveContact
  primitiveContactChangesDeterminateObject :=
    System.primitiveContactChangesIdentity
  skinFinality := System.skinFinality

/-- Kernel-faithful stable identity makes inherited true forms injective. -/
theorem KernelFaithfulStableIdentityInheritance.inheritedForm_injective
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    (System : KernelFaithfulStableIdentityInheritance corpus endpointUse)
    (r : Nat) :
    Function.Injective (System.inheritedForm r) := by
  exact System.toFixedObjectPrimitiveContactInheritance.inheritedForm_injective r

/--
One fixed determinate-identity carrier used at every rank. Inheritance is the
identity map, so stability is definitional; the endpoint kernel supplies the
license for comparing these identities.
-/
noncomputable def kernelFaithfulFixedIdentityInheritance
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (Identity : Type)
    [Fintype Identity]
    (semantics : GovernedFormSemantics Identity) :
    KernelFaithfulStableIdentityInheritance corpus endpointUse where
  Form := fun _ => Identity
  formFintype := fun _ => inferInstance
  semantics := fun _ => semantics
  inheritedForm := fun _ identity => identity
  Identity := Identity
  determinateIdentity := fun _ identity => identity
  identityStable := by
    intro _ _
    rfl
  skinEquivalent := fun _ left right => left = right
  standingDistinction := fun _ left right => left ≠ right
  primitiveContact := fun _ left right => left ≠ right
  skinHasNoStandingAuthority := by
    intro _ left right same distinct
    exact distinct same
  nonSkinIsStandingBearing := by
    intro _ _ _ distinct
    exact distinct
  nonInheritedStandingRequiresPrimitiveContact := by
    intro _ _ _ _ distinct
    exact distinct
  primitiveContactChangesIdentity := by
    intro _ _ _ contact
    exact contact
  skinFinality := by
    intro _ _ _ same
    exact same

theorem kernelFaithfulFixedIdentityInheritance_inheritedForm_eq
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (Identity : Type)
    [Fintype Identity]
    (semantics : GovernedFormSemantics Identity)
    (r : Nat)
    (identity : Identity) :
    (kernelFaithfulFixedIdentityInheritance (corpus := corpus)
      endpointUse Identity semantics).inheritedForm r identity = identity := by
  rfl

theorem kernelFaithfulFixedIdentityInheritance_identityStable
    {S : SunflowerCarrier}
    {corpus : KernelFirstCorpusMachinery S}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (Identity : Type)
    [Fintype Identity]
    (semantics : GovernedFormSemantics Identity)
    (r : Nat)
    (identity : Identity) :
    (kernelFaithfulFixedIdentityInheritance (corpus := corpus)
      endpointUse Identity semantics).determinateIdentity (r + 1) identity =
    (kernelFaithfulFixedIdentityInheritance (corpus := corpus)
      endpointUse Identity semantics).determinateIdentity r
        ((kernelFaithfulFixedIdentityInheritance (corpus := corpus)
          endpointUse Identity semantics).inheritedForm r identity) := by
  rfl

/--
Concrete governed deletion on the canonical minimal blocker. The predecessor
is the actual private-witness residual, not an abstract coordinate.
-/
structure GovernedMinimalBlockerDeletion
    (Form : Type)
    [Fintype Form]
    [Nonempty Form]
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)) where
  semantics : GovernedFormSemantics Form
  form : {x // x ∈ MinimalBlocker.minimalBlocker F} -> Form
  skinEquivalent :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  tensorSplit :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  nonSkinCollisionExhaustive :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      PrivateWitnessReduction.residual F left =
        PrivateWitnessReduction.residual F right ->
      form left = form right ->
      Not (skinEquivalent left right) ->
      tensorSplit left right \/
      Concrete.HasSunflower k F \/
      Exists (fun factor :
        (Concrete.concreteSunflowerCarrier alpha (r + 1) k).StandingFactor =>
        corpus.fixedDomainClosure.disposition factor =
          SameScopeFactorDisposition.independentAuthorizer)
  skinFinality :
    forall left right, skinEquivalent left right -> left = right
  tensorSplitExcluded :
    forall left right, tensorSplit left right -> False

/--
The literal private-residual fibers populate a concrete `k`-slot governed
deletion with no semantic source premise. All slots carry the bounded-fiber
role; equal parent and equal slot are already combinatorially final.
-/
noncomputable def privateWitnessResidualFiberDeletion
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    [Nonempty (Fin k)]
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)) :
    GovernedMinimalBlockerDeletion (Fin k) F noSunflower corpus where
  semantics := ⟨fun _ => .boundedFiber⟩
  form := PrivateWitnessReduction.residualFiberSlot F noSunflower
  skinEquivalent := fun left right => left = right
  tensorSplit := fun _ _ => False
  nonSkinCollisionExhaustive := by
    intro left right sameResidual sameSlot nonSkin
    exact False.elim <| nonSkin <|
      PrivateWitnessReduction.eq_of_same_residual_same_fiberSlot
        F noSunflower left right sameResidual sameSlot
  skinFinality := fun _ _ skin => skin
  tensorSplitExcluded := fun _ _ impossible => impossible

/-- The exact concrete local lemma: skin, tensor, sunflower, or authorizer. -/
theorem GovernedMinimalBlockerDeletion.skin_or_forbidden
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : GovernedMinimalBlockerDeletion
      Form F noSunflower corpus)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameResidual :
      PrivateWitnessReduction.residual F left =
        PrivateWitnessReduction.residual F right)
    (sameForm : Population.form left = Population.form right) :
    Population.skinEquivalent left right \/
    Population.tensorSplit left right \/
    Concrete.HasSunflower k F \/
    Exists (fun factor :
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k).StandingFactor =>
      corpus.fixedDomainClosure.disposition factor =
        SameScopeFactorDisposition.independentAuthorizer) := by
  by_cases skin : Population.skinEquivalent left right
  · exact Or.inl skin
  · exact Or.inr <|
      Population.nonSkinCollisionExhaustive
        left right sameResidual sameForm skin

/-- Same residual parent and same governed form force one blocker coordinate. -/
theorem GovernedMinimalBlockerDeletion.collision
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : GovernedMinimalBlockerDeletion
      Form F noSunflower corpus)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameResidual :
      PrivateWitnessReduction.residual F left =
        PrivateWitnessReduction.residual F right)
    (sameForm : Population.form left = Population.form right) :
    left = right := by
  rcases Population.skin_or_forbidden
      left right sameResidual sameForm with skin | forbidden
  · exact Population.skinFinality left right skin
  · rcases forbidden with tensor | sunOrIndependent
    · exact False.elim (Population.tensorSplitExcluded left right tensor)
    · rcases sunOrIndependent with sunflower | independent
      · exact False.elim (noSunflower sunflower)
      · rcases independent with ⟨factor, forbidden⟩
        exact False.elim <|
          corpus.fixedDomainClosure.excludesIndependentAuthorizer
            factor forbidden

noncomputable def residualParent
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    {edge // edge ∈ (PrivateWitnessReduction.residualFamily F).edges} :=
  ⟨PrivateWitnessReduction.residual F x,
    PrivateWitnessReduction.mem_residualFamily_iff.mpr ⟨x, rfl⟩⟩

noncomputable def GovernedMinimalBlockerDeletion.deletionCode
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : GovernedMinimalBlockerDeletion
      Form F noSunflower corpus) :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {edge // edge ∈ (PrivateWitnessReduction.residualFamily F).edges} ×
        Form :=
  fun x => (residualParent F x, Population.form x)

theorem GovernedMinimalBlockerDeletion.deletionCode_injective
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : GovernedMinimalBlockerDeletion
      Form F noSunflower corpus) :
    Function.Injective Population.deletionCode := by
  intro left right sameCode
  apply Population.collision left right
  · exact congrArg (fun pair => pair.1.val) sameCode
  · exact congrArg Prod.snd sameCode

/-- Structural deletion transition; the product cardinal is not primitive. -/
noncomputable def GovernedMinimalBlockerDeletion.deletionTransition
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : GovernedMinimalBlockerDeletion
      Form F noSunflower corpus) :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ↪
      ({edge // edge ∈
        (PrivateWitnessReduction.residualFamily F).edges} × Form) where
  toFun := Population.deletionCode
  inj' := Population.deletionCode_injective

/-- Counting appears only as the image of the structural transition. -/
theorem GovernedMinimalBlockerDeletion.minimalBlocker_card_le
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : GovernedMinimalBlockerDeletion
      Form F noSunflower corpus) :
    (MinimalBlocker.minimalBlocker F).card <=
      (PrivateWitnessReduction.residualFamily F).edges.card *
        governedFormCard Form := by
  have cardBound := Fintype.card_le_of_injective
    Population.deletionCode Population.deletionCode_injective
  simpa [governedFormCard, Fintype.card_prod] using cardBound

end GovernedDeletion
end V2
end SunflowerAASC
