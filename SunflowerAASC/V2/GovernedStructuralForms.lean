import SunflowerAASC.V2.BlockerSupportLayers
import SunflowerAASC.V2.ConstraintMapPopulation
import SunflowerAASC.V2.DenseCountercaseRange

namespace SunflowerAASC
namespace V2
namespace GovernedStructuralForms

/-- Semantic governance is attached to a structural form before it is counted. -/
structure GovernedFormSemantics (Form : Type) where
  role : Form -> AASCBlockerRole

/-- Standing is binary and is determined by the governed role. -/
def GovernedFormSemantics.StandingBearing
    {Form : Type}
    (semantics : GovernedFormSemantics Form)
    (form : Form) : Prop :=
  semantics.role form ≠ .skin

theorem GovernedFormSemantics.standingBearing_or_not
    {Form : Type}
    (semantics : GovernedFormSemantics Form)
    (form : Form) :
    semantics.StandingBearing form ∨
      Not (semantics.StandingBearing form) := by
  exact Classical.em _

/-- The numerical size is a downstream invariant of the governed form type. -/
def governedFormCard (Form : Type) [Fintype Form] : Nat :=
  Fintype.card Form

theorem governedFormCard_positive
    (Form : Type)
    [Fintype Form]
    [Nonempty Form] :
    0 < governedFormCard Form := by
  exact Fintype.card_pos

/-- Any finite presentation of the governed forms is merely an encoding. -/
noncomputable def governedFormEquivFin
    (Form : Type)
    [Fintype Form] :
    Form ≃ Fin (governedFormCard Form) :=
  Fintype.equivFin Form

/-- Equivalent encodings have the same downstream cardinality. -/
theorem governedFormCard_congr
    {Form Other : Type}
    [Fintype Form]
    [Fintype Other]
    (equiv : Form ≃ Other) :
    governedFormCard Form = governedFormCard Other :=
  Fintype.card_congr equiv

instance constraintSignatureNonempty :
    Nonempty ConstraintMapPopulation.ConstraintSignature :=
  ⟨(∅, .skin)⟩

/--
Structural population of a minimal blocker. The primitive data are governed
forms and the four exhaustive collision dispositions. No numerical slot is
chosen here.
-/
structure GovernedPrivateWitnessPopulation
    (Form : Type)
    [Fintype Form]
    [Nonempty Form]
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) where
  semantics : GovernedFormSemantics Form
  form : {x // x ∈ MinimalBlocker.minimalBlocker F} -> Form
  skinOutcome :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  tensorSplitOutcome :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  sunflowerOutcome :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  collisionExhaustive :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩ ->
      form left = form right ->
      left = right \/
      skinOutcome left right \/
      tensorSplitOutcome left right \/
      sunflowerOutcome left right
  skinFinality :
    forall left right, skinOutcome left right -> left = right
  tensorSplitExcluded :
    forall left right, tensorSplitOutcome left right -> False
  sunflowerExcluded :
    forall left right, sunflowerOutcome left right -> False

/-- A completed endpoint factorization is already a governed-form population. -/
noncomputable def governedPopulationOfConstraintFactorization
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Factorization :
      ConstraintMapPopulation.PrivateWitnessConstraintFactorization
        noSunflower) :
    GovernedPrivateWitnessPopulation
      ConstraintMapPopulation.ConstraintSignature F noSunflower where
  semantics := ⟨Prod.snd⟩
  form := fun x =>
    (Factorization.constraintProfile x, Factorization.forcedRole x)
  skinOutcome := fun _ _ => False
  tensorSplitOutcome := fun _ _ => False
  sunflowerOutcome := fun _ _ => False
  collisionExhaustive := by
    intro left right sameCell sameForm
    apply Or.inl
    exact MinimalBlocker.eq_of_sameEndpointIncidence F left right <|
      Factorization.endpointIncidenceFactors
        left right sameCell
        (congrArg Prod.fst sameForm)
        (congrArg Prod.snd sameForm)
  skinFinality := fun _ _ impossible => False.elim impossible
  tensorSplitExcluded := fun _ _ impossible => impossible
  sunflowerExcluded := fun _ _ impossible => impossible

/--
The existing corpus population assembles its profile and role into one governed
form. The number `256` is not used in this construction.
-/
noncomputable def governedPopulationOfConstraintPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : ConstraintMapPopulation.PrivateWitnessConstraintPopulation
      noSunflower corpus) :
    GovernedPrivateWitnessPopulation
      ConstraintMapPopulation.ConstraintSignature F noSunflower where
  semantics := ⟨Prod.snd⟩
  form := fun x =>
    (Population.constraintProfile x, Population.forcedRole x)
  skinOutcome := fun _ _ => False
  tensorSplitOutcome := fun _ _ => False
  sunflowerOutcome := fun _ _ => False
  collisionExhaustive := by
    intro left right sameCell sameForm
    apply Or.inl
    exact Population.withinCellTensorMultiplicityCollapse
      left right sameCell
      (congrArg Prod.fst sameForm)
      (congrArg Prod.snd sameForm)
  skinFinality := fun _ _ impossible => False.elim impossible
  tensorSplitExcluded := fun _ _ impossible => impossible
  sunflowerExcluded := fun _ _ impossible => impossible

theorem constraintSignature_governedFormCard_eq :
    governedFormCard ConstraintMapPopulation.ConstraintSignature = 256 := by
  rw [governedFormCard,
    ConstraintMapPopulation.constraintSignature_card,
    ConstraintMapPopulation.constraintSignatureSize_eq]

/-- Cardinal encoding is derived only after structural population is complete. -/
noncomputable def GovernedPrivateWitnessPopulation.toSupportFiberCompression
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Population : GovernedPrivateWitnessPopulation Form F noSunflower) :
    BlockerSupportLayers.SupportFiberCompression
      (governedFormCard Form) F noSunflower where
  effectiveBlocker := MinimalBlocker.minimalBlocker F
  effective_subset_raw := MinimalBlocker.minimalBlocker_subset_raw F
  fiberSlot := fun x => governedFormEquivFin Form (Population.form x)
  skinOutcome := Population.skinOutcome
  tensorSplitOutcome := Population.tensorSplitOutcome
  sunflowerOutcome := Population.sunflowerOutcome
  collisionExhaustive := by
    intro left right sameCell sameSlot
    exact Population.collisionExhaustive left right sameCell <|
      (governedFormEquivFin Form).injective sameSlot
  skinFinality := Population.skinFinality
  tensorSplitExcluded := Population.tensorSplitExcluded
  sunflowerExcluded := Population.sunflowerExcluded
  preservesRawHits := by
    intro edge edge_mem _rawHit
    exact MinimalBlocker.minimalBlocker_hitsEveryEdge F edge edge_mem

/-- The derived cardinal bounds the governed population inside support cells. -/
theorem GovernedPrivateWitnessPopulation.minimalBlocker_card_le
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Population : GovernedPrivateWitnessPopulation Form F noSunflower) :
    (MinimalBlocker.minimalBlocker F).card <=
      VennSeparation.vennAlphabetSize k (governedFormCard Form) := by
  exact Population.toSupportFiberCompression.toVennCompressedBlocker.effective_card_le

/-- One governed form type supplies every rank; its cardinal is not input data. -/
structure RankUniformGovernedFormSource
    (alpha : Type)
    [DecidableEq alpha]
    (k : Nat)
    (Form : Type)
    [Fintype Form]
    [Nonempty Form] where
  populate :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      GovernedPrivateWitnessPopulation Form F noSunflower

noncomputable def RankUniformGovernedFormSource.toSupportFiberSource
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    (Src : RankUniformGovernedFormSource alpha k Form) :
    BlockerSupportLayers.RankUniformSupportFiberSource
      alpha k (governedFormCard Form) where
  fiberBound_positive := governedFormCard_positive Form
  compress := fun r F noSunflower =>
    (Src.populate r F noSunflower).toSupportFiberCompression

/-- Structural governance yields the numerical endpoint only as a corollary. -/
theorem sunflower_of_rankUniformGovernedForms
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    (Src : RankUniformGovernedFormSource alpha k Form)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      VennSeparation.vennAlphabetSize k (governedFormCard Form) ^ n <
        F.edges.card) :
    Concrete.HasSunflower k F := by
  exact BlockerSupportLayers.sunflower_of_supportFiberCompression
    Src.toSupportFiberSource F sizeExcess

/--
The preferred source asks for structural population only in a quantitative
countercase. Sparse families require no governed-form assignment.
-/
structure DenseGovernedFormSource
    (alpha : Type)
    [DecidableEq alpha]
    (k : Nat)
    (Form : Type)
    [Fintype Form]
    [Nonempty Form] where
  populate :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      VennSeparation.vennAlphabetSize k
          (governedFormCard Form) ^ (r + 1) <
        F.edges.card ->
      GovernedPrivateWitnessPopulation Form F noSunflower

noncomputable def DenseGovernedFormSource.toDenseCountercaseSource
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    (Src : DenseGovernedFormSource alpha k Form) :
    EffectiveBlocker.DenseCountercaseSource alpha k
      (VennSeparation.vennAlphabetSize k (governedFormCard Form)) where
  certificate := by
    intro r F noSunflower sizeExcess
    let Population := Src.populate r F noSunflower sizeExcess
    exact {
      blocker := MinimalBlocker.minimalBlocker F
      blocker_card_le := Population.minimalBlocker_card_le
      hitsEveryEdge := by
        intro edge edge_mem
        rcases Finset.not_disjoint_iff.mp
            (MinimalBlocker.minimalBlocker_hitsEveryEdge F edge edge_mem) with
          ⟨x, x_edge, x_blocker⟩
        exact ⟨x, x_blocker, x_edge⟩ }

/-- Dense structural governance yields the endpoint with counting downstream. -/
theorem sunflower_of_denseGovernedForms
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {Form : Type}
    [Fintype Form]
    [Nonempty Form]
    (Src : DenseGovernedFormSource alpha k Form)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      VennSeparation.vennAlphabetSize k (governedFormCard Form) ^ n <
        F.edges.card) :
    Concrete.HasSunflower k F := by
  exact EffectiveBlocker.sunflower_of_card_gt_pow_of_denseCountercaseSource
    Src.toDenseCountercaseSource F sizeExcess

/--
The former large-rank AASC population source factors through the structural
source. The numerical corpus base is used only to identify the final derived
cardinality.
-/
noncomputable def largeRankConstraintPopulation_toDenseGovernedFormSource
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : DenseCountercaseRange.LargeRankConstraintPopulationSource
      alpha k k_nondegenerate) :
    DenseGovernedFormSource alpha k
      ConstraintMapPopulation.ConstraintSignature where
  populate := by
    intro r F noSunflower sizeExcess
    have corpusSizeExcess :
        ConstraintMapPopulation.corpusConstraintBase k ^ (r + 1) <
          F.edges.card := by
      simpa [ConstraintMapPopulation.corpusConstraintBase,
        governedFormCard,
        ConstraintMapPopulation.constraintSignature_card] using sizeExcess
    by_cases factorialRange :
        (k - 1) * DenseCountercaseRange.reflectedFactorialBase (r + 1) <=
          ConstraintMapPopulation.corpusConstraintBase k
    · exact governedPopulationOfConstraintFactorization <|
        DenseCountercaseRange.privateWitnessFactorization_of_reflectedFactorialRange
          factorialRange noSunflower corpusSizeExcess
    · exact governedPopulationOfConstraintPopulation <|
        (Src.populate r F noSunflower corpusSizeExcess
          (Nat.lt_of_not_ge factorialRange)).population

/-- The corrected structural closeout has one semantic population obligation. -/
inductive GovernedClosureObligation where
  | denseGovernedFormPopulation
deriving DecidableEq, Repr

def governedClosureObligations : List GovernedClosureObligation :=
  [.denseGovernedFormPopulation]

theorem governedClosureObligationCount_eq :
    governedClosureObligations.length = 1 := by
  rfl

/--
Rank-indexed governed forms may grow by structural branching. The role ledger,
not a chosen numeral system, bounds that branching.
-/
structure RankIndexedGovernedForms where
  Form : Nat -> Type
  formFintype : forall r, Fintype (Form r)
  transition :
    forall r,
      Form (r + 1) ↪
        (Form r × AASCBlockerRole)

def RankIndexedGovernedForms.formCard
    (System : RankIndexedGovernedForms)
    (r : Nat) : Nat :=
  @Fintype.card (System.Form r) (System.formFintype r)

theorem RankIndexedGovernedForms.card_succ_le
    (System : RankIndexedGovernedForms)
    (r : Nat) :
    System.formCard (r + 1) <= 4 * System.formCard r := by
  letI := System.formFintype (r + 1)
  letI := System.formFintype r
  have cardBound := Fintype.card_le_of_injective
    (System.transition r) (System.transition r).injective
  change Fintype.card (System.Form (r + 1)) <=
    4 * Fintype.card (System.Form r)
  simpa [Fintype.card_prod, WitnessCompression.aascBlockerRole_card,
    Nat.mul_comm] using cardBound

/-- The numerical `4^r` estimate is derived from structural role transitions. -/
theorem RankIndexedGovernedForms.formCard_le_role_pow
    (System : RankIndexedGovernedForms)
    (r : Nat) :
    System.formCard r <= 4 ^ r * System.formCard 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        System.formCard (r + 1) <= 4 * System.formCard r :=
          System.card_succ_le r
        _ <= 4 * (4 ^ r * System.formCard 0) :=
          Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (r + 1) * System.formCard 0 := by
          rw [pow_succ]
          ac_rfl

end GovernedStructuralForms
end V2
end SunflowerAASC
