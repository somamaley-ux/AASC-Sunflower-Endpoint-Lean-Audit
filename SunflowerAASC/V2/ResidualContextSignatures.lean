import SunflowerAASC.V2.ResidualGateContextQuotient

namespace SunflowerAASC
namespace V2
namespace ResidualContextSignatures

open ResidualVennPincer
open ResidualGateContextQuotient

/-- The gate coordinates where one component product differs from a reference. -/
noncomputable def contextDisagreementSupport
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (reference context : ResidualComponentProduct F) :
    Finset (GateSlot F) := by
  classical
  exact Finset.univ.filter fun slot =>
    productComponentAt F context slot ≠ productComponentAt F reference slot

theorem mem_contextDisagreementSupport_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (reference context : ResidualComponentProduct F)
    (slot : GateSlot F) :
    slot ∈ contextDisagreementSupport F reference context ↔
      productComponentAt F context slot ≠
        productComponentAt F reference slot := by
  simp [contextDisagreementSupport]

theorem productComponentAt_normalize_self
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (reference code : ResidualComponentProduct F)
    (slot : GateSlot F) :
    productComponentAt F (normalizeProductAtSlot F reference slot code) slot =
      productComponentAt F reference slot := by
  classical
  cases slot with
  | none => simp [normalizeProductAtSlot, productComponentAt]
  | some petal => simp [normalizeProductAtSlot, productComponentAt]

/-- Normalization changes only the selected gate coordinate. -/
theorem productComponentAt_normalize_of_ne
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (reference code : ResidualComponentProduct F)
    (selected other : GateSlot F)
    (different : other ≠ selected) :
    productComponentAt F (normalizeProductAtSlot F reference selected code) other =
      productComponentAt F code other := by
  classical
  cases selected with
  | none =>
      cases other with
      | none => exact False.elim (different rfl)
      | some petal => simp [normalizeProductAtSlot, productComponentAt]
  | some selectedPetal =>
      cases other with
      | none => simp [normalizeProductAtSlot, productComponentAt]
      | some otherPetal =>
          have petalDifferent : otherPetal ≠ selectedPetal := by
            intro same
            subst otherPetal
            exact different rfl
          simp [normalizeProductAtSlot, productComponentAt, Function.update,
            petalDifferent]

/-- The selected gate coordinate is erased from a normalized context. -/
theorem selectedSlot_not_mem_contextSupport
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    selected ∉ contextDisagreementSupport F missing.code
      (gateContextCode F missing selected edge) := by
  rw [mem_contextDisagreementSupport_iff]
  exact not_ne_iff.mpr <|
    productComponentAt_normalize_self
      F missing.code (residualProductCode F edge) selected

/-- Every component product is determined by its values at all gate slots. -/
theorem product_eq_of_components_eq
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : ResidualComponentProduct F)
    (sameComponents : ∀ slot : GateSlot F,
      productComponentAt F left slot = productComponentAt F right slot) :
    left = right := by
  apply Prod.ext
  · funext petal
    apply Subtype.ext
    simpa [productComponentAt] using sameComponents (some petal)
  · apply Subtype.ext
    simpa [productComponentAt] using sameComponents none

theorem productComponents_disjoint_of_ne
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (code : ResidualComponentProduct F)
    (left right : GateSlot F)
    (different : left ≠ right) :
    Disjoint (productComponentAt F code left)
      (productComponentAt F code right) := by
  classical
  cases left with
  | none =>
      cases right with
      | none => exact False.elim (different rfl)
      | some petal =>
          have component_subset_support :
              (code.1 petal).val ⊆ residualSupport F := by
            intro y y_mem
            have y_petal := petalComponent_subset_petal F petal (code.1 petal) y_mem
            exact Finset.mem_biUnion.mpr ⟨petal.val, petal.property, y_petal⟩
          exact (outsideComponent_disjoint_support F code.2).mono_right
            component_subset_support
  | some leftPetal =>
      cases right with
      | none =>
          have component_subset_support :
              (code.1 leftPetal).val ⊆ residualSupport F := by
            intro y y_mem
            have y_petal := petalComponent_subset_petal
              F leftPetal (code.1 leftPetal) y_mem
            exact Finset.mem_biUnion.mpr
              ⟨leftPetal.val, leftPetal.property, y_petal⟩
          exact (outsideComponent_disjoint_support F code.2).symm.mono_left
            component_subset_support
      | some rightPetal =>
          have petalsDifferent : leftPetal ≠ rightPetal := by
            intro same
            subst rightPetal
            exact different rfl
          have petalsDisjoint : Disjoint leftPetal.val rightPetal.val := by
            simpa using
              (residualMatching F).matching.residuals_disjoint
                leftPetal.val rightPetal.val
                leftPetal.property rightPetal.property
                (fun same => petalsDifferent (Subtype.ext same))
          exact petalsDisjoint.mono
            (petalComponent_subset_petal F leftPetal (code.1 leftPetal))
            (petalComponent_subset_petal F rightPetal (code.1 rightPetal))

/--
A lower-rank gate member with a nonempty normalized context has two distinct
endpoint-local disagreement coordinates: the selected gate and one surviving
context coordinate.
-/
structure SecondaryGateDisagreement
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) where
  other : GateSlot F
  other_ne_selected : other ≠ selected
  selectedDiffers :
    productComponentAt F (residualProductCode F edge) selected ≠
      productComponentAt F missing.code selected
  otherDiffers :
    productComponentAt F (residualProductCode F edge) other ≠
      productComponentAt F missing.code other

/-- The concrete disjoint-factor geometry carried by a secondary disagreement. -/
structure SecondaryGateDisjointFactorWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    extends SecondaryGateDisagreement F missing selected edge where
  componentFactorsDisjoint :
    Disjoint
      (productComponentAt F (residualProductCode F edge) selected)
      (productComponentAt F (residualProductCode F edge) other)

def SecondaryGateDisagreement.toDisjointFactorWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {missing : MissingComponentCombination F}
    {selected : GateSlot F}
    {edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}}
    (witness : SecondaryGateDisagreement F missing selected edge) :
    SecondaryGateDisjointFactorWitness F missing selected edge where
  toSecondaryGateDisagreement := witness
  componentFactorsDisjoint :=
    productComponents_disjoint_of_ne F (residualProductCode F edge)
      selected witness.other witness.other_ne_selected.symm

theorem nonempty_contextSupport_gives_secondaryDisagreement
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (edge_mem : edge ∈ lowerRankGateDisagreementFiber F missing selected)
    (supportNonempty :
      (contextDisagreementSupport F missing.code
        (gateContextCode F missing selected edge)).Nonempty) :
    Nonempty (SecondaryGateDisagreement F missing selected edge) := by
  classical
  rcases supportNonempty with ⟨other, other_mem⟩
  have other_ne_selected : other ≠ selected := by
    intro same
    subst other
    exact selectedSlot_not_mem_contextSupport F missing selected edge other_mem
  have gate_mem : edge ∈ gateDisagreementFiber F missing selected :=
    (Finset.mem_filter.mp edge_mem).1
  have selected_eq : gateDisagreementSlot F missing edge = selected :=
    (mem_gateDisagreementFiber_iff F missing selected edge).mp gate_mem
  have selectedDiffers :
      productComponentAt F (residualProductCode F edge) selected ≠
        productComponentAt F missing.code selected := by
    simpa [selected_eq] using gateDisagreementSlot_spec F missing edge
  have normalizedDiffers :
      productComponentAt F (gateContextCode F missing selected edge) other ≠
        productComponentAt F missing.code other :=
    (mem_contextDisagreementSupport_iff F missing.code
      (gateContextCode F missing selected edge) other).mp other_mem
  have preserved :
      productComponentAt F (gateContextCode F missing selected edge) other =
        productComponentAt F (residualProductCode F edge) other := by
    exact productComponentAt_normalize_of_ne
      F missing.code (residualProductCode F edge) selected other other_ne_selected
  rw [preserved] at normalizedDiffers
  exact ⟨{
    other := other
    other_ne_selected := other_ne_selected
    selectedDiffers := selectedDiffers
    otherDiffers := normalizedDiffers }⟩

theorem nonempty_contextSupport_gives_secondaryDisjointFactorWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (edge_mem : edge ∈ lowerRankGateDisagreementFiber F missing selected)
    (supportNonempty :
      (contextDisagreementSupport F missing.code
        (gateContextCode F missing selected edge)).Nonempty) :
    Nonempty (SecondaryGateDisjointFactorWitness F missing selected edge) := by
  rcases nonempty_contextSupport_gives_secondaryDisagreement
      F missing selected edge edge_mem supportNonempty with ⟨witness⟩
  exact ⟨witness.toDisjointFactorWitness⟩

/-- No member of this gate branch carries an independent second disagreement. -/
def NoSecondaryGateDisagreement
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F) : Prop :=
  ∀ edge, edge ∈ lowerRankGateDisagreementFiber F missing selected ->
    Not (Nonempty (SecondaryGateDisagreement F missing selected edge))

/-- A strong concrete exclusion: no realized secondary disjoint-factor witness. -/
def NoSecondaryGateDisjointFactorWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F) : Prop :=
  ∀ edge, edge ∈ lowerRankGateDisagreementFiber F missing selected ->
    Not (Nonempty (SecondaryGateDisjointFactorWitness F missing selected edge))

theorem noSecondaryDisagreement_of_noSecondaryDisjointFactorWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (noFactor : NoSecondaryGateDisjointFactorWitness F missing selected) :
    NoSecondaryGateDisagreement F missing selected := by
  intro edge edge_mem secondary
  rcases secondary with ⟨witness⟩
  exact noFactor edge edge_mem ⟨witness.toDisjointFactorWitness⟩

/--
The concrete half of the terminal-prime interface. Every realized secondary
disjoint-factor witness must construct an actual tensor-split object. This is
the geometric population step; it does not assume that the split is excluded.
-/
structure SecondaryDisjointFactorTensorSplitRealization
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F) where
  TensorSplit : Type
  realize :
    ∀ edge,
      edge ∈ lowerRankGateDisagreementFiber F missing selected ->
      SecondaryGateDisjointFactorWitness F missing selected edge ->
      TensorSplit

/--
The AASC impossibility half of the interface: terminal primeness leaves no
realized tensor split. Keeping this separate from realization makes the
combinatorial-to-governance dependency explicit.
-/
structure TerminalPrimeTensorSplitImpossibility
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {missing : MissingComponentCombination F}
    {selected : GateSlot F}
    (Realization : SecondaryDisjointFactorTensorSplitRealization
      F missing selected) where
  excludes : Realization.TensorSplit -> False

/-- Realization followed by terminal-prime impossibility excludes every secondary factor. -/
theorem noSecondaryDisjointFactorWitness_of_terminalPrimeTensorSplit
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {missing : MissingComponentCombination F}
    {selected : GateSlot F}
    (Realization : SecondaryDisjointFactorTensorSplitRealization
      F missing selected)
    (Impossibility : TerminalPrimeTensorSplitImpossibility Realization) :
    NoSecondaryGateDisjointFactorWitness F missing selected := by
  intro edge edge_mem witness
  rcases witness with ⟨witness⟩
  exact Impossibility.excludes (Realization.realize edge edge_mem witness)

theorem context_eq_reference_of_support_empty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (reference context : ResidualComponentProduct F)
    (supportEmpty : contextDisagreementSupport F reference context = ∅) :
    context = reference := by
  apply product_eq_of_components_eq F
  intro slot
  by_contra differs
  have slot_mem : slot ∈ contextDisagreementSupport F reference context :=
    (mem_contextDisagreementSupport_iff F reference context slot).mpr differs
  rw [supportEmpty] at slot_mem
  exact Finset.notMem_empty slot slot_mem

theorem occupiedContext_support_empty_of_noSecondary
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (noSecondary : NoSecondaryGateDisagreement F missing selected)
    (context : {context // context ∈
      occupiedLowerRankGateContexts F missing selected}) :
    contextDisagreementSupport F missing.code context.val = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro contextSupport
  let edge := contextRepresentative F missing selected context
  have edge_mem : edge ∈ lowerRankGateDisagreementFiber F missing selected :=
    contextRepresentative_mem_lowerRankFiber F missing selected context
  have representativeContext : gateContextCode F missing selected edge = context.val :=
    contextRepresentative_context F missing selected context
  have representativeSupport :
      (contextDisagreementSupport F missing.code
        (gateContextCode F missing selected edge)).Nonempty := by
    simpa [representativeContext] using contextSupport
  exact noSecondary edge edge_mem
    (nonempty_contextSupport_gives_secondaryDisagreement
      F missing selected edge edge_mem representativeSupport)

/-- Once secondary tensor factors are impossible, every occupied context is the same context. -/
theorem occupiedContext_eq_of_noSecondaryDisjointFactorWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (noFactor : NoSecondaryGateDisjointFactorWitness F missing selected)
    (left right : {context // context ∈
      occupiedLowerRankGateContexts F missing selected}) :
    left = right := by
  have noSecondary :=
    noSecondaryDisagreement_of_noSecondaryDisjointFactorWitness
      F missing selected noFactor
  apply Subtype.ext
  have leftEmpty := occupiedContext_support_empty_of_noSecondary
    F missing selected noSecondary left
  have rightEmpty := occupiedContext_support_empty_of_noSecondary
    F missing selected noSecondary right
  exact (context_eq_reference_of_support_empty
    F missing.code left.val leftEmpty).trans
      (context_eq_reference_of_support_empty
        F missing.code right.val rightEmpty).symm

/-- Excluding a concrete two-slot disagreement collapses the context ledger. -/
theorem occupiedLowerRankGateContexts_card_le_one_of_noSecondary
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (noSecondary : NoSecondaryGateDisagreement F missing selected) :
    (occupiedLowerRankGateContexts F missing selected).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro left left_mem right right_mem
  have leftEmpty := occupiedContext_support_empty_of_noSecondary
    F missing selected noSecondary ⟨left, left_mem⟩
  have rightEmpty := occupiedContext_support_empty_of_noSecondary
    F missing selected noSecondary ⟨right, right_mem⟩
  exact (context_eq_reference_of_support_empty F missing.code left leftEmpty).trans
    (context_eq_reference_of_support_empty F missing.code right rightEmpty).symm

theorem lowerRankGateFiber_card_le_of_noSecondary
    {alpha : Type}
    [DecidableEq alpha]
    {r M : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (noSecondary : NoSecondaryGateDisagreement F missing selected)
    (sectionBound : ∀ context : {context // context ∈
      occupiedLowerRankGateContexts F missing selected},
      (gateContextSection F missing selected context).edges.card ≤ M) :
    (lowerRankGateDisagreementFiber F missing selected).card ≤ M := by
  simpa using lowerRankGateFiber_card_le_of_context_section_bounds
    F missing selected
      (occupiedLowerRankGateContexts_card_le_one_of_noSecondary
        F missing selected noSecondary)
      sectionBound

/-- The arbitrary context multiplier disappears once every two-slot witness is excluded. -/
theorem residualFamily_card_le_of_noSecondary
    {alpha : Type}
    [DecidableEq alpha]
    {r k M : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (noSecondary : ∀ selected : GateSlot F,
      NoSecondaryGateDisagreement F missing selected)
    (sectionBound : ∀ selected : GateSlot F,
      ∀ context : {context // context ∈
        occupiedLowerRankGateContexts F missing selected},
      (gateContextSection F missing selected context).edges.card ≤ M) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤
      k * (M + 1) := by
  simpa using residualFamily_card_le_of_context_section_bounds
    F noSunflower missing
      (fun selected => occupiedLowerRankGateContexts_card_le_one_of_noSecondary
        F missing selected (noSecondary selected))
      sectionBound

theorem minimalBlocker_card_le_of_noSecondary
    {alpha : Type}
    [DecidableEq alpha]
    {r k M : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (noSecondary : ∀ selected : GateSlot F,
      NoSecondaryGateDisagreement F missing selected)
    (sectionBound : ∀ selected : GateSlot F,
      ∀ context : {context // context ∈
        occupiedLowerRankGateContexts F missing selected},
      (gateContextSection F missing selected context).edges.card ≤ M) :
    (MinimalBlocker.minimalBlocker F).card ≤
      k * (k * (M + 1)) := by
  simpa using minimalBlocker_card_le_of_context_section_bounds
    F noSunflower missing
      (fun selected => occupiedLowerRankGateContexts_card_le_one_of_noSecondary
        F missing selected (noSecondary selected))
      sectionBound

theorem residualFamily_card_le_of_noSecondaryDisjointFactorWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r k M : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (noFactor : ∀ selected : GateSlot F,
      NoSecondaryGateDisjointFactorWitness F missing selected)
    (sectionBound : ∀ selected : GateSlot F,
      ∀ context : {context // context ∈
        occupiedLowerRankGateContexts F missing selected},
      (gateContextSection F missing selected context).edges.card ≤ M) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤
      k * (M + 1) := by
  exact residualFamily_card_le_of_noSecondary F noSunflower missing
    (fun selected => noSecondaryDisagreement_of_noSecondaryDisjointFactorWitness
      F missing selected (noFactor selected))
    sectionBound

theorem minimalBlocker_card_le_of_noSecondaryDisjointFactorWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r k M : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (noFactor : ∀ selected : GateSlot F,
      NoSecondaryGateDisjointFactorWitness F missing selected)
    (sectionBound : ∀ selected : GateSlot F,
      ∀ context : {context // context ∈
        occupiedLowerRankGateContexts F missing selected},
      (gateContextSection F missing selected context).edges.card ≤ M) :
    (MinimalBlocker.minimalBlocker F).card ≤
      k * (k * (M + 1)) := by
  exact minimalBlocker_card_le_of_noSecondary F noSunflower missing
    (fun selected => noSecondaryDisagreement_of_noSecondaryDisjointFactorWitness
      F missing selected (noFactor selected))
    sectionBound

theorem exists_component_distinction
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (left right : ResidualComponentProduct F)
    (distinct : left ≠ right) :
    ∃ slot : GateSlot F,
      productComponentAt F left slot ≠ productComponentAt F right slot := by
  by_contra noSlot
  push_neg at noSlot
  exact distinct (product_eq_of_components_eq F left right noSlot)

/-- A finite endpoint-local witness inside one coarse context-support cell. -/
structure SameSupportContextDistinctionWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (reference left right : ResidualComponentProduct F) where
  slot : GateSlot F
  leftDiffersRight :
    productComponentAt F left slot ≠ productComponentAt F right slot
  slotOccupiedOnLeft : slot ∈ contextDisagreementSupport F reference left
  slotOccupiedOnRight : slot ∈ contextDisagreementSupport F reference right

theorem sameSupport_distinct_has_finite_witness
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (reference left right : ResidualComponentProduct F)
    (sameSupport : contextDisagreementSupport F reference left =
      contextDisagreementSupport F reference right)
    (distinct : left ≠ right) :
    Nonempty (SameSupportContextDistinctionWitness F reference left right) := by
  classical
  rcases exists_component_distinction F left right distinct with ⟨slot, differs⟩
  have occupiedEither :
      productComponentAt F left slot ≠ productComponentAt F reference slot ∨
      productComponentAt F right slot ≠ productComponentAt F reference slot := by
    by_contra neither
    push_neg at neither
    exact differs (neither.1.trans neither.2.symm)
  have leftMem : slot ∈ contextDisagreementSupport F reference left := by
    rcases occupiedEither with leftOccupied | rightOccupied
    · exact (mem_contextDisagreementSupport_iff F reference left slot).mpr
        leftOccupied
    · rw [sameSupport]
      exact (mem_contextDisagreementSupport_iff F reference right slot).mpr
        rightOccupied
  have rightMem : slot ∈ contextDisagreementSupport F reference right := by
    rw [← sameSupport]
    exact leftMem
  exact ⟨{
    slot := slot
    leftDiffersRight := differs
    slotOccupiedOnLeft := leftMem
    slotOccupiedOnRight := rightMem }⟩

/-- Inject the at-most-`k` gate slots into a fixed `Fin k` support alphabet. -/
noncomputable def gateSlotEmbedding
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    GateSlot F ↪ Fin k :=
  (Fintype.equivFin (GateSlot F)).toEmbedding.trans
    ⟨Fin.castLE (gateSlot_card_le F noSunflower),
      Fin.castLE_injective (gateSlot_card_le F noSunflower)⟩

/-- The finite coarse code of one occupied normalized context. -/
noncomputable def occupiedContextSupportCode
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (context : {context // context ∈
      occupiedLowerRankGateContexts F missing selected}) :
    Finset (Fin k) :=
  (contextDisagreementSupport F missing.code context.val).map
    (gateSlotEmbedding F noSunflower)

theorem occupiedContextSupportCode_eq_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (left right : {context // context ∈
      occupiedLowerRankGateContexts F missing selected}) :
    occupiedContextSupportCode F noSunflower missing selected left =
        occupiedContextSupportCode F noSunflower missing selected right ↔
      contextDisagreementSupport F missing.code left.val =
        contextDisagreementSupport F missing.code right.val := by
  constructor
  · intro sameCode
    apply Finset.map_injective (gateSlotEmbedding F noSunflower)
    simpa [occupiedContextSupportCode] using sameCode
  · intro sameSupport
    simp [occupiedContextSupportCode, sameSupport]

/-- All coarse context-support cells occupied at one gate slot. -/
noncomputable def occupiedContextSupportCodes
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F) :
    Finset (Finset (Fin k)) :=
  Finset.univ.image
    (occupiedContextSupportCode F noSunflower missing selected)

theorem occupiedContextSupportCodes_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F) :
    (occupiedContextSupportCodes F noSunflower missing selected).card ≤ 2 ^ k := by
  calc
    (occupiedContextSupportCodes F noSunflower missing selected).card ≤
        (Finset.univ : Finset (Finset (Fin k))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ k := by simp [Fintype.card_finset]

/-- One coarse support cell of occupied normalized contexts. -/
noncomputable def occupiedContextSupportFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (code : Finset (Fin k)) :
    Finset {context // context ∈
      occupiedLowerRankGateContexts F missing selected} :=
  Finset.univ.filter fun context =>
    occupiedContextSupportCode F noSunflower missing selected context = code

theorem occupiedContexts_card_eq_sum_supportFibers
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F) :
    (occupiedLowerRankGateContexts F missing selected).card =
      ∑ code ∈ occupiedContextSupportCodes F noSunflower missing selected,
        (occupiedContextSupportFiber
          F noSunflower missing selected code).card := by
  classical
  simpa [occupiedContextSupportCodes, occupiedContextSupportFiber] using
    Finset.card_eq_sum_card_image
      (occupiedContextSupportCode F noSunflower missing selected)
      (Finset.univ : Finset {context // context ∈
        occupiedLowerRankGateContexts F missing selected})

theorem sameSupportCode_distinct_has_finite_witness
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (selected : GateSlot F)
    (left right : {context // context ∈
      occupiedLowerRankGateContexts F missing selected})
    (sameCode : occupiedContextSupportCode F noSunflower missing selected left =
      occupiedContextSupportCode F noSunflower missing selected right)
    (distinct : left ≠ right) :
    Nonempty (SameSupportContextDistinctionWitness
      F missing.code left.val right.val) := by
  apply sameSupport_distinct_has_finite_witness F missing.code left.val right.val
  · exact (occupiedContextSupportCode_eq_iff
      F noSunflower missing selected left right).mp sameCode
  · intro sameValue
    exact distinct (Subtype.ext sameValue)

end ResidualContextSignatures
end V2
end SunflowerAASC
