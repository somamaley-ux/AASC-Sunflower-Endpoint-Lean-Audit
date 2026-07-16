import SunflowerAASC.V2.ResidualGateSections

namespace SunflowerAASC
namespace V2
namespace ResidualGateContextQuotient

open ResidualVennPincer
open ResidualGateSections

/-- Replace one selected coordinate by a fixed reference component. -/
noncomputable def normalizeProductAtSlot
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (reference : ResidualComponentProduct F)
    (slot : GateSlot F)
    (code : ResidualComponentProduct F) : ResidualComponentProduct F := by
  classical
  cases slot with
  | none => exact (code.1, reference.2)
  | some petal =>
      exact (Function.update code.1 petal (reference.1 petal), code.2)

/-- The fixed context of a residual at a selected missing-tuple gate slot. -/
noncomputable def gateContextCode
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    ResidualComponentProduct F :=
  normalizeProductAtSlot F missing.code slot (residualProductCode F edge)

theorem product_eq_of_normalize_eq_of_component_eq
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (reference left right : ResidualComponentProduct F)
    (slot : GateSlot F)
    (sameContext :
      normalizeProductAtSlot F reference slot left =
        normalizeProductAtSlot F reference slot right)
    (sameSelected :
      productComponentAt F left slot = productComponentAt F right slot) :
    left = right := by
  classical
  cases slot with
  | none =>
      apply Prod.ext
      · simpa [normalizeProductAtSlot] using congrArg Prod.fst sameContext
      · apply Subtype.ext
        simpa [productComponentAt] using sameSelected
  | some petal =>
      apply Prod.ext
      · funext sibling
        by_cases same : sibling = petal
        · subst sibling
          apply Subtype.ext
          simpa [productComponentAt] using sameSelected
        · have sameFunctions := congrArg Prod.fst sameContext
          have sameAtSibling := congrFun sameFunctions sibling
          simpa [normalizeProductAtSlot, Function.update, same] using sameAtSibling
      · simpa [normalizeProductAtSlot] using congrArg Prod.snd sameContext

theorem edge_eq_of_same_context_and_component
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (left right : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (sameContext : gateContextCode F missing slot left =
      gateContextCode F missing slot right)
    (sameSelected :
      productComponentAt F (residualProductCode F left) slot =
        productComponentAt F (residualProductCode F right) slot) :
    left = right := by
  apply residualProductCode_injective F
  exact product_eq_of_normalize_eq_of_component_eq
    F missing.code (residualProductCode F left) (residualProductCode F right)
      slot sameContext sameSelected

/-- The contexts actually occupied inside one lower-rank gate branch. -/
noncomputable def occupiedLowerRankGateContexts
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F) :
    Finset (ResidualComponentProduct F) :=
  (lowerRankGateDisagreementFiber F missing slot).image
    (gateContextCode F missing slot)

/-- One exact fixed-context fiber inside a lower-rank gate branch. -/
noncomputable def lowerRankGateContextFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (context : ResidualComponentProduct F) :
    Finset {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges} :=
  (lowerRankGateDisagreementFiber F missing slot).filter fun edge =>
    gateContextCode F missing slot edge = context

theorem lowerRankGateFiber_card_eq_sum_contextFibers
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F) :
    (lowerRankGateDisagreementFiber F missing slot).card =
      ∑ context ∈ occupiedLowerRankGateContexts F missing slot,
        (lowerRankGateContextFiber F missing slot context).card := by
  classical
  simpa [occupiedLowerRankGateContexts, lowerRankGateContextFiber] using
    Finset.card_eq_sum_card_image
      (gateContextCode F missing slot)
      (lowerRankGateDisagreementFiber F missing slot)

/-- Select a realized lower-rank residual carrying one occupied context. -/
noncomputable def contextRepresentative
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (context : {context // context ∈
      occupiedLowerRankGateContexts F missing slot}) :
    {edge // edge ∈ (PrivateWitnessReduction.residualFamily F).edges} :=
  Classical.choose (Finset.mem_image.mp context.property)

theorem contextRepresentative_mem_lowerRankFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (context : {context // context ∈
      occupiedLowerRankGateContexts F missing slot}) :
    contextRepresentative F missing slot context ∈
      lowerRankGateDisagreementFiber F missing slot :=
  (Classical.choose_spec (Finset.mem_image.mp context.property)).1

theorem contextRepresentative_context
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (context : {context // context ∈
      occupiedLowerRankGateContexts F missing slot}) :
    gateContextCode F missing slot
      (contextRepresentative F missing slot context) = context.val :=
  (Classical.choose_spec (Finset.mem_image.mp context.property)).2

noncomputable def gateContextSectionRank
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (context : {context // context ∈
      occupiedLowerRankGateContexts F missing slot}) : Nat :=
  (productComponentAt F
    (residualProductCode F (contextRepresentative F missing slot context))
    slot).card

/-- The realized one-slot section attached to one occupied fixed context. -/
noncomputable def gateContextSection
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (context : {context // context ∈
      occupiedLowerRankGateContexts F missing slot}) :
    Concrete.UniformSetFamily alpha
      (gateContextSectionRank F missing slot context) := by
  cases slot with
  | none =>
      exact outsideSectionFactor F (contextRepresentative F missing none context)
  | some petal =>
      exact petalSectionFactor F
        (contextRepresentative F missing (some petal) context) petal

theorem gateContextSection_rank_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (context : {context // context ∈
      occupiedLowerRankGateContexts F missing slot}) :
    gateContextSectionRank F missing slot context < r + 1 := by
  exact (Finset.mem_filter.mp
    (contextRepresentative_mem_lowerRankFiber F missing slot context)).2

theorem gateContextSection_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (context : {context // context ∈
      occupiedLowerRankGateContexts F missing slot}) :
    Not (Concrete.HasSunflower k
      (gateContextSection F missing slot context)) := by
  cases slot with
  | none =>
      exact outsideSectionFactor_noSunflower F noSunflower
        (contextRepresentative F missing none context)
  | some petal =>
      exact petalSectionFactor_noSunflower F noSunflower
        (contextRepresentative F missing (some petal) context) petal

theorem outside_agrees_of_same_context
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (left right : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (sameContext : gateContextCode F missing none left =
      gateContextCode F missing none right) :
    OutsideContextAgrees F left right := by
  intro petal
  have sameFunctions := congrArg Prod.fst sameContext
  exact (congrFun sameFunctions petal).symm

theorem petal_agrees_of_same_context
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (left right : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (sameContext : gateContextCode F missing (some petal) left =
      gateContextCode F missing (some petal) right) :
    PetalContextAgrees F left petal right := by
  constructor
  · intro sibling sibling_ne
    have sameFunctions := congrArg Prod.fst sameContext
    have sameAtSibling := congrFun sameFunctions sibling
    simpa [gateContextCode, normalizeProductAtSlot,
      Function.update, sibling_ne] using sameAtSibling.symm
  · simpa [gateContextCode, normalizeProductAtSlot] using
      (congrArg Prod.snd sameContext).symm

theorem selectedComponent_mem_contextSection
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (context : {context // context ∈
      occupiedLowerRankGateContexts F missing slot})
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (edge_mem : edge ∈
      lowerRankGateContextFiber F missing slot context.val) :
    productComponentAt F (residualProductCode F edge) slot ∈
      (gateContextSection F missing slot context).edges := by
  have sameContext : gateContextCode F missing slot edge =
      gateContextCode F missing slot
        (contextRepresentative F missing slot context) := by
    calc
      gateContextCode F missing slot edge = context.val :=
        (Finset.mem_filter.mp edge_mem).2
      _ = gateContextCode F missing slot
          (contextRepresentative F missing slot context) :=
        (contextRepresentative_context F missing slot context).symm
  cases slot with
  | none =>
      apply (mem_outsideSectionComponents_iff F
        (contextRepresentative F missing none context) _).mpr
      exact ⟨edge,
        outside_agrees_of_same_context F missing
          (contextRepresentative F missing none context) edge sameContext.symm,
        rfl⟩
  | some petal =>
      apply (mem_petalSectionComponents_iff F
        (contextRepresentative F missing (some petal) context) petal _).mpr
      exact ⟨edge,
        petal_agrees_of_same_context F missing petal
          (contextRepresentative F missing (some petal) context) edge
          sameContext.symm,
        rfl⟩

theorem selectedComponent_injective_on_contextFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (context : ResidualComponentProduct F) :
    Set.InjOn
      (fun edge => productComponentAt F (residualProductCode F edge) slot)
      (lowerRankGateContextFiber F missing slot context) := by
  intro left left_mem right right_mem sameSelected
  apply edge_eq_of_same_context_and_component F missing slot left right
  · exact ((Finset.mem_filter.mp left_mem).2).trans
      ((Finset.mem_filter.mp right_mem).2).symm
  · exact sameSelected

theorem contextFiber_card_le_section
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (context : {context // context ∈
      occupiedLowerRankGateContexts F missing slot}) :
    (lowerRankGateContextFiber F missing slot context.val).card ≤
      (gateContextSection F missing slot context).edges.card := by
  classical
  let selected := fun edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges} =>
    productComponentAt F (residualProductCode F edge) slot
  calc
    (lowerRankGateContextFiber F missing slot context.val).card =
        ((lowerRankGateContextFiber F missing slot context.val).image selected).card := by
      symm
      apply Finset.card_image_iff.mpr
      exact selectedComponent_injective_on_contextFiber
        F missing slot context.val
    _ ≤ (gateContextSection F missing slot context).edges.card := by
      apply Finset.card_le_card
      intro component component_mem
      rcases Finset.mem_image.mp component_mem with ⟨edge, edge_mem, rfl⟩
      exact selectedComponent_mem_contextSection
        F missing slot context edge edge_mem

theorem lowerRankGateFiber_card_le_contexts_mul
    {alpha : Type}
    [DecidableEq alpha]
    {r M : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (sectionBound : ∀ context : {context // context ∈
      occupiedLowerRankGateContexts F missing slot},
      (gateContextSection F missing slot context).edges.card ≤ M) :
    (lowerRankGateDisagreementFiber F missing slot).card ≤
      (occupiedLowerRankGateContexts F missing slot).card * M := by
  rw [lowerRankGateFiber_card_eq_sum_contextFibers]
  calc
    ∑ context ∈ occupiedLowerRankGateContexts F missing slot,
        (lowerRankGateContextFiber F missing slot context).card ≤
        ∑ _context ∈ occupiedLowerRankGateContexts F missing slot, M := by
      apply Finset.sum_le_sum
      intro context context_mem
      exact (contextFiber_card_le_section F missing slot ⟨context, context_mem⟩).trans
        (sectionBound ⟨context, context_mem⟩)
    _ = (occupiedLowerRankGateContexts F missing slot).card * M := by simp

theorem lowerRankGateFiber_card_le_of_context_section_bounds
    {alpha : Type}
    [DecidableEq alpha]
    {r C M : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (contextBound :
      (occupiedLowerRankGateContexts F missing slot).card ≤ C)
    (sectionBound : ∀ context : {context // context ∈
      occupiedLowerRankGateContexts F missing slot},
      (gateContextSection F missing slot context).edges.card ≤ M) :
    (lowerRankGateDisagreementFiber F missing slot).card ≤ C * M := by
  exact (lowerRankGateFiber_card_le_contexts_mul
    F missing slot sectionBound).trans
      (Nat.mul_le_mul_right M contextBound)

theorem residualFamily_card_le_of_context_section_bounds
    {alpha : Type}
    [DecidableEq alpha]
    {r k C M : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (contextBound : ∀ slot : GateSlot F,
      (occupiedLowerRankGateContexts F missing slot).card ≤ C)
    (sectionBound : ∀ slot : GateSlot F,
      ∀ context : {context // context ∈
        occupiedLowerRankGateContexts F missing slot},
      (gateContextSection F missing slot context).edges.card ≤ M) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤
      k * (C * M + 1) := by
  apply residualFamily_card_le_of_lowerRankGateFiberBound
    F noSunflower missing
  intro slot
  exact lowerRankGateFiber_card_le_of_context_section_bounds
    F missing slot (contextBound slot) (sectionBound slot)

theorem minimalBlocker_card_le_of_context_section_bounds
    {alpha : Type}
    [DecidableEq alpha]
    {r k C M : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (contextBound : ∀ slot : GateSlot F,
      (occupiedLowerRankGateContexts F missing slot).card ≤ C)
    (sectionBound : ∀ slot : GateSlot F,
      ∀ context : {context // context ∈
        occupiedLowerRankGateContexts F missing slot},
      (gateContextSection F missing slot context).edges.card ≤ M) :
    (MinimalBlocker.minimalBlocker F).card ≤
      k * (k * (C * M + 1)) := by
  apply minimalBlocker_card_le_of_lowerRankGateFiberBound
    F noSunflower missing
  intro slot
  exact lowerRankGateFiber_card_le_of_context_section_bounds
    F missing slot (contextBound slot) (sectionBound slot)

end ResidualGateContextQuotient
end V2
end SunflowerAASC
