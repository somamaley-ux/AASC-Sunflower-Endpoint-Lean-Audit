import SunflowerAASC.V2.FixedCellRoleLocusExclusion

namespace SunflowerAASC
namespace V2
namespace CompleteRoleRefinement

open GeneratedIncidenceTower
open GeneratedSeedCapacity
open ReachableRoleOccupancy
open KernelRoleOccupancyAdapter
open FixedCellStandingClosure
open FixedCellRoleLocusExclusion

/-- The complete endpoint role of a minimal-blocker coordinate. -/
abbrev CompleteEndpointRole
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :=
  {edge // edge ∈ F.edges} -> Prop

def completeEndpointRole
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    CompleteEndpointRole F :=
  MinimalBlocker.globalEndpointIncidenceProfile F source

/-- Complete endpoint roles retain literal private-witness identity. -/
theorem completeEndpointRole_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    Function.Injective (completeEndpointRole F) := by
  exact MinimalBlocker.globalEndpointIncidenceProfile_injective F

/-- A tensor-active endpoint distinction changes the complete incidence role. -/
def EndpointTensorActive
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Prop :=
  completeEndpointRole F left ≠ completeEndpointRole F right

/-- On a minimal private-witness carrier, tensor activity is raw distinction. -/
theorem endpointTensorActive_iff_distinct
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    EndpointTensorActive F left right ↔ left ≠ right := by
  constructor
  · intro active same
    subst right
    exact active rfl
  · intro distinct sameRole
    exact distinct (completeEndpointRole_injective F sameRole)

/-- Skin and complete tensor distinction are exact complements here. -/
theorem endpointTensorActive_iff_not_endpointSkin
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    EndpointTensorActive F left right ↔
      Not (MinimalBlocker.EndpointSkinEquivalent F left right) := by
  rw [endpointTensorActive_iff_distinct,
    MinimalBlocker.endpointSkinEquivalent_iff_eq]

/-- Every realized private-witness load changes complete tensor content. -/
theorem endpointTensorActive_of_privateWitnessLoad
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (load : MinimalBlocker.PrivateWitnessEndpointLoad F left right) :
    EndpointTensorActive F left right := by
  exact (endpointTensorActive_iff_not_endpointSkin F left right).mpr
    load.not_endpointSkin

/-- A code is complete exactly when equal codes preserve the full role. -/
def CompleteRoleReflectingCode
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    {Code : Type}
    (code : {x // x ∈ MinimalBlocker.minimalBlocker F} -> Code) : Prop :=
  ∀ left right, code left = code right ->
    completeEndpointRole F left = completeEndpointRole F right

/--
Because the complete endpoint role is already identity-faithful, reflecting it
is equivalent to injectivity of the proposed code. This prevents a coarse code
from being called complete without proving the missing cardinality statement.
-/
theorem completeRoleReflectingCode_iff_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    {Code : Type}
    (code : {x // x ∈ MinimalBlocker.minimalBlocker F} -> Code) :
    CompleteRoleReflectingCode F code ↔ Function.Injective code := by
  constructor
  · intro reflects left right sameCode
    exact completeEndpointRole_injective F
      (reflects left right sameCode)
  · intro injective left right sameCode
    rw [injective sameCode]

/-- Changing the rank-lowered residual parent is genuine tensor content. -/
def ResidualParentTensorDistinction
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Prop :=
  PrivateWitnessReduction.residual F left ≠
    PrivateWitnessReduction.residual F right

/-- Inside one residual parent, distinction is carried by a derived `Fin k` slot. -/
def BoundedFiberSlotDistinction
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Prop :=
  PrivateWitnessReduction.residual F left =
      PrivateWitnessReduction.residual F right ∧
    PrivateWitnessReduction.residualFiberSlot F noSunflower left ≠
      PrivateWitnessReduction.residualFiberSlot F noSunflower right

/--
Exact local role exhaustion for distinct private witnesses. There is no skin
or independent-authorizer branch: the distinction is either a different
rank-lowered tensor parent or a different slot in one bounded residual fiber.
-/
theorem distinct_exhausts_into_parentTensor_or_boundedFiberSlot
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (distinct : left ≠ right) :
    ResidualParentTensorDistinction F left right ∨
      BoundedFiberSlotDistinction F noSunflower left right := by
  by_cases sameParent :
      PrivateWitnessReduction.residual F left =
        PrivateWitnessReduction.residual F right
  · apply Or.inr
    exact ⟨sameParent,
      PrivateWitnessReduction.residualFiberSlot_ne_of_sameResidual_of_nonSkin
        F noSunflower left right sameParent
        (MinimalBlocker.distinct_privateWitness_not_endpointSkin
          F left right distinct)⟩
  · exact Or.inl sameParent

/-- Same residual parent and same bounded slot are already raw exactness. -/
theorem sameResidualAndSlot_iff_eq
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (PrivateWitnessReduction.residual F left =
        PrivateWitnessReduction.residual F right ∧
      PrivateWitnessReduction.residualFiberSlot F noSunflower left =
        PrivateWitnessReduction.residualFiberSlot F noSunflower right) ↔
      left = right := by
  constructor
  · rintro ⟨sameResidual, sameSlot⟩
    exact PrivateWitnessReduction.eq_of_same_residual_same_fiberSlot
      F noSunflower left right sameResidual sameSlot
  · intro same
    subst right
    exact ⟨rfl, rfl⟩

/-- The concrete residual-parent/slot code reflects the complete role. -/
theorem residualSlotCode_completeRoleReflecting
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    CompleteRoleReflectingCode F
      (PrivateWitnessReduction.residualSlotCode F noSunflower) := by
  exact (completeRoleReflectingCode_iff_injective F
    (PrivateWitnessReduction.residualSlotCode F noSunflower)).mpr
      (PrivateWitnessReduction.residualSlotCode_injective F noSunflower)

/--
Relation-wide terminal reference preservation. This is the precise semantic
content needed to turn one literal terminal locus into one source identity.
-/
def SharedTerminalLocusPreservesCompleteRole
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F)) : Prop :=
  ∀ (left right : CellSource cell) (locus : TerminalCarrier F),
    ReachesTerminalCarrier left.coordinate locus ->
    ReachesTerminalCarrier right.coordinate locus ->
    sourceReference F cell left = sourceReference F cell right

/--
For private-witness sources, relation-wide reference preservation is exactly
the strong role-locus exclusion law. Kernel-role possession alone does not
weaken this equivalence.
-/
theorem sharedTerminalLocusPreservesCompleteRole_iff_exclusion
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F)) :
    SharedTerminalLocusPreservesCompleteRole F cell ↔
      CompleteRoleLocusExclusion F cell := by
  constructor
  · intro preserves left right locus leftReach rightReach
    exact sourceReference_injective F cell
      (preserves left right locus leftReach rightReach)
  · intro exclusion left right locus leftReach rightReach
    have sameSource : left = right :=
      exclusion left right locus leftReach rightReach
    subst right
    rfl

/-- Reference preservation for the generated selected terminal carrier. -/
def SelectedTerminalLocusPreservesCompleteRole
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F)) : Prop :=
  ∀ left right : CellSource cell,
    cellCarrierOf F cell left = cellCarrierOf F cell right ->
      sourceReference F cell left = sourceReference F cell right

/-- Selected reference preservation is exactly injectivity of that selection. -/
theorem selectedTerminalLocusPreservesCompleteRole_iff_injective
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F)) :
    SelectedTerminalLocusPreservesCompleteRole F cell ↔
      Function.Injective (cellCarrierOf F cell) := by
  constructor
  · intro preserves left right sameLocus
    exact sourceReference_injective F cell
      (preserves left right sameLocus)
  · intro injective left right sameLocus
    rw [injective sameLocus]

/-- A selected complete-reference transport supplies the generated Hall bridge. -/
theorem reachableRoleHall_of_selectedCompleteRolePreservation
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (preserves : SelectedTerminalLocusPreservesCompleteRole F cell) :
    ReachableRoleHall F cell := by
  apply reachableRoleHall_iff_exists_injective_selector.mpr
  exact ⟨cellCarrierOf F cell,
    (selectedTerminalLocusPreservesCompleteRole_iff_injective F cell).mp
      preserves,
    cellCarrierOf_reachable F cell⟩

end CompleteRoleRefinement
end V2
end SunflowerAASC
