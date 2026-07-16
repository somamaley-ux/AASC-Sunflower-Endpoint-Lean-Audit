import SunflowerAASC.V2.CompleteRoleRefinement

namespace SunflowerAASC
namespace V2
namespace QuotientCoverageRigidity

/--
A proposed terminal quotient on minimal-blocker coordinates is coverage
respecting when related coordinates answer every realized edge-incidence probe
the same way.  This is the minimum condition needed for blocker coverage to
descend to the quotient.
-/
structure CoverageRespectingSetoid
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) where
  setoid : Setoid {x // x ∈ MinimalBlocker.minimalBlocker F}
  coverage_preserving : ∀ left right,
    setoid.r left right →
      MinimalBlocker.SameEndpointIncidence F left right

/--
Private-edge minimality makes every coverage-respecting terminal relation
literal equality on source coordinates.  Such a quotient may remove duplicate
paths attached to one source, but it cannot identify two distinct sources.
-/
theorem CoverageRespectingSetoid.rel_iff_eq
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (S : CoverageRespectingSetoid F)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    S.setoid.r left right ↔ left = right := by
  constructor
  · intro related
    exact MinimalBlocker.eq_of_sameEndpointIncidence F left right
      (S.coverage_preserving left right related)
  · intro same
    subst right
    exact S.setoid.refl left

/-- The quotient map induced by a coverage-respecting relation is injective. -/
theorem CoverageRespectingSetoid.quotientMk_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (S : CoverageRespectingSetoid F) :
    Function.Injective (Quotient.mk S.setoid) := by
  intro left right sameClass
  exact (S.rel_iff_eq left right).mp (Quotient.exact sameClass)

/--
An undischarged source-level bridge applies a coverage-preserving quotient
before bounded, split, sunflower, and lower-rank dispositions have been
resolved.  It does not assume injectivity on raw path histories, but it still
retains every original minimal-blocker source as live endpoint load.
-/
structure UndischargedCoverageCarrierBridge
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (Coordinate : Type) where
  carrierRelation : CoverageRespectingSetoid F
  coordinate : Quotient carrierRelation.setoid -> Coordinate
  coordinate_injective : Function.Injective coordinate

/-- Read the terminal coordinate of an undischarged source through the quotient. -/
def UndischargedCoverageCarrierBridge.sourceCoordinate
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {Coordinate : Type}
    (bridge : UndischargedCoverageCarrierBridge F Coordinate) :
    {x // x ∈ MinimalBlocker.minimalBlocker F} -> Coordinate :=
  fun source => bridge.coordinate
    (Quotient.mk bridge.carrierRelation.setoid source)

/--
Coverage faithfulness makes the quotient map injective on distinct
minimal-blocker sources.  Duplicate histories over one source may still be
identified; distinct private-edge coverage profiles may not.
-/
theorem UndischargedCoverageCarrierBridge.sourceCoordinate_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {Coordinate : Type}
    (bridge : UndischargedCoverageCarrierBridge F Coordinate) :
    Function.Injective bridge.sourceCoordinate := by
  intro left right sameCoordinate
  apply bridge.carrierRelation.quotientMk_injective
  exact bridge.coordinate_injective sameCoordinate

/-- Every undischarged coverage bridge obeys the raw source-coordinate Hall bound. -/
theorem UndischargedCoverageCarrierBridge.source_card_le_coordinate
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {Coordinate : Type}
    [Fintype Coordinate]
    (bridge : UndischargedCoverageCarrierBridge F Coordinate) :
    Fintype.card {x // x ∈ MinimalBlocker.minimalBlocker F} <=
      Fintype.card Coordinate :=
  Fintype.card_le_of_injective bridge.sourceCoordinate
    bridge.sourceCoordinate_injective

/-- One blocker coordinate subsumes another when it hits every edge hit by it. -/
def EndpointCoverageSubsumes
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (representative source :
      {x // x ∈ MinimalBlocker.minimalBlocker F}) : Prop :=
  ∀ edge : Finset alpha, edge ∈ F.edges →
    source.val ∈ edge → representative.val ∈ edge

/--
Minimal-blocker coverage profiles form an antichain: one source can realize all
coverage carried by another source only when the two sources are equal.  Thus
the proposed one-representative coverage number is one only after source
uniqueness has already been established or all other sources have been
structurally discharged.
-/
theorem endpointCoverageSubsumes_iff_eq
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (representative source :
      {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    EndpointCoverageSubsumes F representative source ↔
      representative = source := by
  constructor
  · intro subsumes
    exact (MinimalBlocker.mem_privateEdge_iff F source representative).mp
      (subsumes (MinimalBlocker.privateEdge F source)
        (MinimalBlocker.privateEdge_mem F source)
        (MinimalBlocker.privateEdge_contains F source))
  · intro same
    subst representative
    intro edge _edge_mem source_mem
    exact source_mem

/--
An actual blocker chosen from the cardinality-minimal blocker cannot discard
any coordinate.  The private edge of every omitted coordinate would become
uncovered.
-/
theorem representativeBlocker_eq_minimalBlocker
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (representatives : Finset alpha)
    (representatives_subset :
      representatives ⊆ MinimalBlocker.minimalBlocker F)
    (hitsEveryEdge : ∀ edge : Finset alpha, edge ∈ F.edges →
      Not (Disjoint edge representatives)) :
    representatives = MinimalBlocker.minimalBlocker F := by
  apply Finset.Subset.antisymm representatives_subset
  intro point point_mem
  by_contra point_not_mem
  let source : {x // x ∈ MinimalBlocker.minimalBlocker F} :=
    ⟨point, point_mem⟩
  have representatives_subset_erase :
      representatives ⊆
        (MinimalBlocker.minimalBlocker F).erase point := by
    intro other other_mem
    apply Finset.mem_erase.mpr
    refine ⟨?_, representatives_subset other_mem⟩
    intro other_eq
    subst other
    exact point_not_mem other_mem
  have privateEdge_disjoint :
      Disjoint (MinimalBlocker.privateEdge F source) representatives :=
    (MinimalBlocker.privateEdge_disjoint_erase F source).mono_right
      representatives_subset_erase
  exact (hitsEveryEdge
    (MinimalBlocker.privateEdge F source)
    (MinimalBlocker.privateEdge_mem F source)) privateEdge_disjoint

/--
Consequently a strict representative subset of the minimal blocker cannot be
an actual hitting set for the original family.
-/
theorem strictRepresentativeSubset_not_hitting
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (representatives : Finset alpha)
    (representatives_subset :
      representatives ⊆ MinimalBlocker.minimalBlocker F)
    (strict : representatives ≠ MinimalBlocker.minimalBlocker F) :
    Not (∀ edge : Finset alpha, edge ∈ F.edges →
      Not (Disjoint edge representatives)) := by
  intro hitsEveryEdge
  exact strict (representativeBlocker_eq_minimalBlocker
    F representatives representatives_subset hitsEveryEdge)

end QuotientCoverageRigidity
end V2
end SunflowerAASC
