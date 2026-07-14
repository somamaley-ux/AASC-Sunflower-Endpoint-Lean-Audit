import SunflowerAASC.V2.EffectiveBlocker

namespace SunflowerAASC
namespace V2
namespace MinimalBlocker

/-- A subset of the canonical raw blocker that still hits every family edge. -/
def IsRawHittingBlocker
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (blocker : Finset alpha) : Prop :=
  blocker ⊆ EffectiveBlocker.canonicalRawBlocker F ∧
    ∀ edge : Finset alpha, edge ∈ F.edges -> Not (Disjoint edge blocker)

/-- The finite search space of hit-preserving subsets of the raw blocker. -/
noncomputable def rawHittingBlockers
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    Finset (Finset alpha) := by
  classical
  exact (EffectiveBlocker.canonicalRawBlocker F).powerset.filter
    (IsRawHittingBlocker F)

theorem canonicalRawBlocker_mem_rawHittingBlockers
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    EffectiveBlocker.canonicalRawBlocker F ∈ rawHittingBlockers F := by
  classical
  rw [rawHittingBlockers, Finset.mem_filter]
  refine ⟨Finset.mem_powerset.mpr (fun _ h => h), ?_⟩
  refine ⟨(fun _ h => h), ?_⟩
  intro edge edge_mem
  exact EffectiveBlocker.canonicalRawBlocker_hitsEveryEdge F edge_mem

theorem rawHittingBlockers_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    (rawHittingBlockers F).Nonempty :=
  ⟨EffectiveBlocker.canonicalRawBlocker F,
    canonicalRawBlocker_mem_rawHittingBlockers F⟩

/-- A cardinality-minimal hit-preserving subset of the canonical raw blocker. -/
noncomputable def minimalBlocker
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) : Finset alpha :=
  Classical.choose
    (Finset.exists_min_image
      (rawHittingBlockers F)
      Finset.card
      (rawHittingBlockers_nonempty F))

theorem minimalBlocker_mem
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    minimalBlocker F ∈ rawHittingBlockers F :=
  (Classical.choose_spec
    (Finset.exists_min_image
      (rawHittingBlockers F)
      Finset.card
      (rawHittingBlockers_nonempty F))).1

theorem minimalBlocker_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    {blocker : Finset alpha}
    (blocker_mem : blocker ∈ rawHittingBlockers F) :
    (minimalBlocker F).card <= blocker.card :=
  (Classical.choose_spec
    (Finset.exists_min_image
      (rawHittingBlockers F)
      Finset.card
      (rawHittingBlockers_nonempty F))).2 blocker blocker_mem

theorem minimalBlocker_isRawHittingBlocker
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    IsRawHittingBlocker F (minimalBlocker F) := by
  classical
  have blocker_mem := minimalBlocker_mem F
  rw [rawHittingBlockers, Finset.mem_filter] at blocker_mem
  exact blocker_mem.2

theorem minimalBlocker_subset_raw
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    minimalBlocker F ⊆ EffectiveBlocker.canonicalRawBlocker F :=
  (minimalBlocker_isRawHittingBlocker F).1

theorem minimalBlocker_hitsEveryEdge
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (edge : Finset alpha)
    (edge_mem : edge ∈ F.edges) :
    Not (Disjoint edge (minimalBlocker F)) :=
  (minimalBlocker_isRawHittingBlocker F).2 edge edge_mem

theorem erase_not_hitting
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ minimalBlocker F}) :
    Not (IsRawHittingBlocker F ((minimalBlocker F).erase x.val)) := by
  intro erase_hitting
  have erase_mem :
      (minimalBlocker F).erase x.val ∈ rawHittingBlockers F := by
    classical
    rw [rawHittingBlockers, Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr erase_hitting.1, erase_hitting⟩
  have card_ge := minimalBlocker_card_le F erase_mem
  have card_lt := Finset.card_erase_lt_of_mem x.property
  exact Nat.not_lt_of_ge card_ge card_lt

theorem exists_privateEdge
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ minimalBlocker F}) :
    ∃ edge : Finset alpha,
      edge ∈ F.edges ∧ Disjoint edge ((minimalBlocker F).erase x.val) := by
  have erase_subset_raw :
      (minimalBlocker F).erase x.val ⊆
        EffectiveBlocker.canonicalRawBlocker F :=
    fun _ y_mem =>
      minimalBlocker_subset_raw F (Finset.mem_of_mem_erase y_mem)
  have not_hits :
      Not (∀ edge : Finset alpha, edge ∈ F.edges ->
        Not (Disjoint edge ((minimalBlocker F).erase x.val))) := by
    intro hits
    exact erase_not_hitting F x ⟨erase_subset_raw, hits⟩
  push_neg at not_hits
  exact not_hits

/-- A private edge certifying that a minimal-blocker coordinate is indispensable. -/
noncomputable def privateEdge
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ minimalBlocker F}) : Finset alpha :=
  Classical.choose (exists_privateEdge F x)

theorem privateEdge_mem
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ minimalBlocker F}) :
    privateEdge F x ∈ F.edges :=
  (Classical.choose_spec (exists_privateEdge F x)).1

theorem privateEdge_disjoint_erase
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ minimalBlocker F}) :
    Disjoint (privateEdge F x) ((minimalBlocker F).erase x.val) :=
  (Classical.choose_spec (exists_privateEdge F x)).2

theorem privateEdge_contains
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ minimalBlocker F}) :
    x.val ∈ privateEdge F x := by
  rcases Finset.not_disjoint_iff.mp
      (minimalBlocker_hitsEveryEdge F (privateEdge F x)
        (privateEdge_mem F x)) with ⟨y, y_edge, y_blocker⟩
  have y_eq : y = x.val := by
    by_contra y_ne_x
    have y_erase : y ∈ (minimalBlocker F).erase x.val :=
      Finset.mem_erase.mpr ⟨y_ne_x, y_blocker⟩
    exact Finset.disjoint_left.mp (privateEdge_disjoint_erase F x)
      y_edge y_erase
  simpa [← y_eq] using y_edge

theorem privateEdge_inter_minimalBlocker
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ minimalBlocker F}) :
    privateEdge F x ∩ minimalBlocker F = {x.val} := by
  apply Finset.ext
  intro y
  constructor
  · intro y_mem
    rcases Finset.mem_inter.mp y_mem with ⟨y_edge, y_blocker⟩
    have y_eq : y = x.val := by
      by_contra y_ne
      have y_erase : y ∈ (minimalBlocker F).erase x.val :=
        Finset.mem_erase.mpr ⟨y_ne, y_blocker⟩
      exact Finset.disjoint_left.mp (privateEdge_disjoint_erase F x)
        y_edge y_erase
    simp [y_eq]
  · intro y_mem
    have y_eq : y = x.val := Finset.mem_singleton.mp y_mem
    subst y
    exact Finset.mem_inter.mpr ⟨privateEdge_contains F x, x.property⟩

theorem privateEdge_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    Function.Injective (privateEdge F) := by
  intro left right sameEdge
  apply Subtype.ext
  have sameIntersection := congrArg (fun edge => edge ∩ minimalBlocker F) sameEdge
  change privateEdge F left ∩ minimalBlocker F =
    privateEdge F right ∩ minimalBlocker F at sameIntersection
  rw [privateEdge_inter_minimalBlocker F left,
    privateEdge_inter_minimalBlocker F right] at sameIntersection
  exact Finset.singleton_inj.mp sameIntersection

theorem mem_privateEdge_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ minimalBlocker F}) :
    right.val ∈ privateEdge F left <-> right = left := by
  constructor
  · intro right_mem
    apply Subtype.ext
    have right_mem_inter :
        right.val ∈ privateEdge F left ∩ minimalBlocker F :=
      Finset.mem_inter.mpr ⟨right_mem, right.property⟩
    rw [privateEdge_inter_minimalBlocker F left] at right_mem_inter
    exact Finset.mem_singleton.mp right_mem_inter
  · intro right_eq
    subst right
    exact privateEdge_contains F left

/-- Every distinct minimal-blocker pair is separated by one concrete edge. -/
theorem exists_one_edge_witness
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ minimalBlocker F})
    (distinct : left ≠ right) :
    ∃ edge : Finset alpha,
      edge ∈ F.edges ∧ left.val ∈ edge ∧ right.val ∉ edge := by
  exact ⟨privateEdge F left, privateEdge_mem F left,
    privateEdge_contains F left,
    fun right_mem => distinct <|
      ((mem_privateEdge_iff F left right).mp right_mem).symm⟩

/-- The canonical subfamily of private witness edges. -/
noncomputable def privateWitnessFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    Concrete.UniformSetFamily alpha (r + 1) where
  edges := (minimalBlocker F).attach.image (privateEdge F)
  uniform := by
    intro edge edge_mem
    rcases Finset.mem_image.mp edge_mem with ⟨x, _, rfl⟩
    exact F.uniform (privateEdge F x) (privateEdge_mem F x)

theorem privateWitnessFamily_edges_subset
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    (privateWitnessFamily F).edges ⊆ F.edges := by
  intro edge edge_mem
  rcases Finset.mem_image.mp edge_mem with ⟨x, _, rfl⟩
  exact privateEdge_mem F x

theorem privateWitnessFamily_card
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    (privateWitnessFamily F).edges.card = (minimalBlocker F).card := by
  rw [privateWitnessFamily, Finset.card_image_of_injective]
  · simp
  · exact privateEdge_injective F

theorem privateWitnessFamily_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Not (Concrete.HasSunflower k (privateWitnessFamily F)) := by
  intro hasPrivateSunflower
  rcases hasPrivateSunflower with ⟨core, ⟨W⟩⟩
  exact noSunflower ⟨core, ⟨{
    petals := W.petals
    petals_mem := fun i =>
      privateWitnessFamily_edges_subset F (W.petals_mem i)
    petals_injective := W.petals_injective
    pairwise_intersection := W.pairwise_intersection }⟩⟩

/-- Two blocker coordinates have the same fixed-endpoint incidence profile. -/
def SameEndpointIncidence
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ minimalBlocker F}) : Prop :=
  ∀ edge : Finset alpha, edge ∈ F.edges ->
    (left.val ∈ edge <-> right.val ∈ edge)

/-- An endpoint-local probe is one realized edge of the fixed family. -/
abbrev EndpointIncidenceProbe
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :=
  {edge : Finset alpha // edge ∈ F.edges}

/-- The response of one blocker coordinate to a realized endpoint probe. -/
def endpointProbeResponse
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ minimalBlocker F})
    (probe : EndpointIncidenceProbe F) : Prop :=
  x.val ∈ probe.val

/--
Endpoint skin has no incidence power: skin-equivalent representatives answer
every realized endpoint probe identically.
-/
def EndpointSkinEquivalent
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ minimalBlocker F}) : Prop :=
  ∀ probe : EndpointIncidenceProbe F,
    endpointProbeResponse F left probe <->
      endpointProbeResponse F right probe

/-- A private witness carrying an oriented, realized endpoint-incidence load. -/
structure PrivateWitnessEndpointLoad
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ minimalBlocker F}) where
  probe : EndpointIncidenceProbe F
  leftPositive : endpointProbeResponse F left probe
  rightNegative : Not (endpointProbeResponse F right probe)

/-- Distinct private witnesses carry a concrete endpoint load. -/
noncomputable def privateWitnessEndpointLoadOfDistinct
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ minimalBlocker F})
    (distinct : left ≠ right) :
    PrivateWitnessEndpointLoad F left right where
  probe := ⟨privateEdge F left, privateEdge_mem F left⟩
  leftPositive := privateEdge_contains F left
  rightNegative := fun right_mem => distinct <|
    ((mem_privateEdge_iff F left right).mp right_mem).symm

theorem endpointSkinEquivalent_iff_sameEndpointIncidence
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ minimalBlocker F}) :
    EndpointSkinEquivalent F left right <->
      SameEndpointIncidence F left right := by
  constructor
  · intro skin edge edge_mem
    exact skin ⟨edge, edge_mem⟩
  · intro sameIncidence probe
    exact sameIncidence probe.val probe.property

/-- Realized private-witness load cannot be carried by endpoint skin. -/
theorem PrivateWitnessEndpointLoad.not_endpointSkin
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {left right : {x // x ∈ minimalBlocker F}}
    (load : PrivateWitnessEndpointLoad F left right) :
    Not (EndpointSkinEquivalent F left right) := by
  intro skin
  exact load.rightNegative ((skin load.probe).mp load.leftPositive)

theorem PrivateWitnessEndpointLoad.not_sameEndpointIncidence
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {left right : {x // x ∈ minimalBlocker F}}
    (load : PrivateWitnessEndpointLoad F left right) :
    Not (SameEndpointIncidence F left right) := by
  intro sameIncidence
  exact load.not_endpointSkin <|
    (endpointSkinEquivalent_iff_sameEndpointIncidence F left right).mpr
      sameIncidence

/-- Every distinct pair is unconditionally outside the endpoint-skin branch. -/
theorem distinct_privateWitness_not_endpointSkin
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ minimalBlocker F})
    (distinct : left ≠ right) :
    Not (EndpointSkinEquivalent F left right) :=
  (privateWitnessEndpointLoadOfDistinct F left right distinct).not_endpointSkin

/-- The complete global standing profile over every edge at the endpoint. -/
def globalEndpointIncidenceProfile
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ minimalBlocker F}) :
    {edge // edge ∈ F.edges} -> Prop :=
  fun edge => x.val ∈ edge.val

theorem eq_of_sameEndpointIncidence
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ minimalBlocker F})
    (sameIncidence : SameEndpointIncidence F left right) :
    left = right := by
  apply Subtype.ext
  have right_mem_private : right.val ∈ privateEdge F left :=
    (sameIncidence (privateEdge F left) (privateEdge_mem F left)).mp
      (privateEdge_contains F left)
  have right_mem_inter :
      right.val ∈ privateEdge F left ∩ minimalBlocker F :=
    Finset.mem_inter.mpr ⟨right_mem_private, right.property⟩
  rw [privateEdge_inter_minimalBlocker F left] at right_mem_inter
  exact (Finset.mem_singleton.mp right_mem_inter).symm

/-- Endpoint skin is representative-only on the minimal private-witness carrier. -/
theorem eq_of_endpointSkinEquivalent
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ minimalBlocker F})
    (skin : EndpointSkinEquivalent F left right) :
    left = right :=
  eq_of_sameEndpointIncidence F left right <|
    (endpointSkinEquivalent_iff_sameEndpointIncidence F left right).mp skin

theorem endpointSkinEquivalent_iff_eq
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ minimalBlocker F}) :
    EndpointSkinEquivalent F left right <-> left = right := by
  constructor
  · exact eq_of_endpointSkinEquivalent F left right
  · intro same
    subst right
    intro probe
    exact Iff.rfl

/--
Exact no-power characterization: endpoint skin is precisely the absence of a
realized private-witness load.
-/
theorem endpointSkinEquivalent_iff_no_privateWitnessLoad
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ minimalBlocker F}) :
    EndpointSkinEquivalent F left right <->
      Not (Nonempty (PrivateWitnessEndpointLoad F left right)) := by
  constructor
  · intro skin load
    exact load.some.not_endpointSkin skin
  · intro noLoad
    apply (endpointSkinEquivalent_iff_eq F left right).mpr
    apply Classical.byContradiction
    intro distinct
    exact noLoad ⟨privateWitnessEndpointLoadOfDistinct
      F left right distinct⟩

theorem globalEndpointIncidenceProfile_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    Function.Injective (globalEndpointIncidenceProfile F) := by
  intro left right sameProfile
  apply eq_of_sameEndpointIncidence F left right
  intro edge edge_mem
  exact iff_of_eq <| congrFun sameProfile ⟨edge, edge_mem⟩

end MinimalBlocker
end V2
end SunflowerAASC
