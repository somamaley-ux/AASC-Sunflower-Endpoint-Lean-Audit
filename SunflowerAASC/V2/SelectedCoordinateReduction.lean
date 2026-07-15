import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import SunflowerAASC.V2.ConcreteCarrier

namespace SunflowerAASC
namespace V2
namespace SelectedCoordinateReduction

/-- Every positive-rank edge supplies a coordinate without extra population data. -/
theorem edge_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (edge : {edge // edge ∈ F.edges}) : edge.val.Nonempty := by
  apply Finset.card_pos.mp
  rw [F.uniform edge.val edge.property]
  omega

/-- A generated deletion coordinate for each edge. -/
noncomputable def chosenCoordinate
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (edge : {edge // edge ∈ F.edges}) : alpha :=
  Classical.choose (edge_nonempty F edge)

theorem chosenCoordinate_mem
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (edge : {edge // edge ∈ F.edges}) :
    chosenCoordinate F edge ∈ edge.val :=
  Classical.choose_spec (edge_nonempty F edge)

/-- Delete the generated coordinate from an original edge. -/
noncomputable def residual
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (edge : {edge // edge ∈ F.edges}) : Finset alpha :=
  edge.val.erase (chosenCoordinate F edge)

theorem residual_card
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (edge : {edge // edge ∈ F.edges}) :
    (residual F edge).card = r := by
  rw [residual, Finset.card_erase_of_mem (chosenCoordinate_mem F edge)]
  rw [F.uniform edge.val edge.property]
  simp

theorem edge_eq_insert_residual
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (edge : {edge // edge ∈ F.edges}) :
    edge.val = insert (chosenCoordinate F edge) (residual F edge) := by
  exact (Finset.insert_erase (chosenCoordinate_mem F edge)).symm

theorem chosenCoordinate_not_mem_residual
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (edge : {edge // edge ∈ F.edges}) :
    chosenCoordinate F edge ∉ residual F edge := by
  simp [residual]

/-- All distinct residuals produced by deleting one generated coordinate. -/
noncomputable def residualFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    Concrete.UniformSetFamily alpha r where
  edges := F.edges.attach.image (residual F)
  uniform := by
    intro edge edge_mem
    rcases Finset.mem_image.mp edge_mem with ⟨source, _, rfl⟩
    exact residual_card F source

theorem mem_residualFamily_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {edge : Finset alpha} :
    edge ∈ (residualFamily F).edges <->
      ∃ source : {edge // edge ∈ F.edges}, residual F source = edge := by
  constructor
  · intro edge_mem
    rcases Finset.mem_image.mp edge_mem with ⟨source, _, same⟩
    exact ⟨source, same⟩
  · rintro ⟨source, rfl⟩
    exact Finset.mem_image.mpr ⟨source, Finset.mem_attach _ _, rfl⟩

/-- Original edges producing one fixed residual. -/
noncomputable def residualFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (edge : Finset alpha) :
    Finset {source // source ∈ F.edges} := by
  classical
  exact F.edges.attach.filter (fun source => residual F source = edge)

theorem mem_residualFiber_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {edge : Finset alpha}
    {source : {source // source ∈ F.edges}} :
    source ∈ residualFiber F edge <-> residual F source = edge := by
  classical
  simp [residualFiber]

theorem intersection_eq_residual_of_same_residual
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {edge // edge ∈ F.edges})
    (distinct : left ≠ right)
    (sameResidual : residual F left = residual F right) :
    left.val ∩ right.val = residual F left := by
  have coordinate_ne : chosenCoordinate F left ≠ chosenCoordinate F right := by
    intro sameCoordinate
    apply distinct
    apply Subtype.ext
    rw [edge_eq_insert_residual F left, edge_eq_insert_residual F right,
      sameResidual, sameCoordinate]
  rw [edge_eq_insert_residual F left, edge_eq_insert_residual F right,
    sameResidual]
  apply Finset.ext
  intro x
  constructor
  · intro x_mem
    rcases Finset.mem_inter.mp x_mem with ⟨x_left, x_right⟩
    rcases Finset.mem_insert.mp x_left with x_eq_left | x_residual
    · subst x
      rcases Finset.mem_insert.mp x_right with sameCoordinate | x_residual
      · exact False.elim (coordinate_ne sameCoordinate)
      · rw [← sameResidual] at x_residual
        exact False.elim
          (chosenCoordinate_not_mem_residual F left x_residual)
    · exact x_residual
  · intro x_residual
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_insert.mpr (Or.inr x_residual),
        Finset.mem_insert.mpr (Or.inr x_residual)⟩

theorem hasSunflower_of_residualFiber_card_ge
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (edge : Finset alpha)
    (fiberLarge : k <= (residualFiber F edge).card) :
    Concrete.HasSunflower k F := by
  classical
  obtain ⟨chosen, chosen_subset, chosen_card⟩ :=
    Finset.exists_subset_card_eq fiberLarge
  let enumerate : {source // source ∈ chosen} ≃ Fin k :=
    Fintype.equivFinOfCardEq (by simp [chosen_card])
  let source : Fin k -> {edge // edge ∈ F.edges} :=
    fun i => (enumerate.symm i).val
  have source_mem : ∀ i : Fin k, source i ∈ residualFiber F edge := by
    intro i
    exact chosen_subset (enumerate.symm i).property
  have source_residual : ∀ i : Fin k, residual F (source i) = edge := by
    intro i
    exact mem_residualFiber_iff.mp (source_mem i)
  have source_injective : Function.Injective source := by
    intro i j same
    have nested_same : enumerate.symm i = enumerate.symm j := by
      apply Subtype.ext
      exact same
    exact enumerate.symm.injective nested_same
  refine ⟨edge, ⟨{
    petals := fun i => (source i).val
    petals_mem := fun i => (source i).property
    petals_injective := by
      intro i j sameEdge
      apply source_injective
      exact Subtype.ext sameEdge
    pairwise_intersection := ?_ }⟩⟩
  intro i j distinct
  exact (intersection_eq_residual_of_same_residual F (source i) (source j)
    (fun same => distinct (source_injective same))
    ((source_residual i).trans (source_residual j).symm)).trans
      (source_residual i)

theorem residualFiber_card_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (edge : Finset alpha) :
    (residualFiber F edge).card < k := by
  exact Nat.lt_of_not_ge fun fiberLarge =>
    noSunflower (hasSunflower_of_residualFiber_card_ge F edge fiberLarge)

/-- The whole original family is bounded by `k` times its residual image. -/
theorem family_card_le_k_mul_residualFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    F.edges.card <= k * (residualFamily F).edges.card := by
  classical
  have bound := Finset.card_le_mul_card_image
    (f := residual F)
    F.edges.attach
    k
    (fun edge edge_mem => by
      have fiber_lt := residualFiber_card_lt F noSunflower edge
      have fiber_le : (residualFiber F edge).card <= k :=
        Nat.le_of_lt fiber_lt
      simpa [residualFiber] using fiber_le)
  simpa [residualFamily] using bound

/--
An outgoing cross is literal Venn interference: the coordinate deleted from
one original edge still occurs in a different original edge.
-/
def HasOutgoingCross
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) : Prop :=
  ∃ left right : {edge // edge ∈ F.edges},
    left ≠ right ∧ chosenCoordinate F left ∈ right.val

/-- A cross is either a shared deletion coordinate or entry into the residual. -/
theorem hasOutgoingCross_iff_sharedCoordinate_or_residualCross
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    HasOutgoingCross F <->
      ∃ left right : {edge // edge ∈ F.edges},
        left ≠ right ∧
          (chosenCoordinate F left = chosenCoordinate F right ∨
            chosenCoordinate F left ∈ residual F right) := by
  constructor
  · rintro ⟨left, right, distinct, cross⟩
    rw [edge_eq_insert_residual F right] at cross
    exact ⟨left, right, distinct, Finset.mem_insert.mp cross⟩
  · rintro ⟨left, right, distinct, sharedOrResidual⟩
    refine ⟨left, right, distinct, ?_⟩
    rw [edge_eq_insert_residual F right]
    exact Finset.mem_insert.mpr sharedOrResidual

theorem intersection_eq_residual_inter_of_no_cross
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {edge // edge ∈ F.edges})
    (left_not_right : chosenCoordinate F left ∉ right.val)
    (right_not_left : chosenCoordinate F right ∉ left.val) :
    left.val ∩ right.val = residual F left ∩ residual F right := by
  apply Finset.ext
  intro x
  constructor
  · intro x_mem
    rcases Finset.mem_inter.mp x_mem with ⟨x_left, x_right⟩
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_erase.mpr
      exact ⟨fun x_eq => left_not_right (x_eq ▸ x_right), x_left⟩
    · apply Finset.mem_erase.mpr
      exact ⟨fun x_eq => right_not_left (x_eq ▸ x_left), x_right⟩
  · intro x_mem
    rcases Finset.mem_inter.mp x_mem with ⟨x_left, x_right⟩
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_of_mem_erase x_left, Finset.mem_of_mem_erase x_right⟩

/-- The generated original-edge preimage of one residual sunflower petal. -/
noncomputable def witnessSource
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core)
    (i : Fin k) : {edge // edge ∈ F.edges} :=
  Classical.choose (mem_residualFamily_iff.mp (W.petals_mem i))

theorem witnessSource_spec
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core)
    (i : Fin k) :
    residual F (witnessSource W i) = W.petals i :=
  Classical.choose_spec (mem_residualFamily_iff.mp (W.petals_mem i))

theorem witnessSource_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core) :
    Function.Injective (witnessSource W) := by
  intro i j sameSource
  apply W.petals_injective
  rw [← witnessSource_spec W i, ← witnessSource_spec W j, sameSource]

/--
The witness-local obstruction: a deleted coordinate from one lifted petal
occurs in another lifted petal of this same residual sunflower.
-/
noncomputable def ResidualLiftInterference
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core) : Prop :=
  ∃ i j : Fin k, i ≠ j ∧
    chosenCoordinate F (witnessSource W i) ∈ (witnessSource W j).val

/-- The generated finite Venn profile of all witness-local outgoing crosses. -/
noncomputable def residualLiftCrossProfile
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core) :
    Finset (Fin k × Fin k) := by
  classical
  exact Finset.univ.filter (fun pair =>
    pair.1 ≠ pair.2 ∧
      chosenCoordinate F (witnessSource W pair.1) ∈
        (witnessSource W pair.2).val)

theorem mem_residualLiftCrossProfile_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    {W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core}
    {pair : Fin k × Fin k} :
    pair ∈ residualLiftCrossProfile W <->
      pair.1 ≠ pair.2 ∧
        chosenCoordinate F (witnessSource W pair.1) ∈
          (witnessSource W pair.2).val := by
  classical
  simp [residualLiftCrossProfile]

theorem residualLiftInterference_iff_crossProfile_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core) :
    ResidualLiftInterference W <-> (residualLiftCrossProfile W).Nonempty := by
  constructor
  · rintro ⟨i, j, distinct, cross⟩
    exact ⟨(i, j), mem_residualLiftCrossProfile_iff.mpr
      ⟨distinct, cross⟩⟩
  · rintro ⟨pair, pair_mem⟩
    exact ⟨pair.1, pair.2,
      (mem_residualLiftCrossProfile_iff.mp pair_mem).1,
      (mem_residualLiftCrossProfile_iff.mp pair_mem).2⟩

theorem residualLiftCrossProfile_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core) :
    (residualLiftCrossProfile W).card <= k * k := by
  classical
  calc
    (residualLiftCrossProfile W).card <=
        (Finset.univ : Finset (Fin k × Fin k)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = k * k := by simp

/-- A residual sunflower lifts when its own generated preimages do not interfere. -/
noncomputable def liftResidualWitness_of_noInterference
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core)
    (noInterference : Not (ResidualLiftInterference W)) :
    Concrete.CorePetalSunflowerWitness k F core := by
  exact
    { petals := fun i => (witnessSource W i).val
      petals_mem := fun i => (witnessSource W i).property
      petals_injective := by
        intro i j sameEdge
        apply witnessSource_injective W
        exact Subtype.ext sameEdge
      pairwise_intersection := by
        intro i j distinct
        have left_not_right :
            chosenCoordinate F (witnessSource W i) ∉
              (witnessSource W j).val := by
          intro cross
          exact noInterference ⟨i, j, distinct, cross⟩
        have right_not_left :
            chosenCoordinate F (witnessSource W j) ∉
              (witnessSource W i).val := by
          intro cross
          exact noInterference ⟨j, i, fun same => distinct same.symm, cross⟩
        rw [intersection_eq_residual_inter_of_no_cross F
          (witnessSource W i) (witnessSource W j)
          left_not_right right_not_left,
          witnessSource_spec W i, witnessSource_spec W j,
          W.pairwise_intersection i j distinct] }

/-- A residual sunflower lifts whenever every outgoing cross is absent globally. -/
noncomputable def liftResidualWitness_of_noOutgoingCross
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core)
    (noOutgoingCross : Not (HasOutgoingCross F)) :
    Concrete.CorePetalSunflowerWitness k F core :=
  liftResidualWitness_of_noInterference W (by
    rintro ⟨i, j, distinct, cross⟩
    apply noOutgoingCross
    exact ⟨witnessSource W i, witnessSource W j,
      fun same => distinct (witnessSource_injective W same), cross⟩)

/-- The exact local dichotomy for one generated residual sunflower witness. -/
theorem hasSunflower_or_interference_of_residualWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core) :
    Concrete.HasSunflower k F ∨ ResidualLiftInterference W := by
  classical
  by_cases interference : ResidualLiftInterference W
  · exact Or.inr interference
  · exact Or.inl
      ⟨core, ⟨liftResidualWitness_of_noInterference W interference⟩⟩

theorem residualLiftInterference_of_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (noSunflower : Not (Concrete.HasSunflower k F))
    (W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core) :
    ResidualLiftInterference W := by
  rcases hasSunflower_or_interference_of_residualWitness W with
    sunflower | interference
  · exact False.elim (noSunflower sunflower)
  · exact interference

theorem residualLiftCrossProfile_nonempty_of_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (noSunflower : Not (Concrete.HasSunflower k F))
    (W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core) :
    (residualLiftCrossProfile W).Nonempty :=
  (residualLiftInterference_iff_crossProfile_nonempty W).mp
    (residualLiftInterference_of_noSunflower noSunflower W)

theorem outgoingCross_of_residualLiftInterference
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    {W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core}
    (interference : ResidualLiftInterference W) :
    HasOutgoingCross F := by
  rcases interference with ⟨i, j, distinct, cross⟩
  exact ⟨witnessSource W i, witnessSource W j,
    fun same => distinct (witnessSource_injective W same), cross⟩

theorem hasSunflower_of_residualFamily_of_noOutgoingCross
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (hasResidualSunflower : Concrete.HasSunflower k (residualFamily F))
    (noOutgoingCross : Not (HasOutgoingCross F)) :
    Concrete.HasSunflower k F := by
  rcases hasResidualSunflower with ⟨core, ⟨W⟩⟩
  exact ⟨core, ⟨liftResidualWitness_of_noOutgoingCross W noOutgoingCross⟩⟩

/--
The exact generated-data frontier: a residual sunflower either lifts, or an
actual outgoing cross is present in the original family.
-/
theorem hasSunflower_or_outgoingCross_of_residualFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (hasResidualSunflower : Concrete.HasSunflower k (residualFamily F)) :
    Concrete.HasSunflower k F ∨ HasOutgoingCross F := by
  rcases hasResidualSunflower with ⟨core, ⟨W⟩⟩
  rcases hasSunflower_or_interference_of_residualWitness W with
    sunflower | interference
  · exact Or.inl sunflower
  · exact Or.inr (outgoingCross_of_residualLiftInterference interference)

theorem outgoingCross_of_residualSunflower_of_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (noSunflower : Not (Concrete.HasSunflower k F))
    (hasResidualSunflower : Concrete.HasSunflower k (residualFamily F)) :
    HasOutgoingCross F := by
  rcases hasSunflower_or_outgoingCross_of_residualFamily
      hasResidualSunflower with sunflower | outgoing
  · exact False.elim (noSunflower sunflower)
  · exact outgoing

theorem residualFamily_noSunflower_of_noOutgoingCross
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (noSunflower : Not (Concrete.HasSunflower k F))
    (noOutgoingCross : Not (HasOutgoingCross F)) :
    Not (Concrete.HasSunflower k (residualFamily F)) := by
  intro hasResidualSunflower
  exact noOutgoingCross
    (outgoingCross_of_residualSunflower_of_noSunflower
      noSunflower hasResidualSunflower)

end SelectedCoordinateReduction
end V2
end SunflowerAASC
