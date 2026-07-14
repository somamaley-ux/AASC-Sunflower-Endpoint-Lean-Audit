import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import SunflowerAASC.V2.ConcreteCarrier

namespace SunflowerAASC
namespace V2
namespace Concrete

/-- A nontrivial sunflower witness contains its declared core in every petal. -/
theorem CorePetalSunflowerWitness.core_subset
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (W : CorePetalSunflowerWitness k F core)
    (two_le : 2 ≤ k)
    (index : Fin k) :
    core ⊆ W.petals index := by
  have card_gt : 1 < Fintype.card (Fin k) := by
    simp
    omega
  obtain ⟨other, other_ne_index⟩ :=
    Fintype.exists_ne_of_one_lt_card card_gt index
  intro point point_mem_core
  have point_mem_intersection :
      point ∈ W.petals index ∩ W.petals other := by
    rw [W.pairwise_intersection index other other_ne_index.symm]
    exact point_mem_core
  exact (Finset.mem_inter.mp point_mem_intersection).1

/--
Adjoin one genuinely new edge whose intersection with every old petal is the
declared core.  The result is a sunflower with one additional petal.
-/
def CorePetalSunflowerWitness.augment
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (W : CorePetalSunflowerWitness k F core)
    (edge : Finset alpha)
    (edge_mem : edge ∈ F.edges)
    (edge_fresh : ∀ index : Fin k, edge ≠ W.petals index)
    (edge_intersection : ∀ index : Fin k,
      edge ∩ W.petals index = core) :
    CorePetalSunflowerWitness (k + 1) F core where
  petals := Fin.cases edge W.petals
  petals_mem := by
    intro index
    refine Fin.cases edge_mem (fun old => ?_) index
    exact W.petals_mem old
  petals_injective := by
    intro left
    refine Fin.cases ?_ (fun leftOld => ?_) left
    · intro right
      refine Fin.cases ?_ (fun rightOld => ?_) right
      · intro _same
        rfl
      · intro same
        exact False.elim (edge_fresh rightOld same)
    · intro right
      refine Fin.cases ?_ (fun rightOld => ?_) right
      · intro same
        exact False.elim (edge_fresh leftOld same.symm)
      · intro same
        exact congrArg Fin.succ (W.petals_injective same)
  pairwise_intersection := by
    intro left
    refine Fin.cases ?_ (fun leftOld => ?_) left
    · intro right
      refine Fin.cases ?_ (fun rightOld => ?_) right
      · intro different
        exact False.elim (different rfl)
      · intro _different
        exact edge_intersection rightOld
    · intro right
      refine Fin.cases ?_ (fun rightOld => ?_) right
      · intro _different
        rw [Finset.inter_comm]
        exact edge_intersection leftOld
      · intro different
        exact W.pairwise_intersection leftOld rightOld fun sameOld =>
          different (congrArg Fin.succ sameOld)

theorem hasSunflower_succ_of_augmentingEdge
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (W : CorePetalSunflowerWitness k F core)
    (edge : Finset alpha)
    (edge_mem : edge ∈ F.edges)
    (edge_fresh : ∀ index : Fin k, edge ≠ W.petals index)
    (edge_intersection : ∀ index : Fin k,
      edge ∩ W.petals index = core) :
    HasSunflower (k + 1) F :=
  ⟨core, ⟨W.augment edge edge_mem edge_fresh edge_intersection⟩⟩

/--
Relative to any nontrivial sunflower, an ambient edge either adds one petal or
has a concrete obstruction: it duplicates a selected petal, omits a core
point, or meets a selected petal outside the core.
-/
theorem CorePetalSunflowerWitness.augment_or_finiteObstruction
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (W : CorePetalSunflowerWitness k F core)
    (two_le : 2 ≤ k)
    (edge : Finset alpha)
    (edge_mem : edge ∈ F.edges) :
    HasSunflower (k + 1) F ∨
      (∃ index : Fin k, edge = W.petals index) ∨
      (∃ point : alpha, point ∈ core ∧ point ∉ edge) ∨
      (∃ index : Fin k, ∃ point : alpha,
        point ∈ edge ∧ point ∈ W.petals index ∧ point ∉ core) := by
  classical
  by_cases duplicate : ∃ index : Fin k, edge = W.petals index
  · exact Or.inr (Or.inl duplicate)
  by_cases missingCore : ∃ point : alpha, point ∈ core ∧ point ∉ edge
  · exact Or.inr (Or.inr (Or.inl missingCore))
  by_cases excess : ∃ index : Fin k, ∃ point : alpha,
      point ∈ edge ∧ point ∈ W.petals index ∧ point ∉ core
  · exact Or.inr (Or.inr (Or.inr excess))
  apply Or.inl
  apply hasSunflower_succ_of_augmentingEdge W edge edge_mem
  · intro index same
    exact duplicate ⟨index, same⟩
  · intro index
    apply Finset.ext
    intro point
    constructor
    · intro point_mem_intersection
      have point_mem_edge := (Finset.mem_inter.mp point_mem_intersection).1
      have point_mem_petal := (Finset.mem_inter.mp point_mem_intersection).2
      by_contra point_not_mem_core
      exact excess ⟨index, point, point_mem_edge,
        point_mem_petal, point_not_mem_core⟩
    · intro point_mem_core
      apply Finset.mem_inter.mpr
      constructor
      · by_contra point_not_mem_edge
        exact missingCore ⟨point, point_mem_core, point_not_mem_edge⟩
      · exact W.core_subset two_le index point_mem_core

/--
A largest realized sunflower arity strictly below a fixed target.  Maximality
is only over petal count; the witness retains its actual core and family edges.
-/
structure MaximalLowerSunflowerWitness
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (target : Nat)
    (F : UniformSetFamily alpha n) where
  arity : Nat
  two_le : 2 ≤ arity
  lt_target : arity < target
  core : Finset alpha
  witness : CorePetalSunflowerWitness arity F core
  maximal : ∀ m : Nat, arity < m → m < target →
    Not (HasSunflower m F)

/-- Any realized nontrivial lower sunflower extends to a maximal one below the
same target by finite search over the petal parameter. -/
theorem exists_maximalLowerSunflowerWitness_of_seed
    {alpha : Type}
    [DecidableEq alpha]
    {n target seed : Nat}
    {F : UniformSetFamily alpha n}
    (seed_two_le : 2 ≤ seed)
    (seed_lt_target : seed < target)
    (seedSunflower : HasSunflower seed F) :
    Nonempty (MaximalLowerSunflowerWitness target F) := by
  classical
  let P : Nat → Prop := fun m => 2 ≤ m ∧ HasSunflower m F
  let maximalArity := Nat.findGreatest P (target - 1)
  have seed_le_bound : seed ≤ target - 1 := by omega
  have maximal_spec : P maximalArity :=
    Nat.findGreatest_spec seed_le_bound ⟨seed_two_le, seedSunflower⟩
  rcases maximal_spec with ⟨maximal_two_le, maximalSunflower⟩
  rcases maximalSunflower with ⟨core, ⟨W⟩⟩
  have maximal_lt_target : maximalArity < target := by
    have maximal_le_bound : maximalArity ≤ target - 1 :=
      Nat.findGreatest_le (target - 1)
    omega
  exact ⟨{
    arity := maximalArity
    two_le := maximal_two_le
    lt_target := maximal_lt_target
    core := core
    witness := W
    maximal := by
      intro m maximal_lt_m m_lt_target mSunflower
      have m_le_bound : m ≤ target - 1 := by omega
      exact Nat.findGreatest_is_greatest
        (P := P) maximal_lt_m m_le_bound
          ⟨by omega, mSunflower⟩ }⟩

noncomputable def maximalLowerSunflowerWitnessOfSeed
    {alpha : Type}
    [DecidableEq alpha]
    {n target seed : Nat}
    {F : UniformSetFamily alpha n}
    (seed_two_le : 2 ≤ seed)
    (seed_lt_target : seed < target)
    (seedSunflower : HasSunflower seed F) :
    MaximalLowerSunflowerWitness target F :=
  Classical.choice <| exists_maximalLowerSunflowerWitness_of_seed
    seed_two_le seed_lt_target seedSunflower

/--
At a maximal lower sunflower, target-sunflower exclusion removes the only
growth branch.  Every ambient edge therefore has one of the three explicit
finite obstructions to joining the maximal witness.
-/
theorem MaximalLowerSunflowerWitness.edge_has_finiteObstruction
    {alpha : Type}
    [DecidableEq alpha]
    {n target : Nat}
    {F : UniformSetFamily alpha n}
    (M : MaximalLowerSunflowerWitness target F)
    (noTargetSunflower : Not (HasSunflower target F))
    (edge : Finset alpha)
    (edge_mem : edge ∈ F.edges) :
    (∃ index : Fin M.arity, edge = M.witness.petals index) ∨
      (∃ point : alpha, point ∈ M.core ∧ point ∉ edge) ∨
      (∃ index : Fin M.arity, ∃ point : alpha,
        point ∈ edge ∧
          point ∈ M.witness.petals index ∧ point ∉ M.core) := by
  rcases M.witness.augment_or_finiteObstruction
      M.two_le edge edge_mem with growth | obstruction
  · have growth_le_target : M.arity + 1 ≤ target := by
      have := M.lt_target
      omega
    rcases Nat.lt_or_eq_of_le growth_le_target with
      growth_lt_target | growth_eq_target
    · exact False.elim <|
        M.maximal (M.arity + 1) (by omega) growth_lt_target growth
    · rw [growth_eq_target] at growth
      exact False.elim (noTargetSunflower growth)
  · exact obstruction

/-- Two different finite sets of the same size have a point on the left that
is absent on the right. -/
theorem exists_mem_not_mem_of_ne_of_card_eq
    {alpha : Type}
    [DecidableEq alpha]
    (left right : Finset alpha)
    (different : left ≠ right)
    (sameCard : left.card = right.card) :
    ∃ point : alpha, point ∈ left ∧ point ∉ right := by
  have differenceNonempty : (left \ right).Nonempty :=
    Finset.sdiff_nonempty.mpr fun left_subset =>
      different <| Finset.eq_of_subset_of_card_le left_subset (by omega)
  rcases differenceNonempty with ⟨point, point_mem⟩
  exact ⟨point, (Finset.mem_sdiff.mp point_mem).1,
    (Finset.mem_sdiff.mp point_mem).2⟩

/--
If two distinct equal-sized reference petals share a point missing from an
equal-sized edge, then the edge has a point other than its chosen coordinate
outside at least one reference petal.
-/
theorem exists_present_witness_of_missing_common_point
    {alpha : Type}
    [DecidableEq alpha]
    (edge left right : Finset alpha)
    (left_ne_right : left ≠ right)
    (edge_card_left : edge.card = left.card)
    (edge_card_right : edge.card = right.card)
    (chosen : alpha)
    (chosen_mem_edge : chosen ∈ edge)
    (missing : alpha)
    (missing_mem_left : missing ∈ left)
    (missing_mem_right : missing ∈ right)
    (missing_not_mem_edge : missing ∉ edge) :
    ∃ point : alpha,
      point ∈ edge ∧ point ≠ chosen ∧
        (point ∉ left ∨ point ∉ right) := by
  by_contra noWitness
  have remaining_mem_both : ∀ point : alpha,
      point ∈ edge → point ≠ chosen →
        point ∈ left ∧ point ∈ right := by
    intro point point_mem_edge point_ne_chosen
    constructor
    · by_contra point_not_left
      exact noWitness ⟨point, point_mem_edge, point_ne_chosen,
        Or.inl point_not_left⟩
    · by_contra point_not_right
      exact noWitness ⟨point, point_mem_edge, point_ne_chosen,
        Or.inr point_not_right⟩
  have edgeErase_subset_leftErase :
      edge.erase chosen ⊆ left.erase missing := by
    intro point point_mem
    rcases Finset.mem_erase.mp point_mem with
      ⟨point_ne_chosen, point_mem_edge⟩
    have point_mem_left :=
      (remaining_mem_both point point_mem_edge point_ne_chosen).1
    have point_ne_missing : point ≠ missing := by
      intro same
      subst point
      exact missing_not_mem_edge point_mem_edge
    exact Finset.mem_erase.mpr ⟨point_ne_missing, point_mem_left⟩
  have edgeErase_subset_rightErase :
      edge.erase chosen ⊆ right.erase missing := by
    intro point point_mem
    rcases Finset.mem_erase.mp point_mem with
      ⟨point_ne_chosen, point_mem_edge⟩
    have point_mem_right :=
      (remaining_mem_both point point_mem_edge point_ne_chosen).2
    have point_ne_missing : point ≠ missing := by
      intro same
      subst point
      exact missing_not_mem_edge point_mem_edge
    exact Finset.mem_erase.mpr ⟨point_ne_missing, point_mem_right⟩
  have edgeErase_card_leftErase :
      (edge.erase chosen).card = (left.erase missing).card := by
    rw [Finset.card_erase_of_mem chosen_mem_edge,
      Finset.card_erase_of_mem missing_mem_left, edge_card_left]
  have edgeErase_card_rightErase :
      (edge.erase chosen).card = (right.erase missing).card := by
    rw [Finset.card_erase_of_mem chosen_mem_edge,
      Finset.card_erase_of_mem missing_mem_right, edge_card_right]
  have edgeErase_eq_leftErase :
      edge.erase chosen = left.erase missing :=
    Finset.eq_of_subset_of_card_le edgeErase_subset_leftErase
      (by omega)
  have edgeErase_eq_rightErase :
      edge.erase chosen = right.erase missing :=
    Finset.eq_of_subset_of_card_le edgeErase_subset_rightErase
      (by omega)
  apply left_ne_right
  calc
    left = insert missing (left.erase missing) :=
      (Finset.insert_erase missing_mem_left).symm
    _ = insert missing (right.erase missing) := by
      rw [← edgeErase_eq_leftErase, edgeErase_eq_rightErase]
    _ = right := Finset.insert_erase missing_mem_right

/-- A matching in the link above `core`, expressed with actual residual sets. -/
structure CoreLinkMatching
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (k : Nat)
    (F : UniformSetFamily alpha n)
    (core : Finset alpha) where
  petals : Fin k -> Finset alpha
  petals_mem : forall i : Fin k, petals i ∈ F.edges
  petals_injective : Function.Injective petals
  core_subset : forall i : Fin k, core ⊆ petals i
  residuals_disjoint :
    forall i j : Fin k, Not (i = j) ->
      Disjoint (petals i \ core) (petals j \ core)

theorem CoreLinkMatching.pairwise_intersection_eq_core
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : CoreLinkMatching k F core)
    (i j : Fin k)
    (hne : Not (i = j)) :
    M.petals i ∩ M.petals j = core := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hxi : x ∈ M.petals i := (Finset.mem_inter.mp hx).1
    have hxj : x ∈ M.petals j := (Finset.mem_inter.mp hx).2
    by_contra hxcore
    have hri : x ∈ M.petals i \ core := Finset.mem_sdiff.mpr ⟨hxi, hxcore⟩
    have hrj : x ∈ M.petals j \ core := Finset.mem_sdiff.mpr ⟨hxj, hxcore⟩
    exact Finset.disjoint_left.mp (M.residuals_disjoint i j hne) hri hrj
  · intro hxcore
    exact Finset.mem_inter.mpr
      ⟨M.core_subset i hxcore, M.core_subset j hxcore⟩

/-- A concrete link matching supplies the standard core-petal witness. -/
def CoreLinkMatching.toSunflowerWitness
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : CoreLinkMatching k F core) :
    CorePetalSunflowerWitness k F core where
  petals := M.petals
  petals_mem := M.petals_mem
  petals_injective := M.petals_injective
  pairwise_intersection := M.pairwise_intersection_eq_core

theorem hasSunflower_of_coreLinkMatching
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : CoreLinkMatching k F core) :
    HasSunflower k F := by
  exact ⟨core, Nonempty.intro M.toSunflowerWitness⟩

theorem noSunflower_forbids_coreLinkMatching
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : UniformSetFamily alpha n}
    (noSunflower : Not (HasSunflower k F))
    (core : Finset alpha) :
    Not (Nonempty (CoreLinkMatching k F core)) := by
  intro hmatching
  exact noSunflower (hasSunflower_of_coreLinkMatching hmatching.some)

theorem CoreLinkMatching.residual_card_le_rank
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : CoreLinkMatching k F core)
    (i : Fin k) :
    (M.petals i \ core).card <= n := by
  calc
    (M.petals i \ core).card
        = (M.petals i).card - (core ∩ M.petals i).card :=
          Finset.card_sdiff
    _ <= (M.petals i).card := Nat.sub_le _ _
    _ = n := F.uniform (M.petals i) (M.petals_mem i)

/-- A finite, not-yet-arity-indexed matching in the link above `core`. -/
structure FiniteCoreLinkMatching
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (F : UniformSetFamily alpha n)
    (core : Finset alpha) where
  petals : Finset (Finset alpha)
  petals_subset : petals ⊆ F.edges
  core_subset : forall edge : Finset alpha, edge ∈ petals -> core ⊆ edge
  residuals_disjoint :
    forall left right : Finset alpha,
      left ∈ petals -> right ∈ petals -> Not (left = right) ->
      Disjoint (left \ core) (right \ core)

noncomputable def FiniteCoreLinkMatching.restrictToArity
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : FiniteCoreLinkMatching F core)
    (hcard : k <= M.petals.card) :
    CoreLinkMatching k F core := by
  let enumerate : {edge // edge ∈ M.petals} ≃ Fin M.petals.card :=
    Fintype.equivFinOfCardEq (by simp)
  let select : Fin k -> {edge // edge ∈ M.petals} :=
    fun i => enumerate.symm (Fin.castLE hcard i)
  have select_injective : Function.Injective select := by
    intro i j hij
    have hcast : Fin.castLE hcard i = Fin.castLE hcard j := by
      exact enumerate.symm.injective hij
    exact Fin.castLE_injective hcard hcast
  exact
    { petals := fun i => (select i).val
      petals_mem := fun i => M.petals_subset (select i).property
      petals_injective := by
        intro i j hij
        apply select_injective
        exact Subtype.ext hij
      core_subset := fun i => M.core_subset (select i).val (select i).property
      residuals_disjoint := by
        intro i j hne
        exact M.residuals_disjoint
          (select i).val
          (select j).val
          (select i).property
          (select j).property
          (fun heq => hne (select_injective (Subtype.ext heq))) }

theorem finiteCoreLinkMatching_card_lt_of_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : UniformSetFamily alpha n}
    (noSunflower : Not (HasSunflower k F))
    {core : Finset alpha}
    (M : FiniteCoreLinkMatching F core) :
    M.petals.card < k := by
  apply Nat.lt_of_not_ge
  intro hcard
  exact noSunflower
    (hasSunflower_of_coreLinkMatching (M.restrictToArity hcard))

/-- The classical raw blocker is the union of the matched residual petals. -/
def FiniteCoreLinkMatching.rawBlocker
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : FiniteCoreLinkMatching F core) : Finset alpha :=
  M.petals.biUnion (fun edge => edge \ core)

theorem FiniteCoreLinkMatching.residual_card_le_rank
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : FiniteCoreLinkMatching F core)
    {edge : Finset alpha}
    (hedge : edge ∈ M.petals) :
    (edge \ core).card <= n := by
  calc
    (edge \ core).card = edge.card - (core ∩ edge).card := Finset.card_sdiff
    _ <= edge.card := Nat.sub_le _ _
    _ = n := F.uniform edge (M.petals_subset hedge)

theorem FiniteCoreLinkMatching.rawBlocker_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : FiniteCoreLinkMatching F core) :
    M.rawBlocker.card <= M.petals.card * n := by
  exact Finset.card_biUnion_le_card_mul
    M.petals
    (fun edge => edge \ core)
    n
    (fun _ hedge => M.residual_card_le_rank hedge)

theorem FiniteCoreLinkMatching.rawBlocker_card_le_k_mul_rank
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : FiniteCoreLinkMatching F core)
    (noSunflower : Not (HasSunflower k F)) :
    M.rawBlocker.card <= k * n := by
  exact Nat.le_trans M.rawBlocker_card_le
    (Nat.mul_le_mul_right n
      (Nat.le_of_lt (finiteCoreLinkMatching_card_lt_of_noSunflower noSunflower M)))

/-- The standard Erdős-Rado sharpening uses `petals.card < k` as
`petals.card <= k - 1` instead of rounding it up to `k`. -/
theorem FiniteCoreLinkMatching.rawBlocker_card_le_pred_mul_rank
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : FiniteCoreLinkMatching F core)
    (noSunflower : Not (HasSunflower k F)) :
    M.rawBlocker.card <= (k - 1) * n := by
  have hpetals : M.petals.card <= k - 1 := by
    have hlt := finiteCoreLinkMatching_card_lt_of_noSunflower noSunflower M
    omega
  exact Nat.le_trans M.rawBlocker_card_le
    (Nat.mul_le_mul_right n hpetals)

def IsFiniteCoreLinkMatching
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (F : UniformSetFamily alpha n)
    (core : Finset alpha)
    (petals : Finset (Finset alpha)) : Prop :=
  petals ⊆ F.edges /\
  (forall edge : Finset alpha, edge ∈ petals -> core ⊆ edge) /\
  (forall left right : Finset alpha,
    left ∈ petals -> right ∈ petals -> Not (left = right) ->
    Disjoint (left \ core) (right \ core))

/-- Maximality means every link petal is selected or meets a selected residual. -/
structure MaximalFiniteCoreLinkMatching
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (F : UniformSetFamily alpha n)
    (core : Finset alpha) where
  matching : FiniteCoreLinkMatching F core
  maximal :
    forall edge : Finset alpha,
      edge ∈ F.edges -> core ⊆ edge ->
      edge ∈ matching.petals \/
      Exists (fun chosen : Finset alpha =>
        chosen ∈ matching.petals /\
        Not (Disjoint (edge \ core) (chosen \ core)))

/-- A maximum-cardinality finite link matching exists and is maximal. -/
noncomputable def maximalFiniteCoreLinkMatching
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (F : UniformSetFamily alpha n)
    (core : Finset alpha) :
    MaximalFiniteCoreLinkMatching F core := by
  classical
  let candidates : Finset (Finset (Finset alpha)) :=
    F.edges.powerset.filter (IsFiniteCoreLinkMatching F core)
  have candidates_nonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, IsFiniteCoreLinkMatching]
  let maximumExists :=
    Finset.exists_max_image candidates Finset.card candidates_nonempty
  let petals := Classical.choose maximumExists
  have maximumSpec := Classical.choose_spec maximumExists
  have petals_mem : petals ∈ candidates := maximumSpec.1
  have maximal_card :
      forall candidate, candidate ∈ candidates -> candidate.card <= petals.card :=
    maximumSpec.2
  have matching_holds : IsFiniteCoreLinkMatching F core petals := by
    exact (Finset.mem_filter.mp petals_mem).2
  let matching : FiniteCoreLinkMatching F core :=
    { petals := petals
      petals_subset := matching_holds.1
      core_subset := matching_holds.2.1
      residuals_disjoint := matching_holds.2.2 }
  exact
    { matching := matching
      maximal := by
        intro edge hedge hcore
        by_cases edge_mem : edge ∈ petals
        · exact Or.inl edge_mem
        · apply Or.inr
          by_contra noConflict
          have edge_disjoint :
              forall chosen : Finset alpha,
                chosen ∈ petals ->
                Disjoint (edge \ core) (chosen \ core) := by
            intro chosen chosen_mem
            exact Classical.byContradiction (fun hnot =>
              noConflict ⟨chosen, chosen_mem, hnot⟩)
          have inserted_holds :
              IsFiniteCoreLinkMatching F core (insert edge petals) := by
            refine ⟨?_, ?_, ?_⟩
            · intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hx
              · exact hedge
              · exact matching_holds.1 hx
            · intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hx
              · exact hcore
              · exact matching_holds.2.1 x hx
            · intro left right hleft hright hne
              rcases Finset.mem_insert.mp hleft with rfl | hleft
              · rcases Finset.mem_insert.mp hright with hright | hright
                · exact False.elim (hne hright.symm)
                · exact edge_disjoint right hright
              · rcases Finset.mem_insert.mp hright with hright | hright
                · subst right
                  exact (edge_disjoint left hleft).symm
                · exact matching_holds.2.2 left right hleft hright hne
          have inserted_mem : insert edge petals ∈ candidates := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_powerset.mpr inserted_holds.1, inserted_holds⟩
          have hle := maximal_card (insert edge petals) inserted_mem
          rw [Finset.card_insert_of_notMem edge_mem] at hle
          exact Nat.not_succ_le_self petals.card hle }

theorem MaximalFiniteCoreLinkMatching.hits_link_petals
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    {F : UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : MaximalFiniteCoreLinkMatching F core)
    {edge : Finset alpha}
    (edge_mem : edge ∈ F.edges)
    (core_subset : core ⊆ edge)
    (live : (edge \ core).Nonempty) :
    Not (Disjoint (edge \ core) M.matching.rawBlocker) := by
  rcases M.maximal edge edge_mem core_subset with selected | conflict
  · have residual_subset : edge \ core ⊆ M.matching.rawBlocker := by
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨edge, selected, hx⟩
    rcases live with ⟨x, hx⟩
    exact fun hdisjoint =>
      Finset.disjoint_left.mp
        (hdisjoint.mono_right residual_subset)
        hx
        hx
  · rcases conflict with ⟨chosen, chosen_mem, conflict⟩
    exact fun hdisjoint =>
      conflict
        (hdisjoint.mono_right
          (Finset.subset_biUnion_of_mem
            (fun selectedEdge => selectedEdge \ core)
            chosen_mem))

end Concrete
end V2
end SunflowerAASC
