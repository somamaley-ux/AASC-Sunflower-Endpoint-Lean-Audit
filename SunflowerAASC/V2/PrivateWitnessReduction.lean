import SunflowerAASC.V2.MinimalBlocker

namespace SunflowerAASC
namespace V2
namespace PrivateWitnessReduction

/-- Remove the unique private blocker coordinate from its witness edge. -/
noncomputable def residual
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Finset alpha :=
  (MinimalBlocker.privateEdge F x).erase x.val

theorem residual_card
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (residual F x).card = r := by
  rw [residual, Finset.card_erase_of_mem
    (MinimalBlocker.privateEdge_contains F x)]
  rw [F.uniform (MinimalBlocker.privateEdge F x)
    (MinimalBlocker.privateEdge_mem F x)]
  simp

theorem privateEdge_eq_insert_residual
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    MinimalBlocker.privateEdge F x = insert x.val (residual F x) := by
  exact (Finset.insert_erase
    (MinimalBlocker.privateEdge_contains F x)).symm

theorem blocker_mem_not_mem_residual
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    left.val ∉ residual F right := by
  intro left_mem
  have left_mem_edge : left.val ∈ MinimalBlocker.privateEdge F right :=
    Finset.mem_of_mem_erase left_mem
  have left_eq_right : left = right :=
    (MinimalBlocker.mem_privateEdge_iff F right left).mp left_mem_edge
  subst left
  exact (MinimalBlocker.privateEdge F right).notMem_erase right.val left_mem

/-- The rank-lowered family of all distinct private witness residuals. -/
noncomputable def residualFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    Concrete.UniformSetFamily alpha r where
  edges := (MinimalBlocker.minimalBlocker F).attach.image (residual F)
  uniform := by
    intro edge edge_mem
    rcases Finset.mem_image.mp edge_mem with ⟨x, _, rfl⟩
    exact residual_card F x

theorem mem_residualFamily_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {edge : Finset alpha} :
    edge ∈ (residualFamily F).edges <->
      ∃ x : {x // x ∈ MinimalBlocker.minimalBlocker F}, residual F x = edge := by
  constructor
  · intro edge_mem
    rcases Finset.mem_image.mp edge_mem with ⟨x, _, same⟩
    exact ⟨x, same⟩
  · rintro ⟨x, rfl⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩

/-- Private coordinates producing one fixed rank-lowered residual. -/
noncomputable def residualFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (edge : Finset alpha) :
    Finset {x // x ∈ MinimalBlocker.minimalBlocker F} := by
  classical
  exact (MinimalBlocker.minimalBlocker F).attach.filter
    (fun x => residual F x = edge)

theorem mem_residualFiber_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {edge : Finset alpha}
    {x : {x // x ∈ MinimalBlocker.minimalBlocker F}} :
    x ∈ residualFiber F edge <-> residual F x = edge := by
  classical
  simp [residualFiber]

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
  let enumerate : {x // x ∈ chosen} ≃ Fin k :=
    Fintype.equivFinOfCardEq (by simp [chosen_card])
  let coordinate : Fin k -> {x // x ∈ MinimalBlocker.minimalBlocker F} :=
    fun i => (enumerate.symm i).val
  have coordinate_mem : ∀ i : Fin k,
      coordinate i ∈ residualFiber F edge := by
    intro i
    exact chosen_subset (enumerate.symm i).property
  have coordinate_residual : ∀ i : Fin k,
      residual F (coordinate i) = edge := by
    intro i
    exact mem_residualFiber_iff.mp (coordinate_mem i)
  have coordinate_injective : Function.Injective coordinate := by
    intro i j same
    have nested_same : enumerate.symm i = enumerate.symm j := by
      apply Subtype.ext
      exact same
    exact enumerate.symm.injective nested_same
  refine ⟨edge, ⟨{
    petals := fun i => MinimalBlocker.privateEdge F (coordinate i)
    petals_mem := fun i => MinimalBlocker.privateEdge_mem F (coordinate i)
    petals_injective := fun i j sameEdge =>
      coordinate_injective (MinimalBlocker.privateEdge_injective F sameEdge)
    pairwise_intersection := ?_ }⟩⟩
  intro i j distinct
  have coordinate_distinct : coordinate i ≠ coordinate j :=
    fun same => distinct (coordinate_injective same)
  rw [privateEdge_eq_insert_residual F (coordinate i),
    privateEdge_eq_insert_residual F (coordinate j),
    coordinate_residual i, coordinate_residual j]
  apply Finset.ext
  intro y
  constructor
  · intro y_mem
    rcases Finset.mem_inter.mp y_mem with ⟨y_left, y_right⟩
    rcases Finset.mem_insert.mp y_left with y_eq_left | y_edge
    · subst y
      rcases Finset.mem_insert.mp y_right with sameCoordinate | left_edge
      · exact False.elim <| coordinate_distinct (Subtype.ext sameCoordinate)
      · exact False.elim <|
          (by
            rw [← coordinate_residual j] at left_edge
            exact blocker_mem_not_mem_residual
              F (coordinate i) (coordinate j) left_edge)
    · exact y_edge
  · intro y_edge
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_insert.mpr (Or.inr y_edge),
        Finset.mem_insert.mpr (Or.inr y_edge)⟩

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

/--
Each literal residual fiber has a canonical finite slot embedding. The slot is
derived from the sunflower-free fiber bound; it is not an additional coloring
hypothesis.
-/
noncomputable def residualFiberEmbedding
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (edge : Finset alpha) :
    {x // x ∈ residualFiber F edge} ↪ Fin k := by
  let card_le : Fintype.card {x // x ∈ residualFiber F edge} ≤ k := by
    simpa using Nat.le_of_lt (residualFiber_card_lt F noSunflower edge)
  exact (Fintype.equivFin _).toEmbedding.trans
    ⟨Fin.castLE card_le, Fin.castLE_injective card_le⟩

/-- A fixed global order code used only to enumerate each literal fiber. -/
noncomputable def minimalBlockerOrderCode
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    Fin (Fintype.card {x // x ∈ MinimalBlocker.minimalBlocker F}) :=
  Fintype.equivFin _ x

/-- Coordinates in the same residual fiber that precede `x` globally. -/
noncomputable def residualFiberBefore
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    Finset {x // x ∈ MinimalBlocker.minimalBlocker F} := by
  classical
  exact (residualFiber F (residual F x)).filter
    (fun y => minimalBlockerOrderCode F y < minimalBlockerOrderCode F x)

theorem residualFiberBefore_ssubset
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    residualFiberBefore F x ⊂ residualFiber F (residual F x) := by
  classical
  rw [residualFiberBefore, Finset.filter_ssubset]
  exact ⟨x, mem_residualFiber_iff.mpr rfl, by simp⟩

theorem residualFiberBefore_ssubset_of_code_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameResidual : residual F left = residual F right)
    (code_lt : minimalBlockerOrderCode F left <
      minimalBlockerOrderCode F right) :
    residualFiberBefore F left ⊂ residualFiberBefore F right := by
  classical
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro y y_mem
    rw [residualFiberBefore, Finset.mem_filter] at y_mem ⊢
    exact ⟨mem_residualFiber_iff.mpr
      ((mem_residualFiber_iff.mp y_mem.1).trans sameResidual),
      lt_trans y_mem.2 code_lt⟩
  · intro sameBefore
    have left_mem_right : left ∈ residualFiberBefore F right := by
      rw [residualFiberBefore, Finset.mem_filter]
      exact ⟨mem_residualFiber_iff.mpr sameResidual, code_lt⟩
    have left_not_mem_left : left ∉ residualFiberBefore F left := by
      simp [residualFiberBefore]
    apply left_not_mem_left
    rw [sameBefore]
    exact left_mem_right

/-- The finite local standing slot occupied inside one literal residual fiber. -/
noncomputable def residualFiberSlot
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (x : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Fin k :=
  ⟨(residualFiberBefore F x).card,
    (Finset.card_lt_card (residualFiberBefore_ssubset F x)).trans
      (residualFiber_card_lt F noSunflower (residual F x))⟩

/-- Equal residual parent and equal derived slot force literal blocker equality. -/
theorem eq_of_same_residual_same_fiberSlot
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameResidual : residual F left = residual F right)
    (sameSlot : residualFiberSlot F noSunflower left =
      residualFiberSlot F noSunflower right) :
    left = right := by
  have sameCard : (residualFiberBefore F left).card =
      (residualFiberBefore F right).card :=
    congrArg Fin.val sameSlot
  rcases lt_trichotomy (minimalBlockerOrderCode F left)
      (minimalBlockerOrderCode F right) with code_lt | code_eq | code_gt
  · exact False.elim <| Nat.ne_of_lt
      (Finset.card_lt_card <|
        residualFiberBefore_ssubset_of_code_lt
          F left right sameResidual code_lt) sameCard
  · exact (Fintype.equivFin _).injective code_eq
  · exact False.elim <| Nat.ne_of_lt
      (Finset.card_lt_card <|
        residualFiberBefore_ssubset_of_code_lt
          F right left sameResidual.symm code_gt) sameCard.symm

/-- A surviving non-skin distinction over one residual must occupy another slot. -/
theorem residualFiberSlot_ne_of_sameResidual_of_nonSkin
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameResidual : residual F left = residual F right)
    (nonSkin : Not (MinimalBlocker.EndpointSkinEquivalent F left right)) :
    residualFiberSlot F noSunflower left ≠
      residualFiberSlot F noSunflower right := by
  intro sameSlot
  apply nonSkin
  exact (MinimalBlocker.endpointSkinEquivalent_iff_eq F left right).mpr <|
    eq_of_same_residual_same_fiberSlot
      F noSunflower left right sameResidual sameSlot

/-- A realized endpoint load over one residual is separated by the derived slot. -/
theorem residualFiberSlot_ne_of_sameResidual_of_load
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameResidual : residual F left = residual F right)
    (load : MinimalBlocker.PrivateWitnessEndpointLoad F left right) :
    residualFiberSlot F noSunflower left ≠
      residualFiberSlot F noSunflower right :=
  residualFiberSlot_ne_of_sameResidual_of_nonSkin
    F noSunflower left right sameResidual load.not_endpointSkin

/-- The concrete private-witness deletion code into parent and local slot. -/
noncomputable def residualSlotCode
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    {x // x ∈ MinimalBlocker.minimalBlocker F} → Finset alpha × Fin k :=
  fun x => (residual F x, residualFiberSlot F noSunflower x)

theorem residualSlotCode_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Function.Injective (residualSlotCode F noSunflower) := by
  intro left right sameCode
  exact eq_of_same_residual_same_fiberSlot F noSunflower left right
    (congrArg Prod.fst sameCode) (congrArg Prod.snd sameCode)

theorem minimalBlocker_card_le_k_mul_residualFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    (MinimalBlocker.minimalBlocker F).card <=
      k * (residualFamily F).edges.card := by
  classical
  have bound := Finset.card_le_mul_card_image
    (f := residual F)
    (MinimalBlocker.minimalBlocker F).attach
    k
    (fun edge edge_mem => by
      have fiber_lt := residualFiber_card_lt F noSunflower edge
      have fiber_le : (residualFiber F edge).card <= k :=
        Nat.le_of_lt fiber_lt
      simpa [residualFiber] using fiber_le)
  simpa [residualFamily] using bound

noncomputable def liftResidualWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (W : Concrete.CorePetalSunflowerWitness k (residualFamily F) core) :
    Concrete.CorePetalSunflowerWitness k F core := by
  let coordinate : Fin k -> {x // x ∈ MinimalBlocker.minimalBlocker F} :=
    fun i => Classical.choose (mem_residualFamily_iff.mp (W.petals_mem i))
  have coordinate_spec : ∀ i : Fin k,
      residual F (coordinate i) = W.petals i := by
    intro i
    exact Classical.choose_spec
      (mem_residualFamily_iff.mp (W.petals_mem i))
  let original : Fin k -> Finset alpha := fun i =>
    MinimalBlocker.privateEdge F (coordinate i)
  have coordinate_injective : Function.Injective coordinate := by
    intro i j sameCoordinate
    apply W.petals_injective
    rw [← coordinate_spec i, ← coordinate_spec j, sameCoordinate]
  exact
    { petals := original
      petals_mem := fun i => MinimalBlocker.privateEdge_mem F (coordinate i)
      petals_injective := by
        intro i j sameEdge
        exact coordinate_injective
          (MinimalBlocker.privateEdge_injective F sameEdge)
      pairwise_intersection := by
        intro i j distinct
        have coordinate_distinct : coordinate i ≠ coordinate j :=
          fun same => distinct (coordinate_injective same)
        rw [show original i = insert (coordinate i).val (W.petals i) by
              rw [← coordinate_spec i]
              exact privateEdge_eq_insert_residual F (coordinate i),
            show original j = insert (coordinate j).val (W.petals j) by
              rw [← coordinate_spec j]
              exact privateEdge_eq_insert_residual F (coordinate j)]
        apply Finset.ext
        intro y
        constructor
        · intro y_mem
          rcases Finset.mem_inter.mp y_mem with ⟨y_left, y_right⟩
          rcases Finset.mem_insert.mp y_left with y_eq_left | y_res_left
          · subst y
            have not_residual : (coordinate i).val ∉ W.petals j := by
              rw [← coordinate_spec j]
              exact blocker_mem_not_mem_residual
                F (coordinate i) (coordinate j)
            exact False.elim <| not_residual <|
              (Finset.mem_insert.mp y_right).resolve_left
                (fun same => coordinate_distinct (Subtype.ext same))
          · rcases Finset.mem_insert.mp y_right with y_eq_right | y_res_right
            · subst y
              have not_residual : (coordinate j).val ∉ W.petals i := by
                rw [← coordinate_spec i]
                exact blocker_mem_not_mem_residual
                  F (coordinate j) (coordinate i)
              exact False.elim (not_residual y_res_left)
            · have y_pair : y ∈ W.petals i ∩ W.petals j :=
                Finset.mem_inter.mpr ⟨y_res_left, y_res_right⟩
              rw [W.pairwise_intersection i j distinct] at y_pair
              exact y_pair
        · intro y_core
          have y_pair : y ∈ W.petals i ∩ W.petals j := by
            rw [W.pairwise_intersection i j distinct]
            exact y_core
          exact Finset.mem_inter.mpr
            ⟨Finset.mem_insert.mpr (Or.inr (Finset.mem_inter.mp y_pair).1),
              Finset.mem_insert.mpr (Or.inr (Finset.mem_inter.mp y_pair).2)⟩ }

theorem hasSunflower_of_residualFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (hasResidualSunflower : Concrete.HasSunflower k (residualFamily F)) :
    Concrete.HasSunflower k F := by
  rcases hasResidualSunflower with ⟨core, ⟨W⟩⟩
  exact ⟨core, ⟨liftResidualWitness W⟩⟩

theorem residualFamily_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Not (Concrete.HasSunflower k (residualFamily F)) :=
  fun hasResidual => noSunflower (hasSunflower_of_residualFamily hasResidual)

end PrivateWitnessReduction
end V2
end SunflowerAASC
