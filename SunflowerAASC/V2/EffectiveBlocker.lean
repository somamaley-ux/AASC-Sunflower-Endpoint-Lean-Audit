import Mathlib.Data.Fintype.BigOperators
import SunflowerAASC.V2.VennSeparation

namespace SunflowerAASC
namespace V2
namespace EffectiveBlocker

/-- The one-point link of an `(r+1)`-uniform family at `x`. -/
def onePointLink
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (x : alpha)
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    Concrete.UniformSetFamily alpha r where
  edges := (F.edges.filter (fun edge => x ∈ edge)).image
    (fun edge => edge.erase x)
  uniform := by
    intro residual hresidual
    rcases Finset.mem_image.mp hresidual with ⟨edge, hedge, rfl⟩
    have edge_mem : edge ∈ F.edges := (Finset.mem_filter.mp hedge).1
    have x_mem : x ∈ edge := (Finset.mem_filter.mp hedge).2
    rw [Finset.card_erase_of_mem x_mem, F.uniform edge edge_mem]
    simp

theorem mem_onePointLink_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {x : alpha}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {residual : Finset alpha} :
    residual ∈ (onePointLink x F).edges <->
      Exists (fun edge : Finset alpha =>
        edge ∈ F.edges /\ x ∈ edge /\ edge.erase x = residual) := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨edge, hedge, heq⟩
    exact ⟨edge, (Finset.mem_filter.mp hedge).1,
      (Finset.mem_filter.mp hedge).2, heq⟩
  · rintro ⟨edge, edge_mem, x_mem, rfl⟩
    exact Finset.mem_image.mpr
      ⟨edge, Finset.mem_filter.mpr ⟨edge_mem, x_mem⟩, rfl⟩

noncomputable def liftOnePointLinkWitness
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {x : alpha}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {core : Finset alpha}
    (W : Concrete.CorePetalSunflowerWitness
      k (onePointLink x F) core) :
    Concrete.CorePetalSunflowerWitness k F (insert x core) := by
  let original : Fin k -> Finset alpha := fun i =>
    Classical.choose (mem_onePointLink_iff.mp (W.petals_mem i))
  have original_spec : forall i : Fin k,
      original i ∈ F.edges /\
      x ∈ original i /\
      (original i).erase x = W.petals i := by
    intro i
    exact Classical.choose_spec
      (mem_onePointLink_iff.mp (W.petals_mem i))
  have original_eq : forall i : Fin k,
      original i = insert x (W.petals i) := by
    intro i
    rw [← (original_spec i).2.2]
    exact (Finset.insert_erase (original_spec i).2.1).symm
  exact
    { petals := original
      petals_mem := fun i => (original_spec i).1
      petals_injective := by
        intro i j hij
        apply W.petals_injective
        rw [← (original_spec i).2.2, ← (original_spec j).2.2, hij]
      pairwise_intersection := by
        intro i j hne
        rw [original_eq i, original_eq j]
        apply Finset.ext
        intro y
        constructor
        · intro hy
          rcases Finset.mem_inter.mp hy with ⟨hyi, hyj⟩
          rcases Finset.mem_insert.mp hyi with hyx | hypi
          · exact Finset.mem_insert.mpr (Or.inl hyx)
          · rcases Finset.mem_insert.mp hyj with _ | hypj
            · exact Finset.mem_insert.mpr (Or.inl (by assumption))
            · exact Finset.mem_insert.mpr (Or.inr <| by
                have : y ∈ W.petals i ∩ W.petals j :=
                  Finset.mem_inter.mpr ⟨hypi, hypj⟩
                rw [W.pairwise_intersection i j hne] at this
                exact this)
        · intro hy
          rcases Finset.mem_insert.mp hy with hyx | hycore
          · exact Finset.mem_inter.mpr
              ⟨Finset.mem_insert.mpr (Or.inl hyx),
                Finset.mem_insert.mpr (Or.inl hyx)⟩
          · have hypair : y ∈ W.petals i ∩ W.petals j := by
              rw [W.pairwise_intersection i j hne]
              exact hycore
            exact Finset.mem_inter.mpr
              ⟨Finset.mem_insert.mpr (Or.inr (Finset.mem_inter.mp hypair).1),
                Finset.mem_insert.mpr (Or.inr (Finset.mem_inter.mp hypair).2)⟩ }

theorem hasSunflower_of_onePointLink
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {x : alpha}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (hasLinkSunflower : Concrete.HasSunflower k (onePointLink x F)) :
    Concrete.HasSunflower k F := by
  rcases hasLinkSunflower with ⟨core, ⟨witness⟩⟩
  exact ⟨insert x core, ⟨liftOnePointLinkWitness witness⟩⟩

theorem onePointLink_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    {x : alpha}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Not (Concrete.HasSunflower k (onePointLink x F)) := by
  exact fun hasLinkSunflower =>
    noSunflower (hasSunflower_of_onePointLink hasLinkSunflower)

/-- A bounded blocker that genuinely hits every edge of a positive-rank family. -/
structure Certificate
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (H : Nat)
    (F : Concrete.UniformSetFamily alpha (r + 1)) where
  blocker : Finset alpha
  blocker_card_le : blocker.card <= H
  hitsEveryEdge :
    forall edge : Finset alpha, edge ∈ F.edges ->
      Exists (fun x : alpha => x ∈ blocker /\ x ∈ edge)

/-- A rank-uniform effective blocker source with bound depending only on `k`. -/
structure RankUniformSource
    (alpha : Type)
    [DecidableEq alpha]
    (k H : Nat) where
  H_positive : 0 < H
  certificate :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      Not (Concrete.HasSunflower k F) -> Certificate H F

/--
A bounded blocker source only for a quantitative countercase. Sparse families
already satisfy the target bound and do not need literal blocker compression.
-/
structure DenseCountercaseSource
    (alpha : Type)
    [DecidableEq alpha]
    (k H : Nat) where
  certificate :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall _noSunflower : Not (Concrete.HasSunflower k F),
      H ^ (r + 1) < F.edges.card -> Certificate H F

theorem Certificate.edges_eq_biUnion_filters
    {alpha : Type}
    [DecidableEq alpha]
    {r H : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (Cert : Certificate H F) :
    F.edges = Cert.blocker.biUnion
      (fun x => F.edges.filter (fun edge => x ∈ edge)) := by
  apply Finset.ext
  intro edge
  constructor
  · intro edge_mem
    rcases Cert.hitsEveryEdge edge edge_mem with ⟨x, x_mem, x_edge⟩
    exact Finset.mem_biUnion.mpr
      ⟨x, x_mem, Finset.mem_filter.mpr ⟨edge_mem, x_edge⟩⟩
  · intro edge_mem
    rcases Finset.mem_biUnion.mp edge_mem with ⟨x, _, hfilter⟩
    exact (Finset.mem_filter.mp hfilter).1

theorem filter_card_eq_onePointLink_card
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (x : alpha)
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    (F.edges.filter (fun edge => x ∈ edge)).card =
      (onePointLink x F).edges.card := by
  change (F.edges.filter (fun edge => x ∈ edge)).card =
    ((F.edges.filter (fun edge => x ∈ edge)).image
      (fun edge => edge.erase x)).card
  symm
  apply Finset.card_image_of_injOn
  intro left hleft right hright sameErase
  have x_left : x ∈ left := (Finset.mem_filter.mp hleft).2
  have x_right : x ∈ right := (Finset.mem_filter.mp hright).2
  change left.erase x = right.erase x at sameErase
  calc
    left = insert x (left.erase x) := (Finset.insert_erase x_left).symm
    _ = insert x (right.erase x) := congrArg (insert x) sameErase
    _ = right := Finset.insert_erase x_right

theorem family_card_le_pow
    {alpha : Type}
    [DecidableEq alpha]
    {k H : Nat}
    (Src : RankUniformSource alpha k H) :
    forall n : Nat,
      forall F : Concrete.UniformSetFamily alpha n,
      Not (Concrete.HasSunflower k F) ->
      F.edges.card <= H ^ n := by
  intro n
  induction n with
  | zero =>
      intro F _
      have edges_subset : F.edges ⊆ ({∅} : Finset (Finset alpha)) := by
        intro edge edge_mem
        have edge_card_zero : edge.card = 0 := F.uniform edge edge_mem
        have edge_empty : edge = ∅ := Finset.card_eq_zero.mp edge_card_zero
        simp [edge_empty]
      simpa using Finset.card_le_card edges_subset
  | succ r ih =>
      intro F noSunflower
      let Cert := Src.certificate r F noSunflower
      calc
        F.edges.card
            = (Cert.blocker.biUnion
                (fun x => F.edges.filter (fun edge => x ∈ edge))).card := by
              rw [← Cert.edges_eq_biUnion_filters]
        _ <= ∑ x ∈ Cert.blocker,
              (F.edges.filter (fun edge => x ∈ edge)).card := by
              exact Finset.card_biUnion_le
        _ = ∑ x ∈ Cert.blocker, (onePointLink x F).edges.card := by
              apply Finset.sum_congr rfl
              intro x _
              exact filter_card_eq_onePointLink_card x F
        _ <= ∑ _x ∈ Cert.blocker, H ^ r := by
              apply Finset.sum_le_sum
              intro x _
              exact ih (onePointLink x F)
                (onePointLink_noSunflower noSunflower)
        _ = Cert.blocker.card * H ^ r := by simp
        _ <= H * H ^ r := Nat.mul_le_mul_right (H ^ r) Cert.blocker_card_le
        _ = H ^ (r + 1) := by
              rw [Nat.pow_succ]
              exact Nat.mul_comm H (H ^ r)

theorem sunflower_of_card_gt_pow
    {alpha : Type}
    [DecidableEq alpha]
    {n k H : Nat}
    (Src : RankUniformSource alpha k H)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess : H ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  by_contra noSunflower
  exact Nat.not_lt_of_ge
    (family_card_le_pow Src n F noSunflower)
    sizeExcess

theorem family_card_le_pow_of_denseCountercaseSource
    {alpha : Type}
    [DecidableEq alpha]
    {k H : Nat}
    (Src : DenseCountercaseSource alpha k H) :
    forall n : Nat,
      forall F : Concrete.UniformSetFamily alpha n,
      Not (Concrete.HasSunflower k F) ->
      F.edges.card <= H ^ n := by
  intro n
  induction n with
  | zero =>
      intro F _
      have edges_subset : F.edges ⊆ ({∅} : Finset (Finset alpha)) := by
        intro edge edge_mem
        have edge_card_zero : edge.card = 0 := F.uniform edge edge_mem
        have edge_empty : edge = ∅ := Finset.card_eq_zero.mp edge_card_zero
        simp [edge_empty]
      simpa using Finset.card_le_card edges_subset
  | succ r ih =>
      intro F noSunflower
      by_cases alreadyBounded : F.edges.card <= H ^ (r + 1)
      · exact alreadyBounded
      · have sizeExcess : H ^ (r + 1) < F.edges.card :=
          Nat.lt_of_not_ge alreadyBounded
        let Cert := Src.certificate r F noSunflower sizeExcess
        calc
          F.edges.card
              = (Cert.blocker.biUnion
                  (fun x => F.edges.filter (fun edge => x ∈ edge))).card := by
                rw [← Cert.edges_eq_biUnion_filters]
          _ <= ∑ x ∈ Cert.blocker,
                (F.edges.filter (fun edge => x ∈ edge)).card := by
                exact Finset.card_biUnion_le
          _ = ∑ x ∈ Cert.blocker, (onePointLink x F).edges.card := by
                apply Finset.sum_congr rfl
                intro x _
                exact filter_card_eq_onePointLink_card x F
          _ <= ∑ _x ∈ Cert.blocker, H ^ r := by
                apply Finset.sum_le_sum
                intro x _
                exact ih (onePointLink x F)
                  (onePointLink_noSunflower noSunflower)
          _ = Cert.blocker.card * H ^ r := by simp
          _ <= H * H ^ r :=
                Nat.mul_le_mul_right (H ^ r) Cert.blocker_card_le
          _ = H ^ (r + 1) := by
                rw [Nat.pow_succ]
                exact Nat.mul_comm H (H ^ r)

theorem sunflower_of_card_gt_pow_of_denseCountercaseSource
    {alpha : Type}
    [DecidableEq alpha]
    {n k H : Nat}
    (Src : DenseCountercaseSource alpha k H)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess : H ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  by_contra noSunflower
  exact Nat.not_lt_of_ge
    (family_card_le_pow_of_denseCountercaseSource Src n F noSunflower)
    sizeExcess

noncomputable def emptyCoreMaximalMatching
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) :
    Concrete.MaximalFiniteCoreLinkMatching F (∅ : Finset alpha) :=
  Concrete.maximalFiniteCoreLinkMatching F ∅

noncomputable def canonicalRawBlocker
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1)) : Finset alpha :=
  (emptyCoreMaximalMatching F).matching.rawBlocker

theorem canonicalRawBlocker_hitsEveryEdge
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    {edge : Finset alpha}
    (edge_mem : edge ∈ F.edges) :
    Not (Disjoint edge (canonicalRawBlocker F)) := by
  have edge_live : (edge \ (∅ : Finset alpha)).Nonempty := by
    simp only [Finset.sdiff_empty]
    apply Finset.card_pos.mp
    rw [F.uniform edge edge_mem]
    simp
  simpa [canonicalRawBlocker] using
    (emptyCoreMaximalMatching F).hits_link_petals
      edge_mem
      (Finset.empty_subset edge)
      edge_live

theorem canonicalRawBlocker_card_le_rank_bound
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    (canonicalRawBlocker F).card <= k * (r + 1) := by
  change (emptyCoreMaximalMatching F).matching.rawBlocker.card <= k * (r + 1)
  exact (emptyCoreMaximalMatching F).matching.rawBlocker_card_le_k_mul_rank
    noSunflower

theorem canonicalRawBlocker_card_le_erdosRado_rank_bound
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    (canonicalRawBlocker F).card <= (k - 1) * (r + 1) := by
  change
    (emptyCoreMaximalMatching F).matching.rawBlocker.card <=
      (k - 1) * (r + 1)
  exact
    (emptyCoreMaximalMatching F).matching.rawBlocker_card_le_pred_mul_rank
      noSunflower

/-- The canonical maximal matching gives the classical rank-sized blocker. -/
noncomputable def canonicalRawCertificate
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Certificate (k * (r + 1)) F where
  blocker := canonicalRawBlocker F
  blocker_card_le := canonicalRawBlocker_card_le_rank_bound F noSunflower
  hitsEveryEdge := by
    intro edge edge_mem
    rcases Finset.not_disjoint_iff.mp
        (canonicalRawBlocker_hitsEveryEdge F edge_mem) with
      ⟨x, x_edge, x_blocker⟩
    exact ⟨x, x_blocker, x_edge⟩

/-- The sharp classical certificate keeps the strict matching bound as `k - 1`. -/
noncomputable def canonicalErdosRadoCertificate
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Certificate ((k - 1) * (r + 1)) F where
  blocker := canonicalRawBlocker F
  blocker_card_le :=
    canonicalRawBlocker_card_le_erdosRado_rank_bound F noSunflower
  hitsEveryEdge := by
    intro edge edge_mem
    rcases Finset.not_disjoint_iff.mp
        (canonicalRawBlocker_hitsEveryEdge F edge_mem) with
      ⟨x, x_edge, x_blocker⟩
    exact ⟨x, x_blocker, x_edge⟩

/--
The concrete maximal-blocker recurrence, without constant-fiber compression,
gives the classical factorial sunflower bound.
-/
theorem family_card_le_classicalFactorial
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat} :
    forall n : Nat,
      forall F : Concrete.UniformSetFamily alpha n,
      Not (Concrete.HasSunflower k F) ->
      F.edges.card <= k ^ n * n.factorial := by
  intro n
  induction n with
  | zero =>
      intro F _
      have edges_subset : F.edges ⊆ ({∅} : Finset (Finset alpha)) := by
        intro edge edge_mem
        have edge_card_zero : edge.card = 0 := F.uniform edge edge_mem
        have edge_empty : edge = ∅ := Finset.card_eq_zero.mp edge_card_zero
        simp [edge_empty]
      simpa using Finset.card_le_card edges_subset
  | succ r ih =>
      intro F noSunflower
      let Cert := canonicalRawCertificate F noSunflower
      calc
        F.edges.card
            = (Cert.blocker.biUnion
                (fun x => F.edges.filter (fun edge => x ∈ edge))).card := by
              rw [← Cert.edges_eq_biUnion_filters]
        _ <= ∑ x ∈ Cert.blocker,
              (F.edges.filter (fun edge => x ∈ edge)).card := by
              exact Finset.card_biUnion_le
        _ = ∑ x ∈ Cert.blocker, (onePointLink x F).edges.card := by
              apply Finset.sum_congr rfl
              intro x _
              exact filter_card_eq_onePointLink_card x F
        _ <= ∑ _x ∈ Cert.blocker, k ^ r * r.factorial := by
              apply Finset.sum_le_sum
              intro x _
              exact ih (onePointLink x F)
                (onePointLink_noSunflower noSunflower)
        _ = Cert.blocker.card * (k ^ r * r.factorial) := by simp
        _ <= (k * (r + 1)) * (k ^ r * r.factorial) :=
              Nat.mul_le_mul_right (k ^ r * r.factorial)
                Cert.blocker_card_le
        _ = k ^ (r + 1) * (r + 1).factorial := by
              rw [Nat.pow_succ, Nat.factorial_succ]
              ac_rfl

/-- The standard Erdős-Rado factorial bound `|F| <= (k - 1)^n * n!`. -/
theorem family_card_le_erdosRadoFactorial
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat} :
    forall n : Nat,
      forall F : Concrete.UniformSetFamily alpha n,
      Not (Concrete.HasSunflower k F) ->
      F.edges.card <= (k - 1) ^ n * n.factorial := by
  intro n
  induction n with
  | zero =>
      intro F _
      have edges_subset : F.edges ⊆ ({∅} : Finset (Finset alpha)) := by
        intro edge edge_mem
        have edge_card_zero : edge.card = 0 := F.uniform edge edge_mem
        have edge_empty : edge = ∅ := Finset.card_eq_zero.mp edge_card_zero
        simp [edge_empty]
      simpa using Finset.card_le_card edges_subset
  | succ r ih =>
      intro F noSunflower
      let Cert := canonicalErdosRadoCertificate F noSunflower
      calc
        F.edges.card
            = (Cert.blocker.biUnion
                (fun x => F.edges.filter (fun edge => x ∈ edge))).card := by
              rw [← Cert.edges_eq_biUnion_filters]
        _ <= ∑ x ∈ Cert.blocker,
              (F.edges.filter (fun edge => x ∈ edge)).card := by
              exact Finset.card_biUnion_le
        _ = ∑ x ∈ Cert.blocker, (onePointLink x F).edges.card := by
              apply Finset.sum_congr rfl
              intro x _
              exact filter_card_eq_onePointLink_card x F
        _ <= ∑ _x ∈ Cert.blocker, (k - 1) ^ r * r.factorial := by
              apply Finset.sum_le_sum
              intro x _
              exact ih (onePointLink x F)
                (onePointLink_noSunflower noSunflower)
        _ = Cert.blocker.card * ((k - 1) ^ r * r.factorial) := by simp
        _ <= ((k - 1) * (r + 1)) * ((k - 1) ^ r * r.factorial) :=
              Nat.mul_le_mul_right ((k - 1) ^ r * r.factorial)
                Cert.blocker_card_le
        _ = (k - 1) ^ (r + 1) * (r + 1).factorial := by
              rw [Nat.pow_succ, Nat.factorial_succ]
              ac_rfl

theorem sunflower_of_card_gt_erdosRadoFactorial
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess : (k - 1) ^ n * n.factorial < F.edges.card) :
    Concrete.HasSunflower k F := by
  by_contra noSunflower
  exact Nat.not_lt_of_ge
    (family_card_le_erdosRadoFactorial n F noSunflower)
    sizeExcess

theorem sunflower_of_card_gt_classicalFactorial
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess : k ^ n * n.factorial < F.edges.card) :
    Concrete.HasSunflower k F := by
  by_contra noSunflower
  exact Nat.not_lt_of_ge
    (family_card_le_classicalFactorial n F noSunflower)
    sizeExcess

/--
Venn compression of the concrete maximal raw blocker.  The effective blocker
is an actual subset of raw coordinates, its code is injective, and every raw
hit is preserved by an effective representative.
-/
structure VennCompressedBlocker
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (layerCount fiberBound : Nat)
    (F : Concrete.UniformSetFamily alpha (r + 1)) where
  effectiveBlocker : Finset alpha
  effective_subset_raw : effectiveBlocker ⊆ canonicalRawBlocker F
  code :
    {x // x ∈ effectiveBlocker} ->
      VennSeparation.VennCellCode layerCount fiberBound
  code_injective : Function.Injective code
  preservesRawHits :
    forall edge : Finset alpha, edge ∈ F.edges ->
      Not (Disjoint edge (canonicalRawBlocker F)) ->
      Not (Disjoint edge effectiveBlocker)

theorem VennCompressedBlocker.effective_card_le
    {alpha : Type}
    [DecidableEq alpha]
    {r layerCount fiberBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (Compression : VennCompressedBlocker layerCount fiberBound F) :
    Compression.effectiveBlocker.card <=
      VennSeparation.vennAlphabetSize layerCount fiberBound := by
  have hcard := Fintype.card_le_of_injective
    Compression.code
    Compression.code_injective
  simpa [VennSeparation.vennCellCode_card] using hcard

def VennCompressedBlocker.toCertificate
    {alpha : Type}
    [DecidableEq alpha]
    {r layerCount fiberBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (Compression : VennCompressedBlocker layerCount fiberBound F) :
    Certificate
      (VennSeparation.vennAlphabetSize layerCount fiberBound) F where
  blocker := Compression.effectiveBlocker
  blocker_card_le := Compression.effective_card_le
  hitsEveryEdge := by
    intro edge edge_mem
    have effectiveHit :
        Not (Disjoint edge Compression.effectiveBlocker) :=
      Compression.preservesRawHits edge edge_mem
        (canonicalRawBlocker_hitsEveryEdge F edge_mem)
    rcases Finset.not_disjoint_iff.mp effectiveHit with ⟨x, x_edge, x_blocker⟩
    exact ⟨x, x_blocker, x_edge⟩

/-- Uniform Venn compression of canonical maximal blockers at every rank. -/
structure RankUniformVennCompressionSource
    (alpha : Type)
    [DecidableEq alpha]
    (k layerCount fiberBound : Nat) where
  fiberBound_positive : 0 < fiberBound
  compress :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      Not (Concrete.HasSunflower k F) ->
      VennCompressedBlocker layerCount fiberBound F

def RankUniformVennCompressionSource.toEffectiveBlockerSource
    {alpha : Type}
    [DecidableEq alpha]
    {k layerCount fiberBound : Nat}
    (Src : RankUniformVennCompressionSource
      alpha k layerCount fiberBound) :
    RankUniformSource alpha k
      (VennSeparation.vennAlphabetSize layerCount fiberBound) where
  H_positive := VennSeparation.vennAlphabetSize_positive
    Src.fiberBound_positive
  certificate := fun r F noSunflower =>
    (Src.compress r F noSunflower).toCertificate

theorem sunflower_of_uniformVennBlockerCompression
    {alpha : Type}
    [DecidableEq alpha]
    {n k layerCount fiberBound : Nat}
    (Src : RankUniformVennCompressionSource
      alpha k layerCount fiberBound)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      VennSeparation.vennAlphabetSize layerCount fiberBound ^ n <
        F.edges.card) :
    Concrete.HasSunflower k F := by
  exact sunflower_of_card_gt_pow
    Src.toEffectiveBlockerSource
    F
    sizeExcess

end EffectiveBlocker
end V2
end SunflowerAASC
