import Std

namespace SunflowerAASC
namespace V2
namespace FiniteCombinatorics

/-- Two finite petals intersect when they share an element. -/
def Intersects {α : Type u} (a b : List α) : Prop :=
  ∃ x, x ∈ a ∧ x ∈ b

/-- A finite petal is live when it is nonempty. -/
def LivePetal {α : Type u} (p : List α) : Prop :=
  ∃ x, x ∈ p

/-- A matching is a finite family whose distinct petals are pairwise disjoint. -/
def Matching {α : Type u} (M : List (List α)) : Prop :=
  ∀ {a b}, a ∈ M -> b ∈ M -> a ≠ b -> Not (Intersects a b)

theorem Matching.take
    {α : Type u}
    {M : List (List α)}
    (H : Matching M)
    (k : Nat) :
    Matching (M.take k) := by
  intro a b ha hb hne
  exact H (List.mem_of_mem_take ha) (List.mem_of_mem_take hb) hne

theorem exactSubmatching_of_length_ge
    {α : Type u}
    {M : List (List α)}
    {k : Nat}
    (H : Matching M)
    (hge : k <= M.length) :
    ∃ N : List (List α), Matching N ∧ N.length = k := by
  exact ⟨M.take k, H.take k, List.length_take_of_le hge⟩

def HasMatchingOfArity {α : Type u} (L : List (List α)) (k : Nat) : Prop :=
  ∃ M : List (List α), Matching M ∧ M.length = k ∧ ∀ {p}, p ∈ M -> p ∈ L

def NoMatchingOfArity {α : Type u} (L : List (List α)) (k : Nat) : Prop :=
  ¬ HasMatchingOfArity L k

theorem hasMatchingOfArity_of_matching_length_ge
    {α : Type u}
    {L M : List (List α)}
    {k : Nat}
    (hSub : ∀ {p}, p ∈ M -> p ∈ L)
    (H : Matching M)
    (hge : k <= M.length) :
    HasMatchingOfArity L k := by
  refine ⟨M.take k, H.take k, List.length_take_of_le hge, ?_⟩
  intro p hp
  exact hSub (List.mem_of_mem_take hp)

theorem matching_length_lt_of_noMatchingOfArity
    {α : Type u}
    {L M : List (List α)}
    {k : Nat}
    (hNo : NoMatchingOfArity L k)
    (hSub : ∀ {p}, p ∈ M -> p ∈ L)
    (H : Matching M) :
    M.length < k := by
  exact Nat.lt_of_not_ge (fun hge =>
    hNo (hasMatchingOfArity_of_matching_length_ge hSub H hge))

/--
Relation-parametric matching.  This is the correct finite layer when the
notion of conflict is geometric rather than literal list overlap.
-/
def RelMatching {α : Type u} (R : α -> α -> Prop) (M : List α) : Prop :=
  ∀ {a b}, a ∈ M -> b ∈ M -> a ≠ b -> ¬ R a b

theorem RelMatching.take
    {α : Type u}
    {R : α -> α -> Prop}
    {M : List α}
    (H : RelMatching R M)
    (k : Nat) :
    RelMatching R (M.take k) := by
  intro a b ha hb hne
  exact H (List.mem_of_mem_take ha) (List.mem_of_mem_take hb) hne

def RelHasMatchingOfArity
    {α : Type u}
    (R : α -> α -> Prop)
    (L : List α)
    (k : Nat) : Prop :=
  ∃ M : List α, RelMatching R M ∧ M.length = k ∧ ∀ {p}, p ∈ M -> p ∈ L

def RelNoMatchingOfArity
    {α : Type u}
    (R : α -> α -> Prop)
    (L : List α)
    (k : Nat) : Prop :=
  ¬ RelHasMatchingOfArity R L k

theorem relHasMatchingOfArity_of_length_ge
    {α : Type u}
    {R : α -> α -> Prop}
    {L M : List α}
    {k : Nat}
    (hSub : ∀ {p}, p ∈ M -> p ∈ L)
    (H : RelMatching R M)
    (hge : k <= M.length) :
    RelHasMatchingOfArity R L k := by
  refine ⟨M.take k, H.take k, List.length_take_of_le hge, ?_⟩
  intro p hp
  exact hSub (List.mem_of_mem_take hp)

theorem relMatching_length_lt_of_noMatchingOfArity
    {α : Type u}
    {R : α -> α -> Prop}
    {L M : List α}
    {k : Nat}
    (hNo : RelNoMatchingOfArity R L k)
    (hSub : ∀ {p}, p ∈ M -> p ∈ L)
    (H : RelMatching R M) :
    M.length < k := by
  exact Nat.lt_of_not_ge (fun hge =>
    hNo (relHasMatchingOfArity_of_length_ge hSub H hge))

/-- Relation-parametric maximal matching: every live link item is either in the
matching or conflicts with a matching member. -/
def RelMaximalMatchingIn
    {α : Type u}
    (R : α -> α -> Prop)
    (L M : List α) : Prop :=
  (∀ {p}, p ∈ M -> p ∈ L) /\
  RelMatching R M /\
  (∀ {p}, p ∈ L -> p ∈ M \/ ∃ m, m ∈ M ∧ R p m)

theorem relMaximalMatching_hits
    {α : Type u}
    {R : α -> α -> Prop}
    {L M : List α}
    (H : RelMaximalMatchingIn R L M) :
    ∀ {p}, p ∈ L -> p ∈ M \/ ∃ m, m ∈ M ∧ R p m := by
  exact H.2.2

structure RelRawBlockerNormalForm
    {α : Type u}
    (R : α -> α -> Prop)
    (L M : List α)
    (k : Nat) where
  maximal : RelMaximalMatchingIn R L M
  noMatching : RelNoMatchingOfArity R L k

theorem RelRawBlockerNormalForm.matchingSize_lt
    {α : Type u}
    {R : α -> α -> Prop}
    {L M : List α}
    {k : Nat}
    (N : RelRawBlockerNormalForm R L M k) :
    M.length < k := by
  exact relMatching_length_lt_of_noMatchingOfArity
    N.noMatching
    N.maximal.1
    N.maximal.2.1

/--
`M` is maximal in `L` when every petal of `M` lies in `L`, `M` is a matching,
and every petal of `L` is either already in `M` or intersects a member of `M`.
-/
def MaximalMatchingIn {α : Type u} (L M : List (List α)) : Prop :=
  (∀ {p}, p ∈ M -> p ∈ L) /\
  Matching M /\
  (∀ {p}, p ∈ L -> p ∈ M \/ ∃ m, m ∈ M ∧ Intersects p m)

/-- The raw blocker is the union of all petals in the maximal matching. -/
def rawBlocker {α : Type u} (M : List (List α)) : List α :=
  M.flatten

theorem mem_rawBlocker_of_mem_member
    {α : Type u}
    {x : α}
    {m : List α}
    {M : List (List α)}
    (hx : x ∈ m)
    (hm : m ∈ M) :
    x ∈ rawBlocker M := by
  simpa [rawBlocker] using Exists.intro m (And.intro hm hx)

theorem maximalMatching_rawBlocker_hits_live_petals
    {α : Type u}
    {L M : List (List α)}
    (H : MaximalMatchingIn L M) :
    ∀ {p}, p ∈ L -> LivePetal p -> Intersects (rawBlocker M) p := by
  intro p hp hlive
  rcases H.2.2 hp with hmem | hinter
  · rcases hlive with ⟨x, hx⟩
    exact ⟨x, mem_rawBlocker_of_mem_member hx hmem, hx⟩
  · rcases hinter with ⟨m, hm, x, hp_x, hm_x⟩
    exact ⟨x, mem_rawBlocker_of_mem_member hm_x hm, hp_x⟩

theorem rawBlocker_length_le_of_member_length_le
    {α : Type u}
    {M : List (List α)}
    {r : Nat}
    (h : ∀ {m}, m ∈ M -> m.length <= r) :
    (rawBlocker M).length <= M.length * r := by
  induction M with
  | nil =>
      simp [rawBlocker]
  | cons head tail ih =>
      have hhead : head.length <= r := h (by simp)
      have htail : ∀ {m}, m ∈ tail -> m.length <= r := by
        intro m hm
        exact h (by simp [hm])
      calc
        (rawBlocker (head :: tail)).length
            = head.length + (rawBlocker tail).length := by
              simp [rawBlocker]
        _ <= r + tail.length * r :=
              Nat.add_le_add hhead (ih htail)
        _ = (head :: tail).length * r := by
              simp [Nat.succ_mul, Nat.add_comm]

theorem rawBlocker_length_le_of_matching_size_lt
    {α : Type u}
    {M : List (List α)}
    {r k : Nat}
    (hRank : ∀ {m}, m ∈ M -> m.length <= r)
    (hSize : M.length < k) :
    (rawBlocker M).length <= k * r := by
  calc
    (rawBlocker M).length <= M.length * r :=
      rawBlocker_length_le_of_member_length_le hRank
    _ <= k * r :=
      Nat.mul_le_mul_right r (Nat.le_of_lt hSize)

def LinkRankBound {α : Type u} (L : List (List α)) (r : Nat) : Prop :=
  ∀ {p}, p ∈ L -> p.length <= r

theorem rawBlocker_length_le_of_link_rank_bound
    {α : Type u}
    {L M : List (List α)}
    {r k : Nat}
    (H : MaximalMatchingIn L M)
    (hRank : LinkRankBound L r)
    (hSize : M.length < k) :
    (rawBlocker M).length <= k * r := by
  exact rawBlocker_length_le_of_matching_size_lt
    (fun hm => hRank (H.1 hm))
    hSize

/--
Classical raw-blocker normal form for one finite link.  It deliberately records
the rank-dependent size bound that v2 later replaces by role/fiber counting.
-/
structure ClassicalRawBlockerNormalForm
    {α : Type u}
    (L M : List (List α))
    (k r : Nat) where
  maximal : MaximalMatchingIn L M
  linkRankBound : LinkRankBound L r
  matchingSize_lt : M.length < k

def ClassicalRawBlockerNormalForm.ofNoMatching
    {α : Type u}
    {L M : List (List α)}
    {k r : Nat}
    (H : MaximalMatchingIn L M)
    (hRank : LinkRankBound L r)
    (hNo : NoMatchingOfArity L k) :
    ClassicalRawBlockerNormalForm L M k r :=
  { maximal := H
    linkRankBound := hRank
    matchingSize_lt :=
      matching_length_lt_of_noMatchingOfArity hNo H.1 H.2.1 }

theorem ClassicalRawBlockerNormalForm.hits_live_petals
    {α : Type u}
    {L M : List (List α)}
    {k r : Nat}
    (N : ClassicalRawBlockerNormalForm L M k r) :
    ∀ {p}, p ∈ L -> LivePetal p -> Intersects (rawBlocker M) p := by
  exact maximalMatching_rawBlocker_hits_live_petals N.maximal

theorem ClassicalRawBlockerNormalForm.rawBlocker_size_le
    {α : Type u}
    {L M : List (List α)}
    {k r : Nat}
    (N : ClassicalRawBlockerNormalForm L M k r) :
    (rawBlocker M).length <= k * r := by
  exact rawBlocker_length_le_of_link_rank_bound
    N.maximal
    N.linkRankBound
    N.matchingSize_lt

/--
This is the concrete classical output used by the v2 architecture: maximal
matching produces a raw blocker.  The v2 compactness work starts after this,
by replacing raw coordinates with role-distinct blocker quotient classes.
-/
structure RawBlockerOutput {α : Type u} (L M : List (List α)) where
  maximal : MaximalMatchingIn L M
  hitsLivePetals :
    ∀ {p}, p ∈ L -> LivePetal p -> Intersects (rawBlocker M) p

def rawBlockerOutputOfMaximalMatching
    {α : Type u}
    {L M : List (List α)}
    (H : MaximalMatchingIn L M) :
    RawBlockerOutput L M :=
  { maximal := H
    hitsLivePetals := maximalMatching_rawBlocker_hits_live_petals H }

end FiniteCombinatorics
end V2
end SunflowerAASC
