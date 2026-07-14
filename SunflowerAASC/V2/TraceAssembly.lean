import SunflowerAASC.V2.WitnessCompression

namespace SunflowerAASC
namespace V2
namespace TraceAssembly

/--
A rank-deletion system.  At each successor rank, one finite type code and the
predecessor state jointly determine the current state.
-/
structure RankDeletionSystem (Qk : Nat) where
  State : Nat -> Type
  baseSubsingleton : forall left right : State 0, left = right
  headCode : forall r : Nat, State (r + 1) -> Fin Qk
  predecessor : forall r : Nat, State (r + 1) -> State r
  step_injective :
    forall r : Nat,
      Function.Injective (fun state : State (r + 1) =>
        (headCode r state, predecessor r state))

def RankDeletionSystem.trace
    {Qk : Nat}
    (System : RankDeletionSystem Qk) :
    forall r : Nat, System.State r -> (Fin r -> Fin Qk)
  | 0, _ => fun i => Fin.elim0 i
  | r + 1, state =>
      Fin.cases
        (System.headCode r state)
        (System.trace r (System.predecessor r state))

theorem RankDeletionSystem.trace_injective
    {Qk : Nat}
    (System : RankDeletionSystem Qk) :
    forall r : Nat, Function.Injective (System.trace r) := by
  intro r
  induction r with
  | zero =>
      intro left right _
      exact System.baseSubsingleton left right
  | succ r ih =>
      intro left right sameTrace
      apply System.step_injective r
      apply Prod.ext
      · have hzero := congrFun sameTrace (0 : Fin (r + 1))
        simpa [RankDeletionSystem.trace] using hzero
      · apply ih
        funext i
        have hsucc := congrFun sameTrace i.succ
        simpa [RankDeletionSystem.trace] using hsucc

/-- A rank-deletion system whose top states encode the members of one family. -/
structure FamilyRankDeletionSystem
    {alpha : Type}
    [DecidableEq alpha]
    {n Qk : Nat}
    (F : Concrete.UniformSetFamily alpha n) where
  system : RankDeletionSystem Qk
  topState : {edge // edge ∈ F.edges} -> system.State n
  topState_injective : Function.Injective topState

def FamilyRankDeletionSystem.toTypeTraceCoding
    {alpha : Type}
    [DecidableEq alpha]
    {n Qk : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    (System : FamilyRankDeletionSystem (Qk := Qk) F) :
    RolePopulation.AASCTypeTraceCoding (Qk := Qk) F where
  trace := fun edge => System.system.trace n (System.topState edge)
  trace_injective :=
    (System.system.trace_injective n).comp System.topState_injective

theorem FamilyRankDeletionSystem.family_card_le_type_pow_rank
    {alpha : Type}
    [DecidableEq alpha]
    {n Qk : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    (System : FamilyRankDeletionSystem (Qk := Qk) F) :
    F.edges.card <= Qk ^ n := by
  exact System.toTypeTraceCoding.family_card_le_type_pow_rank

/-- Uniform rank-deletion systems for all no-sunflower families. -/
structure KernelFaithfulRankDeletionSource
    (alpha : Type)
    [DecidableEq alpha]
    (n k Qk : Nat) where
  Qk_positive : 0 < Qk
  roleOfType : Fin Qk -> AASCBlockerRole
  deletionSystem :
    forall F : Concrete.UniformSetFamily alpha n,
      Not (Concrete.HasSunflower k F) ->
      FamilyRankDeletionSystem (Qk := Qk) F

def KernelFaithfulRankDeletionSource.toTypeTraceSource
    {alpha : Type}
    [DecidableEq alpha]
    {n k Qk : Nat}
    (Src : KernelFaithfulRankDeletionSource alpha n k Qk) :
    RolePopulation.KernelFaithfulTypeTraceSource alpha n k Qk where
  Qk_positive := Src.Qk_positive
  roleOfType := Src.roleOfType
  traceCoding := fun F noSunflower =>
    (Src.deletionSystem F noSunflower).toTypeTraceCoding

theorem sunflower_of_rankDeletionSystem
    {alpha : Type}
    [DecidableEq alpha]
    {n k Qk : Nat}
    (Src : KernelFaithfulRankDeletionSource alpha n k Qk)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess : Qk ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  exact RolePopulation.sunflower_of_card_gt_type_pow_rank
    Src.toTypeTraceSource
    F
    sizeExcess

abbrev FinsetRankState
    (alpha : Type)
    [DecidableEq alpha]
    (r : Nat) :=
  {edge : Finset alpha // edge.card = r}

/--
Concrete one-coordinate deletion data.  Equal predecessor and equal true-type
code force equality of the deleted coordinates.
-/
structure FinsetTypeDeletionCoding
    (alpha : Type)
    [DecidableEq alpha]
    (Qk : Nat) where
  chosen : forall r : Nat, FinsetRankState alpha (r + 1) -> alpha
  chosen_mem :
    forall r : Nat, forall state : FinsetRankState alpha (r + 1),
      chosen r state ∈ state.val
  typeCode : forall r : Nat, FinsetRankState alpha (r + 1) -> Fin Qk
  collision :
    forall r : Nat,
      forall left right : FinsetRankState alpha (r + 1),
      typeCode r left = typeCode r right ->
      left.val.erase (chosen r left) = right.val.erase (chosen r right) ->
      chosen r left = chosen r right

def FinsetTypeDeletionCoding.predecessor
    {alpha : Type}
    [DecidableEq alpha]
    {Qk : Nat}
    (Coding : FinsetTypeDeletionCoding alpha Qk)
    (r : Nat)
    (state : FinsetRankState alpha (r + 1)) :
    FinsetRankState alpha r :=
  ⟨state.val.erase (Coding.chosen r state), by
    rw [Finset.card_erase_of_mem (Coding.chosen_mem r state)]
    simp [state.property]⟩

def FinsetTypeDeletionCoding.toRankDeletionSystem
    {alpha : Type}
    [DecidableEq alpha]
    {Qk : Nat}
    (Coding : FinsetTypeDeletionCoding alpha Qk) :
    RankDeletionSystem Qk where
  State := FinsetRankState alpha
  baseSubsingleton := by
    intro left right
    apply Subtype.ext
    exact Finset.card_eq_zero.mp left.property |>.trans
      (Finset.card_eq_zero.mp right.property).symm
  headCode := Coding.typeCode
  predecessor := Coding.predecessor
  step_injective := by
    intro r left right hpair
    have hcode : Coding.typeCode r left = Coding.typeCode r right :=
      congrArg Prod.fst hpair
    have hpredecessor :
        left.val.erase (Coding.chosen r left) =
          right.val.erase (Coding.chosen r right) :=
      congrArg Subtype.val (congrArg Prod.snd hpair)
    have hchosen : Coding.chosen r left = Coding.chosen r right :=
      Coding.collision r left right hcode hpredecessor
    apply Subtype.ext
    calc
      left.val = insert (Coding.chosen r left)
          (left.val.erase (Coding.chosen r left)) :=
        (Finset.insert_erase (Coding.chosen_mem r left)).symm
      _ = insert (Coding.chosen r right)
          (right.val.erase (Coding.chosen r right)) := by
        exact congrArg₂ (fun x s => insert x s) hchosen hpredecessor
      _ = right.val := Finset.insert_erase (Coding.chosen_mem r right)

def FinsetTypeDeletionCoding.familyRankDeletionSystem
    {alpha : Type}
    [DecidableEq alpha]
    {n Qk : Nat}
    (Coding : FinsetTypeDeletionCoding alpha Qk)
    (F : Concrete.UniformSetFamily alpha n) :
    FamilyRankDeletionSystem (Qk := Qk) F where
  system := Coding.toRankDeletionSystem
  topState := fun edge =>
    ⟨edge.val, F.uniform edge.val edge.property⟩
  topState_injective := by
    intro left right h
    apply Subtype.ext
    exact congrArg
      (fun state : FinsetRankState alpha n => state.val)
      h

theorem FinsetTypeDeletionCoding.family_card_le_type_pow_rank
    {alpha : Type}
    [DecidableEq alpha]
    {n Qk : Nat}
    (Coding : FinsetTypeDeletionCoding alpha Qk)
    (F : Concrete.UniformSetFamily alpha n) :
    F.edges.card <= Qk ^ n := by
  exact (Coding.familyRankDeletionSystem F).family_card_le_type_pow_rank

end TraceAssembly
end V2
end SunflowerAASC
