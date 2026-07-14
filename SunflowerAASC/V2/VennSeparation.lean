import Mathlib.Data.Fintype.Powerset
import SunflowerAASC.V2.TraceAssembly

namespace SunflowerAASC
namespace V2
namespace VennSeparation

/-- An overlapping-layer cell together with a bounded slot inside that cell. -/
abbrev VennCellCode (layerCount fiberBound : Nat) :=
  Finset (Fin layerCount) × Fin fiberBound

def vennAlphabetSize (layerCount fiberBound : Nat) : Nat :=
  2 ^ layerCount * fiberBound

theorem vennCellCode_card (layerCount fiberBound : Nat) :
    Fintype.card (VennCellCode layerCount fiberBound) =
      vennAlphabetSize layerCount fiberBound := by
  simp [VennCellCode, vennAlphabetSize, Fintype.card_finset]

noncomputable def vennCellEquivFin (layerCount fiberBound : Nat) :
    VennCellCode layerCount fiberBound ≃
      Fin (vennAlphabetSize layerCount fiberBound) :=
  Fintype.equivFinOfCardEq (vennCellCode_card layerCount fiberBound)

theorem vennAlphabetSize_positive
    {layerCount fiberBound : Nat}
    (fiberBound_positive : 0 < fiberBound) :
    0 < vennAlphabetSize layerCount fiberBound := by
  exact Nat.mul_pos (Nat.two_pow_pos layerCount) fiberBound_positive

/--
One terminal no-sunflower rank system governed by overlapping constraint
layers.  Layers need not partition states.  A bounded slot records the
surviving multiplicity inside one complete Venn cell.
-/
structure TerminalVennRankSystem
    (layerCount fiberBound : Nat) where
  State : Nat -> Type
  baseSubsingleton : forall left right : State 0, left = right
  predecessor : forall r : Nat, State (r + 1) -> State r
  layerCell : forall r : Nat, State (r + 1) -> Finset (Fin layerCount)
  fiberSlot : forall r : Nat, State (r + 1) -> Fin fiberBound
  skinOutcome : forall r : Nat, State (r + 1) -> State (r + 1) -> Prop
  tensorSplitOutcome : forall r : Nat, State (r + 1) -> State (r + 1) -> Prop
  sunflowerOutcome : forall r : Nat, State (r + 1) -> State (r + 1) -> Prop
  collisionExhaustive :
    forall r : Nat, forall left right : State (r + 1),
      predecessor r left = predecessor r right ->
      layerCell r left = layerCell r right ->
      fiberSlot r left = fiberSlot r right ->
      left = right \/
      skinOutcome r left right \/
      tensorSplitOutcome r left right \/
      sunflowerOutcome r left right
  skinFinality :
    forall r : Nat, forall left right : State (r + 1),
      skinOutcome r left right -> left = right
  tensorSplitExcluded :
    forall r : Nat, forall left right : State (r + 1),
      tensorSplitOutcome r left right -> False
  sunflowerExcluded :
    forall r : Nat, forall left right : State (r + 1),
      sunflowerOutcome r left right -> False

theorem TerminalVennRankSystem.collision
    {layerCount fiberBound : Nat}
    (System : TerminalVennRankSystem layerCount fiberBound)
    (r : Nat)
    (left right : System.State (r + 1))
    (samePredecessor :
      System.predecessor r left = System.predecessor r right)
    (sameCell : System.layerCell r left = System.layerCell r right)
    (sameSlot : System.fiberSlot r left = System.fiberSlot r right) :
    left = right := by
  rcases System.collisionExhaustive
      r left right samePredecessor sameCell sameSlot with
    equal | skinOrTensorOrSun
  · exact equal
  · rcases skinOrTensorOrSun with skin | tensorOrSun
    · exact System.skinFinality r left right skin
    · rcases tensorOrSun with tensor | sunflower
      · exact False.elim (System.tensorSplitExcluded r left right tensor)
      · exact False.elim (System.sunflowerExcluded r left right sunflower)

noncomputable def TerminalVennRankSystem.toRankDeletionSystem
    {layerCount fiberBound : Nat}
    (System : TerminalVennRankSystem layerCount fiberBound) :
    TraceAssembly.RankDeletionSystem
      (vennAlphabetSize layerCount fiberBound) where
  State := System.State
  baseSubsingleton := System.baseSubsingleton
  predecessor := System.predecessor
  headCode := fun r state =>
    vennCellEquivFin layerCount fiberBound
      (System.layerCell r state, System.fiberSlot r state)
  step_injective := by
    intro r left right hpair
    have samePredecessor :
        System.predecessor r left = System.predecessor r right :=
      congrArg Prod.snd hpair
    have sameCode :
        (System.layerCell r left, System.fiberSlot r left) =
          (System.layerCell r right, System.fiberSlot r right) := by
      apply (vennCellEquivFin layerCount fiberBound).injective
      exact congrArg Prod.fst hpair
    exact System.collision r left right
      samePredecessor
      (congrArg Prod.fst sameCode)
      (congrArg Prod.snd sameCode)

/-- A Venn-layer system whose top states faithfully contain the real family. -/
structure FamilyTerminalVennSystem
    {alpha : Type}
    [DecidableEq alpha]
    {n layerCount fiberBound : Nat}
    (F : Concrete.UniformSetFamily alpha n) where
  vennSystem : TerminalVennRankSystem layerCount fiberBound
  topState : {edge // edge ∈ F.edges} -> vennSystem.State n
  topState_injective : Function.Injective topState

noncomputable def FamilyTerminalVennSystem.toFamilyRankDeletionSystem
    {alpha : Type}
    [DecidableEq alpha]
    {n layerCount fiberBound : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    (System : FamilyTerminalVennSystem
      (layerCount := layerCount) (fiberBound := fiberBound) F) :
    TraceAssembly.FamilyRankDeletionSystem
      (Qk := vennAlphabetSize layerCount fiberBound) F where
  system := System.vennSystem.toRankDeletionSystem
  topState := System.topState
  topState_injective := System.topState_injective

/-- Uniform Venn-layer exhaustion for every no-sunflower countercase. -/
structure KernelFaithfulVennDeletionSource
    (alpha : Type)
    [DecidableEq alpha]
    (n k layerCount fiberBound : Nat)
    (corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha n k)) where
  fiberBound_positive : 0 < fiberBound
  roleOfType :
    Fin (vennAlphabetSize layerCount fiberBound) -> AASCBlockerRole
  system :
    forall F : Concrete.UniformSetFamily alpha n,
      Not (Concrete.HasSunflower k F) ->
      FamilyTerminalVennSystem
        (layerCount := layerCount) (fiberBound := fiberBound) F

noncomputable def KernelFaithfulVennDeletionSource.toRankDeletionSource
    {alpha : Type}
    [DecidableEq alpha]
    {n k layerCount fiberBound : Nat}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha n k)}
    (Src : KernelFaithfulVennDeletionSource
      alpha n k layerCount fiberBound corpus) :
    TraceAssembly.KernelFaithfulRankDeletionSource
      alpha n k (vennAlphabetSize layerCount fiberBound) where
  Qk_positive := vennAlphabetSize_positive Src.fiberBound_positive
  roleOfType := Src.roleOfType
  deletionSystem := fun F noSunflower =>
    (Src.system F noSunflower).toFamilyRankDeletionSystem

theorem sunflower_of_vennDeletion
    {alpha : Type}
    [DecidableEq alpha]
    {n k layerCount fiberBound : Nat}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha n k)}
    (Src : KernelFaithfulVennDeletionSource
      alpha n k layerCount fiberBound corpus)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      vennAlphabetSize layerCount fiberBound ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  exact TraceAssembly.sunflower_of_rankDeletionSystem
    Src.toRankDeletionSource
    F
    sizeExcess

end VennSeparation
end V2
end SunflowerAASC
