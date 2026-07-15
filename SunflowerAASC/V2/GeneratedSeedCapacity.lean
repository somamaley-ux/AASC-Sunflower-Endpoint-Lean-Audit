import SunflowerAASC.V2.GeneratedIncidenceTower
import SunflowerAASC.V2.PopulationInheritance

namespace SunflowerAASC
namespace V2
namespace GeneratedSeedCapacity

open GeneratedIncidenceTower

abbrev InitialCarrier
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)) :=
  {x // x ∈ MinimalBlocker.minimalBlocker F}

abbrev CellSource
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    (cell : Finset (InitialCarrier F)) :=
  {x // x ∈ cell}

def CellSource.coordinate
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (source : CellSource cell) : InitialCarrier F :=
  source.val

/-- The terminal blocker carrier is generated before AASC governance is used. -/
noncomputable def cellCarrierOf
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F))
    (source : CellSource cell) :
    {x // x ∈ MinimalBlocker.minimalBlocker
      (terminalFamily baseRank steps F)} :=
  generatedCarrier baseRank steps F source.coordinate

theorem cellCarrierOf_reachable
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F))
    (source : CellSource cell) :
    ReachesTerminalCarrier source.coordinate (cellCarrierOf F cell source) :=
  generatedCarrier_reachable baseRank steps F source.coordinate

/--
The exact AASC handoff for already generated terminal carriers.  `skin` is the
standing-form quotient relation.  Carrier equality fixes the complete AASC
type, and quotient finality removes only skin.  No population, path, numerical
slot, or injective map is supplied by this structure.
-/
structure KernelFaithfulEndpointRoleBridge
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F)) where
  skin : Setoid (CellSource cell)
  carrierDeterminesAASCType :
    ∀ left right : CellSource cell,
      cellCarrierOf F cell left = cellCarrierOf F cell right →
        Quotient.mk skin left = Quotient.mk skin right
  quotientFinality :
    ∀ left right : CellSource cell, skin.r left right → left = right

/-- Same complete endpoint carrier is skin-equivalence, not new population. -/
theorem KernelFaithfulEndpointRoleBridge.sameCarrier_isSkin
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (bridge : KernelFaithfulEndpointRoleBridge F cell)
    (left right : CellSource cell)
    (sameCarrier : cellCarrierOf F cell left = cellCarrierOf F cell right) :
    bridge.skin.r left right := by
  exact Quotient.exact <| bridge.carrierDeterminesAASCType
    left right sameCarrier

/-- AASC endpoint governance makes the generated terminal carrier collision-free. -/
theorem KernelFaithfulEndpointRoleBridge.cellCarrierOf_injective
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (bridge : KernelFaithfulEndpointRoleBridge F cell) :
    Function.Injective (cellCarrierOf F cell) := by
  intro left right sameCarrier
  exact bridge.quotientFinality left right <|
    bridge.sameCarrier_isSkin left right sameCarrier

/-- Equality-skin packages any independently proved terminal collision theorem. -/
noncomputable def bridgeOfCellCarrierInjective
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (injective : Function.Injective (cellCarrierOf F cell)) :
    KernelFaithfulEndpointRoleBridge F cell where
  skin := {
    r := Eq
    iseqv := {
      refl := fun _ => rfl
      symm := fun same => same.symm
      trans := fun left right => left.trans right } }
  carrierDeterminesAASCType := by
    intro left right sameCarrier
    exact congrArg (Quotient.mk _) (injective sameCarrier)
  quotientFinality := by
    intro left right same
    exact same

/--
Audit boundary: after generation, the AASC bridge has exactly the content of
terminal carrier collision-impossibility, not the content of path population.
-/
theorem nonempty_endpointRoleBridge_iff_cellCarrierOf_injective
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)} :
    Nonempty (KernelFaithfulEndpointRoleBridge F cell) ↔
      Function.Injective (cellCarrierOf F cell) := by
  constructor
  · intro bridge
    exact bridge.some.cellCarrierOf_injective
  · intro injective
    exact ⟨bridgeOfCellCarrierInjective injective⟩

/-- The combinatorial terminal family receives its traditional seed code. -/
noncomputable def terminalSeedEmbedding
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps k cutoff : Nat}
    (rankAtMost : baseRank + 1 ≤ cutoff)
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    {x // x ∈ MinimalBlocker.minimalBlocker
      (terminalFamily baseRank steps F)} ↪
      Fin (PopulationInheritance.traditionalSeedTensorProfileBound k cutoff) :=
  PopulationInheritance.traditionalSeedProfileEmbedding
    rankAtMost
    (terminalFamily baseRank steps F)
    (terminalFamily_noSunflower baseRank steps F noSunflower)

/-- The fully composed generated seed code, still prior to endpoint governance. -/
noncomputable def cellSeedCode
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps k cutoff : Nat}
    {rankAtMost : baseRank + 1 ≤ cutoff}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (cell : Finset (InitialCarrier F)) :
    CellSource cell →
      Fin (PopulationInheritance.traditionalSeedTensorProfileBound k cutoff) :=
  fun source => terminalSeedEmbedding rankAtMost F noSunflower
    (cellCarrierOf F cell source)

theorem KernelFaithfulEndpointRoleBridge.seedCode_injective
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps k cutoff : Nat}
    {rankAtMost : baseRank + 1 ≤ cutoff}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {cell : Finset (InitialCarrier F)}
    (bridge : KernelFaithfulEndpointRoleBridge F cell) :
    Function.Injective
      (cellSeedCode (rankAtMost := rankAtMost)
        (F := F) (noSunflower := noSunflower) cell) := by
  intro left right sameCode
  apply bridge.cellCarrierOf_injective
  exact (terminalSeedEmbedding rankAtMost F noSunflower).injective sameCode

theorem KernelFaithfulEndpointRoleBridge.cell_card_le_seedCapacity
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps k cutoff : Nat}
    {rankAtMost : baseRank + 1 ≤ cutoff}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {cell : Finset (InitialCarrier F)}
    (bridge : KernelFaithfulEndpointRoleBridge F cell) :
    cell.card ≤
      PopulationInheritance.traditionalSeedTensorProfileBound k cutoff := by
  classical
  have bound := Fintype.card_le_of_injective
    (cellSeedCode (rankAtMost := rankAtMost)
      (F := F) (noSunflower := noSunflower) cell)
    (bridge.seedCode_injective
      (rankAtMost := rankAtMost) (noSunflower := noSunflower))
  simpa using bound

/-- The publication's literal three-petal seed capacity. -/
theorem KernelFaithfulEndpointRoleBridge.cell_card_le_4094
    {alpha : Type}
    [DecidableEq alpha]
    {steps : Nat}
    {F : Concrete.UniformSetFamily alpha (2046 + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {cell : Finset (InitialCarrier F)}
    (bridge : KernelFaithfulEndpointRoleBridge F cell) :
    cell.card ≤ 4094 := by
  simpa [PopulationInheritance.threePetalTraditionalCutoff] using
    bridge.cell_card_le_seedCapacity
      (k := 3)
      (cutoff := PopulationInheritance.threePetalTraditionalCutoff)
      (rankAtMost := by decide)
      (noSunflower := noSunflower)

/--
The relation-level handoff. Combinatorics has already populated `Reaches`; AASC
classifies which generated endpoint relations remain standing-bearing, proves
that one such relation survives for each source, and governs same-role
collisions. No continuation path or terminal coordinate is generated here.
-/
structure KernelFaithfulStandingPathBridge
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F)) where
  standingReach :
    CellSource cell →
      {x // x ∈ MinimalBlocker.minimalBlocker
        (terminalFamily baseRank steps F)} → Prop
  standingReach_generated :
    ∀ source carrier, standingReach source carrier →
      ReachesTerminalCarrier source.coordinate carrier
  standingReach_nonempty :
    ∀ source, ∃ carrier, standingReach source carrier
  standingReach_singleValued :
    ∀ source left right,
      standingReach source left → standingReach source right → left = right
  skin : Setoid (CellSource cell)
  sameCarrierDeterminesAASCType :
    ∀ left right carrier,
      standingReach left carrier → standingReach right carrier →
        Quotient.mk skin left = Quotient.mk skin right
  quotientFinality :
    ∀ left right : CellSource cell, skin.r left right → left = right

/-- The unique surviving carrier is selected only after the generated relation is governed. -/
noncomputable def KernelFaithfulStandingPathBridge.standingCarrierOf
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (bridge : KernelFaithfulStandingPathBridge F cell)
    (source : CellSource cell) :
    {x // x ∈ MinimalBlocker.minimalBlocker
      (terminalFamily baseRank steps F)} :=
  Classical.choose (bridge.standingReach_nonempty source)

theorem KernelFaithfulStandingPathBridge.standingCarrierOf_spec
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (bridge : KernelFaithfulStandingPathBridge F cell)
    (source : CellSource cell) :
    bridge.standingReach source (bridge.standingCarrierOf source) :=
  Classical.choose_spec (bridge.standingReach_nonempty source)

theorem KernelFaithfulStandingPathBridge.standingCarrier_reachable
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (bridge : KernelFaithfulStandingPathBridge F cell)
    (source : CellSource cell) :
    ReachesTerminalCarrier source.coordinate (bridge.standingCarrierOf source) :=
  bridge.standingReach_generated source (bridge.standingCarrierOf source)
    (bridge.standingCarrierOf_spec source)

theorem KernelFaithfulStandingPathBridge.standingCarrier_choice_independent
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (bridge : KernelFaithfulStandingPathBridge F cell)
    (source : CellSource cell)
    (carrier : {x // x ∈ MinimalBlocker.minimalBlocker
      (terminalFamily baseRank steps F)})
    (standing : bridge.standingReach source carrier) :
    carrier = bridge.standingCarrierOf source :=
  bridge.standingReach_singleValued source carrier
    (bridge.standingCarrierOf source) standing
    (bridge.standingCarrierOf_spec source)

/-- Endpoint governance, not generation, excludes a shared standing carrier. -/
theorem KernelFaithfulStandingPathBridge.standingCarrierOf_injective
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (bridge : KernelFaithfulStandingPathBridge F cell) :
    Function.Injective bridge.standingCarrierOf := by
  intro left right sameCarrier
  have leftStanding := bridge.standingCarrierOf_spec left
  have rightStandingAtLeft :
      bridge.standingReach right (bridge.standingCarrierOf left) := by
    rw [sameCarrier]
    exact bridge.standingCarrierOf_spec right
  exact bridge.quotientFinality left right <| Quotient.exact <|
    bridge.sameCarrierDeterminesAASCType left right
      (bridge.standingCarrierOf left) leftStanding rightStandingAtLeft

noncomputable def KernelFaithfulStandingPathBridge.seedCode
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps k cutoff : Nat}
    {rankAtMost : baseRank + 1 ≤ cutoff}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {cell : Finset (InitialCarrier F)}
    (bridge : KernelFaithfulStandingPathBridge F cell) :
    CellSource cell →
      Fin (PopulationInheritance.traditionalSeedTensorProfileBound k cutoff) :=
  fun source => terminalSeedEmbedding rankAtMost F noSunflower
    (bridge.standingCarrierOf source)

theorem KernelFaithfulStandingPathBridge.seedCode_injective
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps k cutoff : Nat}
    {rankAtMost : baseRank + 1 ≤ cutoff}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {cell : Finset (InitialCarrier F)}
    (bridge : KernelFaithfulStandingPathBridge F cell) :
    Function.Injective
      (bridge.seedCode (rankAtMost := rankAtMost)
        (noSunflower := noSunflower)) := by
  intro left right sameCode
  apply bridge.standingCarrierOf_injective
  exact (terminalSeedEmbedding rankAtMost F noSunflower).injective sameCode

theorem KernelFaithfulStandingPathBridge.cell_card_le_4094
    {alpha : Type}
    [DecidableEq alpha]
    {steps : Nat}
    {F : Concrete.UniformSetFamily alpha (2046 + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {cell : Finset (InitialCarrier F)}
    (bridge : KernelFaithfulStandingPathBridge F cell) :
    cell.card ≤ 4094 := by
  classical
  have bound := Fintype.card_le_of_injective
    (bridge.seedCode
      (k := 3)
      (cutoff := PopulationInheritance.threePetalTraditionalCutoff)
      (rankAtMost := by decide)
      (noSunflower := noSunflower))
    (bridge.seedCode_injective
      (k := 3)
      (cutoff := PopulationInheritance.threePetalTraditionalCutoff)
      (rankAtMost := by decide)
      (noSunflower := noSunflower))
  simpa [PopulationInheritance.threePetalTraditionalCutoff] using bound

end GeneratedSeedCapacity
end V2
end SunflowerAASC
