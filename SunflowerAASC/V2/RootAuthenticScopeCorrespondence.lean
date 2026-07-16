import SunflowerAASC.V2.PairLocalizedReferenceDivergence
import SunflowerAASC.V2.ReachableRoleOccupancy

namespace SunflowerAASC
namespace V2
namespace RootAuthenticScopeCorrespondence

open GeneratedIncidenceTower
open GeneratedSeedCapacity
open ReachableRoleOccupancy

/-- The literal controlled-rank blocker coordinate used as a seed carrier. -/
abbrev SeedCoordinate
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)) :=
  {x // x ∈ MinimalBlocker.minimalBlocker
    (terminalFamily baseRank steps F)}

/--
The exact Lean form of the manuscript's root-to-seed crossing. Kernel
governance of the determinate generated incidence is already established; the
fields here isolate the additional representation claim that a generated
standing-positive seed relation is total and cannot assign one literal seed
coordinate to two source roots.
-/
structure RootAuthenticScopeSeedClosure
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F)) where
  rootSeed : CellSource cell → SeedCoordinate F → Prop
  rootSeed_generated :
    ∀ source seed, rootSeed source seed →
      ReachesTerminalCarrier source.coordinate seed
  rootSeed_total : ∀ source, ∃ seed, rootSeed source seed
  rootSeed_rightUnique :
    ∀ left right seed,
      rootSeed left seed → rootSeed right seed → left = right

/-- Finite choice displays the manuscript's selected root-to-seed map. -/
noncomputable def RootAuthenticScopeSeedClosure.rootSeedMap
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (closure : RootAuthenticScopeSeedClosure F cell) :
    CellSource cell → SeedCoordinate F :=
  fun source => Classical.choose (closure.rootSeed_total source)

theorem RootAuthenticScopeSeedClosure.rootSeedMap_rootSeed
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (closure : RootAuthenticScopeSeedClosure F cell)
    (source : CellSource cell) :
    closure.rootSeed source (closure.rootSeedMap source) :=
  Classical.choose_spec (closure.rootSeed_total source)

theorem RootAuthenticScopeSeedClosure.rootSeedMap_generated
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (closure : RootAuthenticScopeSeedClosure F cell)
    (source : CellSource cell) :
    ReachesTerminalCarrier source.coordinate (closure.rootSeedMap source) :=
  closure.rootSeed_generated source (closure.rootSeedMap source)
    (closure.rootSeedMap_rootSeed source)

theorem RootAuthenticScopeSeedClosure.rootSeedMap_injective
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (closure : RootAuthenticScopeSeedClosure F cell) :
    Function.Injective closure.rootSeedMap := by
  intro left right sameSeed
  apply closure.rootSeed_rightUnique left right (closure.rootSeedMap left)
  · exact closure.rootSeedMap_rootSeed left
  · rw [sameSeed]
    exact closure.rootSeedMap_rootSeed right

/-- The manuscript root-to-seed package entails Hall occupancy. -/
theorem reachableRoleHall_of_rootAuthenticScopeSeedClosure
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (closure : RootAuthenticScopeSeedClosure F cell) :
    ReachableRoleHall F cell := by
  apply reachableRoleHall_iff_exists_injective_selector.mpr
  exact ⟨closure.rootSeedMap, closure.rootSeedMap_injective,
    closure.rootSeedMap_generated⟩

/-- A reachable injective selector constructs the exact root-to-seed package. -/
def rootAuthenticScopeSeedClosureOfInjectiveSelector
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (seedOf : CellSource cell → SeedCoordinate F)
    (injective : Function.Injective seedOf)
    (generated : ∀ source,
      ReachesTerminalCarrier source.coordinate (seedOf source)) :
    RootAuthenticScopeSeedClosure F cell where
  rootSeed := fun source seed => seedOf source = seed
  rootSeed_generated := by
    intro source seed same
    simpa [← same] using generated source
  rootSeed_total := fun source => ⟨seedOf source, rfl⟩
  rootSeed_rightUnique := by
    intro left right seed leftSeed rightSeed
    exact injective (leftSeed.trans rightSeed.symm)

/-- Hall occupancy reconstructs the manuscript root-to-seed package. -/
noncomputable def rootAuthenticScopeSeedClosureOfReachableRoleHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (hall : ReachableRoleHall F cell) :
    RootAuthenticScopeSeedClosure F cell := by
  let witness := reachableRoleHall_iff_exists_injective_selector.mp hall
  let seedOf := Classical.choose witness
  have specification := Classical.choose_spec witness
  exact rootAuthenticScopeSeedClosureOfInjectiveSelector seedOf
    specification.1 specification.2

/--
Exact-strength theorem for the manuscript vocabulary: inhabiting its
root-standing/root-reference seed package is exactly finite Hall occupancy of
the already generated terminal incidence relation.
-/
theorem nonempty_rootAuthenticScopeSeedClosure_iff_reachableRoleHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)} :
    Nonempty (RootAuthenticScopeSeedClosure F cell) ↔
      ReachableRoleHall F cell := by
  constructor
  · intro closure
    exact reachableRoleHall_of_rootAuthenticScopeSeedClosure closure.some
  · intro hall
    exact ⟨rootAuthenticScopeSeedClosureOfReachableRoleHall hall⟩

/-- The root-authentic package and the older standing-path package have equal strength. -/
theorem nonempty_rootAuthenticScopeSeedClosure_iff_standingPathBridge
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)} :
    Nonempty (RootAuthenticScopeSeedClosure F cell) ↔
      Nonempty (KernelFaithfulStandingPathBridge F cell) := by
  rw [nonempty_rootAuthenticScopeSeedClosure_iff_reachableRoleHall,
    nonempty_standingPathBridge_iff_reachableRoleHall]

end RootAuthenticScopeCorrespondence
end V2
end SunflowerAASC
