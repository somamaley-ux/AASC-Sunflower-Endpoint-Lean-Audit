import Mathlib.Combinatorics.Hall.Finite
import SunflowerAASC.V2.GeneratedSeedCapacity

namespace SunflowerAASC
namespace V2
namespace ReachableRoleOccupancy

open GeneratedIncidenceTower
open GeneratedSeedCapacity

/-- The literal terminal blocker coordinates reachable from one cell source. -/
noncomputable def reachableCarriers
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F))
    (source : CellSource cell) :
    Finset {x // x ∈ MinimalBlocker.minimalBlocker
      (terminalFamily baseRank steps F)} := by
  classical
  exact (MinimalBlocker.minimalBlocker
    (terminalFamily baseRank steps F)).attach.filter
      (ReachesTerminalCarrier source.coordinate)

theorem mem_reachableCarriers_iff
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    {source : CellSource cell}
    {carrier : {x // x ∈ MinimalBlocker.minimalBlocker
      (terminalFamily baseRank steps F)}} :
    carrier ∈ reachableCarriers F cell source ↔
      ReachesTerminalCarrier source.coordinate carrier := by
  classical
  simp [reachableCarriers]

theorem reachableCarriers_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F))
    (source : CellSource cell) :
    (reachableCarriers F cell source).Nonempty := by
  rcases exists_reachesTerminalCarrier baseRank steps F source.coordinate with
    ⟨carrier, reachable⟩
  exact ⟨carrier, mem_reachableCarriers_iff.mpr reachable⟩

/--
Hall occupancy for the generated blocker-incidence relation. Every finite
subcell has at least as many reachable terminal roles as source identities.
-/
def ReachableRoleHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F)) : Prop :=
  ∀ sources : Finset (CellSource cell),
    sources.card ≤ (sources.biUnion (reachableCarriers F cell)).card

/-- Hall occupancy is equivalent to a collision-free reachable selector. -/
theorem reachableRoleHall_iff_exists_injective_selector
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)} :
    ReachableRoleHall F cell ↔
      ∃ carrierOf : CellSource cell →
          {x // x ∈ MinimalBlocker.minimalBlocker
            (terminalFamily baseRank steps F)},
        Function.Injective carrierOf ∧
          ∀ source, ReachesTerminalCarrier source.coordinate
            (carrierOf source) := by
  classical
  rw [ReachableRoleHall]
  constructor
  · intro hall
    rcases (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (reachableCarriers F cell)).mp hall with ⟨carrierOf, injective, member⟩
    exact ⟨carrierOf, injective, fun source =>
      mem_reachableCarriers_iff.mp (member source)⟩
  · rintro ⟨carrierOf, injective, reachable⟩
    exact (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (reachableCarriers F cell)).mpr
        ⟨carrierOf, injective, fun source =>
          mem_reachableCarriers_iff.mpr (reachable source)⟩

/-- A reachable injection constructs the complete relation-level AASC bridge. -/
noncomputable def standingPathBridgeOfInjectiveSelector
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (carrierOf : CellSource cell →
      {x // x ∈ MinimalBlocker.minimalBlocker
        (terminalFamily baseRank steps F)})
    (injective : Function.Injective carrierOf)
    (reachable : ∀ source, ReachesTerminalCarrier source.coordinate
      (carrierOf source)) :
    GeneratedSeedCapacity.KernelFaithfulStandingPathBridge F cell where
  standingReach := fun source carrier => carrierOf source = carrier
  standingReach_generated := by
    intro source carrier same
    simpa [← same] using reachable source
  standingReach_nonempty := fun source => ⟨carrierOf source, rfl⟩
  standingReach_singleValued := by
    intro source left right leftStanding rightStanding
    exact leftStanding.symm.trans rightStanding
  skin := {
    r := Eq
    iseqv := {
      refl := fun _ => rfl
      symm := fun same => same.symm
      trans := fun left right => left.trans right } }
  sameCarrierDeterminesAASCType := by
    intro left right carrier leftStanding rightStanding
    have sameSelected : carrierOf left = carrierOf right :=
      leftStanding.trans rightStanding.symm
    exact congrArg (Quotient.mk _) (injective sameSelected)
  quotientFinality := by
    intro left right same
    exact same

/-- Hall occupancy constructs the kernel-faithful standing-path bridge. -/
noncomputable def standingPathBridgeOfReachableRoleHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (hall : ReachableRoleHall F cell) :
    GeneratedSeedCapacity.KernelFaithfulStandingPathBridge F cell := by
  let witness := reachableRoleHall_iff_exists_injective_selector.mp hall
  let carrierOf := Classical.choose witness
  have specification := Classical.choose_spec witness
  exact standingPathBridgeOfInjectiveSelector carrierOf
    specification.1 specification.2

/-- Every standing-path bridge supplies Hall occupancy of generated roles. -/
theorem reachableRoleHall_of_bridge
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (bridge : GeneratedSeedCapacity.KernelFaithfulStandingPathBridge F cell) :
    ReachableRoleHall F cell := by
  apply reachableRoleHall_iff_exists_injective_selector.mpr
  exact ⟨bridge.standingCarrierOf, bridge.standingCarrierOf_injective,
    bridge.standingCarrier_reachable⟩

/--
Exact bridge boundary: the relation-level bridge is inhabited precisely when
the generated incidence relation satisfies finite Hall occupancy.
-/
theorem nonempty_standingPathBridge_iff_reachableRoleHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)} :
    Nonempty (GeneratedSeedCapacity.KernelFaithfulStandingPathBridge F cell) ↔
      ReachableRoleHall F cell := by
  constructor
  · intro bridge
    exact reachableRoleHall_of_bridge bridge.some
  · intro hall
    exact ⟨standingPathBridgeOfReachableRoleHall hall⟩

end ReachableRoleOccupancy
end V2
end SunflowerAASC
