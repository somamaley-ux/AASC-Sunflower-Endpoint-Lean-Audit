import SunflowerAASC.V2.ConstraintMapPopulation
import SunflowerAASC.V2.KernelRoleOccupancyAdapter

namespace SunflowerAASC
namespace V2
namespace FixedCellStandingClosure

open GeneratedIncidenceTower
open GeneratedSeedCapacity
open ReachableRoleOccupancy
open KernelRoleOccupancyAdapter

/-- The two finite classifier maps used to form genuine manuscript cells. -/
structure FixedComparisonClassifiers
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)) where
  constraintProfile : InitialCarrier F ->
    Finset ConstraintMapPopulation.ConstraintMapLevel
  forcedRole : InitialCarrier F -> AASCBlockerRole

/--
The exact support/profile/role fibre from the manuscript. Unlike the earlier
free `cell : Finset _`, every member carries the three fixed comparison fields
by construction.
-/
noncomputable def fixedComparisonCell
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (noSunflower : Not (Concrete.HasSunflower 3 F))
    (classifiers : FixedComparisonClassifiers F)
    (support : Finset (Fin 3))
    (profile : Finset ConstraintMapPopulation.ConstraintMapLevel)
    (role : AASCBlockerRole) : Finset (InitialCarrier F) := by
  classical
  exact (MinimalBlocker.minimalBlocker F).attach.filter fun source =>
    BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
        ⟨source.val,
          MinimalBlocker.minimalBlocker_subset_raw F source.property⟩ = support ∧
      classifiers.constraintProfile source = profile ∧
      classifiers.forcedRole source = role

theorem mem_fixedComparisonCell_iff
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {classifiers : FixedComparisonClassifiers F}
    {support : Finset (Fin 3)}
    {profile : Finset ConstraintMapPopulation.ConstraintMapLevel}
    {role : AASCBlockerRole}
    {source : InitialCarrier F} :
    source ∈ fixedComparisonCell F noSunflower classifiers support profile role ↔
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨source.val,
            MinimalBlocker.minimalBlocker_subset_raw F source.property⟩ = support ∧
        classifiers.constraintProfile source = profile ∧
        classifiers.forcedRole source = role := by
  classical
  simp [fixedComparisonCell]

/-- Every source lies in the fibre named by its own finite classifier values. -/
theorem mem_own_fixedComparisonCell
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (noSunflower : Not (Concrete.HasSunflower 3 F))
    (classifiers : FixedComparisonClassifiers F)
    (source : InitialCarrier F) :
    source ∈ fixedComparisonCell F noSunflower classifiers
      (BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
        ⟨source.val,
          MinimalBlocker.minimalBlocker_subset_raw F source.property⟩)
      (classifiers.constraintProfile source)
      (classifiers.forcedRole source) := by
  exact mem_fixedComparisonCell_iff.mpr ⟨rfl, rfl, rfl⟩

abbrev FixedCellSource
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    (noSunflower : Not (Concrete.HasSunflower 3 F))
    (classifiers : FixedComparisonClassifiers F)
    (support : Finset (Fin 3))
    (profile : Finset ConstraintMapPopulation.ConstraintMapLevel)
    (role : AASCBlockerRole) :=
  CellSource (fixedComparisonCell F noSunflower classifiers support profile role)

theorem fixedCellSource_support
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {classifiers : FixedComparisonClassifiers F}
    {support : Finset (Fin 3)}
    {profile : Finset ConstraintMapPopulation.ConstraintMapLevel}
    {role : AASCBlockerRole}
    (source : FixedCellSource noSunflower classifiers support profile role) :
    BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
        ⟨source.coordinate.val,
          MinimalBlocker.minimalBlocker_subset_raw F
            source.coordinate.property⟩ = support :=
  (mem_fixedComparisonCell_iff.mp source.property).1

theorem fixedCellSource_profile
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {classifiers : FixedComparisonClassifiers F}
    {support : Finset (Fin 3)}
    {profile : Finset ConstraintMapPopulation.ConstraintMapLevel}
    {role : AASCBlockerRole}
    (source : FixedCellSource noSunflower classifiers support profile role) :
    classifiers.constraintProfile source.coordinate = profile :=
  (mem_fixedComparisonCell_iff.mp source.property).2.1

theorem fixedCellSource_role
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {classifiers : FixedComparisonClassifiers F}
    {support : Finset (Fin 3)}
    {profile : Finset ConstraintMapPopulation.ConstraintMapLevel}
    {role : AASCBlockerRole}
    (source : FixedCellSource noSunflower classifiers support profile role) :
    classifiers.forcedRole source.coordinate = role :=
  (mem_fixedComparisonCell_iff.mp source.property).2.2

theorem fixedCellSource_fields_eq
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {classifiers : FixedComparisonClassifiers F}
    {support : Finset (Fin 3)}
    {profile : Finset ConstraintMapPopulation.ConstraintMapLevel}
    {role : AASCBlockerRole}
    (left right : FixedCellSource noSunflower classifiers support profile role) :
    BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.coordinate.val,
            MinimalBlocker.minimalBlocker_subset_raw F
              left.coordinate.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.coordinate.val,
            MinimalBlocker.minimalBlocker_subset_raw F
              right.coordinate.property⟩ ∧
      classifiers.constraintProfile left.coordinate =
        classifiers.constraintProfile right.coordinate ∧
      classifiers.forcedRole left.coordinate =
        classifiers.forcedRole right.coordinate := by
  exact ⟨(fixedCellSource_support left).trans
      (fixedCellSource_support right).symm,
    (fixedCellSource_profile left).trans
      (fixedCellSource_profile right).symm,
    (fixedCellSource_role left).trans
      (fixedCellSource_role right).symm⟩

abbrev TerminalCarrier
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)) :=
  {x // x ∈ MinimalBlocker.minimalBlocker
    (terminalFamily baseRank steps F)}

/--
One literal terminal carrier has one faithful fixed-endpoint reference.
`referenceOf` is not a source-to-carrier assignment and contains no population
or Hall field.
-/
structure DeterminateTerminalReference
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)) where
  referenceOf : TerminalCarrier F -> EndpointReference F
  faithful : Function.Injective referenceOf

/--
A generated reach is standing exactly when it is an admissible redescription:
the source and literal terminal carrier retain one fixed determinate reference.
-/
def StandingAdmissibleRedescription
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (reference : DeterminateTerminalReference F)
    (source : CellSource cell)
    (carrier : TerminalCarrier F) : Prop :=
  ReachesTerminalCarrier source.coordinate carrier ∧
    reference.referenceOf carrier = sourceReference F cell source

/--
The sole positive source obligation after the carrier and cell are fixed.
It asks for one already generated standing redescription in each source fibre.
-/
def StandingFiberPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (reference : DeterminateTerminalReference F) : Prop :=
  ∀ source : CellSource cell,
    ∃ carrier : TerminalCarrier F,
      StandingAdmissibleRedescription reference source carrier

theorem standingAdmissibleRedescription_singleValued
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (reference : DeterminateTerminalReference F)
    (source : CellSource cell)
    (left right : TerminalCarrier F)
    (leftStanding : StandingAdmissibleRedescription reference source left)
    (rightStanding : StandingAdmissibleRedescription reference source right) :
    left = right := by
  apply reference.faithful
  exact leftStanding.2.trans rightStanding.2.symm

/-- Shared standing carrier leaves only skin, hence one literal source. -/
theorem standingAdmissibleRedescription_sharedCarrier
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (reference : DeterminateTerminalReference F)
    (left right : CellSource cell)
    (carrier : TerminalCarrier F)
    (leftStanding : StandingAdmissibleRedescription reference left carrier)
    (rightStanding : StandingAdmissibleRedescription reference right carrier) :
    left = right := by
  apply sourceReference_injective F cell
  exact leftStanding.2.symm.trans rightStanding.2

/--
Determinate carrier reference and skin finality derive the complete bridge from
standing-fibre population. No injective selector or Hall inequality is an
input.
-/
noncomputable def standingPathBridgeOfStandingFiberPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (reference : DeterminateTerminalReference F)
    (population : StandingFiberPopulation (cell := cell) reference) :
    KernelFaithfulStandingPathBridge F cell where
  standingReach := StandingAdmissibleRedescription reference
  standingReach_generated := by
    intro source carrier standing
    exact standing.1
  standingReach_nonempty := population
  standingReach_singleValued := by
    intro source left right leftStanding rightStanding
    exact standingAdmissibleRedescription_singleValued
      reference source left right leftStanding rightStanding
  skin := {
    r := fun left right =>
      sourceReference F cell left = sourceReference F cell right
    iseqv := {
      refl := fun _ => rfl
      symm := fun same => same.symm
      trans := fun left right => left.trans right } }
  sameCarrierDeterminesAASCType := by
    intro left right carrier leftStanding rightStanding
    apply Quotient.sound
    exact leftStanding.2.symm.trans rightStanding.2
  quotientFinality := by
    intro left right sameReference
    exact sourceReference_injective F cell sameReference

/-- Standing population plus determinate carrier identity implies Hall. -/
theorem reachableRoleHall_of_standingFiberPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (reference : DeterminateTerminalReference F)
    (population : StandingFiberPopulation (cell := cell) reference) :
    ReachableRoleHall F cell :=
  reachableRoleHall_of_bridge
    (standingPathBridgeOfStandingFiberPopulation reference population)

/-- The fixed-cell specialization used by the manuscript crossing. -/
theorem fixedCell_reachableRoleHall_of_standingFiberPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {classifiers : FixedComparisonClassifiers F}
    {support : Finset (Fin 3)}
    {profile : Finset ConstraintMapPopulation.ConstraintMapLevel}
    {role : AASCBlockerRole}
    (reference : DeterminateTerminalReference F)
    (population : StandingFiberPopulation
      (cell := fixedComparisonCell F noSunflower classifiers support profile role)
      reference) :
    ReachableRoleHall F
      (fixedComparisonCell F noSunflower classifiers support profile role) :=
  reachableRoleHall_of_standingFiberPopulation reference population

end FixedCellStandingClosure
end V2
end SunflowerAASC
