import SunflowerAASC.V2.FixedCellStandingClosure

namespace SunflowerAASC
namespace V2
namespace FixedCellRoleLocusExclusion

open GeneratedIncidenceTower
open GeneratedSeedCapacity
open ReachableRoleOccupancy
open FixedCellStandingClosure

/--
The Pauli-style exclusion law for a complete fixed AASC role cell. Two
role-identical determinate continuations cannot occupy one literal terminal
locus while remaining distinct source objects.

This is a collision law, not a population field. Population of the raw
generated relation is supplied independently by `exists_reachesTerminalCarrier`.
-/
def CompleteRoleLocusExclusion
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F)) : Prop :=
  forall (left right : CellSource cell) (locus : TerminalCarrier F),
    ReachesTerminalCarrier left.coordinate locus ->
    ReachesTerminalCarrier right.coordinate locus ->
    left = right

/-- The generated carrier choice is collision-free under role-locus exclusion. -/
theorem generatedCarrier_injective_of_completeRoleLocusExclusion
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (exclusion : CompleteRoleLocusExclusion F cell) :
    Function.Injective (cellCarrierOf F cell) := by
  intro left right sameLocus
  have leftReach := cellCarrierOf_reachable F cell left
  have rightReach := cellCarrierOf_reachable F cell right
  rw [← sameLocus] at rightReach
  exact exclusion left right (cellCarrierOf F cell left)
    leftReach rightReach

/--
Positive combinatorial reachability and complete role-locus exclusion imply
Hall occupancy. No standing subrelation or standing-population premise occurs.
-/
theorem reachableRoleHall_of_completeRoleLocusExclusion
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (exclusion : CompleteRoleLocusExclusion F cell) :
    ReachableRoleHall F cell := by
  apply reachableRoleHall_iff_exists_injective_selector.mpr
  exact
    ⟨cellCarrierOf F cell,
      generatedCarrier_injective_of_completeRoleLocusExclusion exclusion,
      cellCarrierOf_reachable F cell⟩

/-- The classifiers carried by an existing complete AASC signature package. -/
def classifiersOfConstraintPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha
        (baseRank + steps + 1) 3)}
    (population : ConstraintMapPopulation.PrivateWitnessConstraintPopulation
      noSunflower corpus) :
    FixedComparisonClassifiers F where
  constraintProfile := population.constraintProfile
  forcedRole := population.forcedRole

/--
The existing complete-signature exhaustion proves the stronger fact that each
fixed support/profile/role cell is subsingleton. This theorem records the exact
point where the AASC collision sieve realizes the role-locus exclusion law.
-/
theorem fixedCellSource_eq_of_constraintPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha
        (baseRank + steps + 1) 3)}
    (population : ConstraintMapPopulation.PrivateWitnessConstraintPopulation
      noSunflower corpus)
    {support : Finset (Fin 3)}
    {profile : Finset ConstraintMapPopulation.ConstraintMapLevel}
    {role : AASCBlockerRole}
    (left right : FixedCellSource noSunflower
      (classifiersOfConstraintPopulation population) support profile role) :
    left = right := by
  rcases fixedCellSource_fields_eq left right with
    ⟨sameSupport, sameProfile, sameRole⟩
  apply Subtype.ext
  exact population.withinCellTensorMultiplicityCollapse
    left.coordinate right.coordinate sameSupport sameProfile sameRole

/-- Complete AASC signature exhaustion instantiates role-locus exclusion. -/
theorem completeRoleLocusExclusion_of_constraintPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha
        (baseRank + steps + 1) 3)}
    (population : ConstraintMapPopulation.PrivateWitnessConstraintPopulation
      noSunflower corpus)
    (support : Finset (Fin 3))
    (profile : Finset ConstraintMapPopulation.ConstraintMapLevel)
    (role : AASCBlockerRole) :
    CompleteRoleLocusExclusion F
      (fixedComparisonCell F noSunflower
        (classifiersOfConstraintPopulation population) support profile role) := by
  intro left right _locus _leftReach _rightReach
  exact fixedCellSource_eq_of_constraintPopulation population left right

/--
The complete-signature AASC package and generated combinatorial reachability
compose directly to Hall on every genuine fixed comparison cell.
-/
theorem fixedCell_reachableRoleHall_of_constraintPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha
        (baseRank + steps + 1) 3)}
    (population : ConstraintMapPopulation.PrivateWitnessConstraintPopulation
      noSunflower corpus)
    (support : Finset (Fin 3))
    (profile : Finset ConstraintMapPopulation.ConstraintMapLevel)
    (role : AASCBlockerRole) :
    ReachableRoleHall F
      (fixedComparisonCell F noSunflower
        (classifiersOfConstraintPopulation population) support profile role) :=
  reachableRoleHall_of_completeRoleLocusExclusion
    (completeRoleLocusExclusion_of_constraintPopulation
      population support profile role)

end FixedCellRoleLocusExclusion
end V2
end SunflowerAASC
