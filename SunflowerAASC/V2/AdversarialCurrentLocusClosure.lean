import MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.CurrentLocusNullExclusion
import SunflowerAASC.V2.CurrentReferenceClassifierAdapter
import SunflowerAASC.V2.GeneratedTerminalKernelGovernance

namespace SunflowerAASC
namespace V2
namespace AdversarialCurrentLocusClosure

open GeneratedIncidenceTower
open GeneratedSeedCapacity
open ReachableRoleOccupancy
open RootAuthenticScopeCorrespondence
open CurrentReferenceClassifierAdapter
open GeneratedTerminalKernelGovernance
open MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction

/-!
Lean form of the manuscript's adversarial current-locus argument.

Track I supplies the generated relation. The AASC half supplies two logically
separate facts: an all-null generated fibre would destroy inherited Standing,
and every occupied locus bears a lawful primitive Current-Reference claim.
The kernel null-exclusion theorem derives population first; classifier
uniqueness derives collision exclusion second.
-/

/-- Standing of the necessarily governed terminal endpoint act. -/
def TerminalKernelStanding
    (alpha : Type)
    [DecidableEq alpha]
    (baseRank : Nat) : Prop :=
  ((terminalKernelFirstCorpusMachinery alpha baseRank).kernelAtEndpointUse
    (terminalNoSunflowerEndpointUse alpha baseRank)).standing

theorem terminalKernelStanding_holds
    (alpha : Type)
    [DecidableEq alpha]
    (baseRank : Nat) :
    TerminalKernelStanding alpha baseRank :=
  (terminalKernelFirstCorpusMachinery alpha baseRank).kernelAtEndpointUse
    (terminalNoSunflowerEndpointUse alpha baseRank) |>.standing_holds

/--
The generated current-locus system for one relation chosen by governance.
Generation is the literal incidence-tower relation and remains independent of
the narrower standing-positive occupancy relation.
-/
def generatedCurrentLocusSystem
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F))
    (currentOccupancy : CellSource cell -> SeedCoordinate F -> Prop)
    (occupancy_generated :
      forall source locus,
        currentOccupancy source locus ->
          ReachesTerminalCarrier source.coordinate locus) :
    GeneratedCurrentLocusSystem (CellSource cell) (SeedCoordinate F) where
  generated := fun source locus =>
    ReachesTerminalCarrier source.coordinate locus
  currentOccupancy := currentOccupancy
  sourceStanding := fun _ => TerminalKernelStanding alpha baseRank
  liveSamePackage := fun _ => True
  generated_nonempty := by
    intro source
    exact exists_reachesTerminalCarrier
      baseRank steps F source.coordinate
  occupancy_generated := occupancy_generated

/--
The exact adversarial manuscript package before finite readout.

There is no totality, right-uniqueness, selector, Hall, finite-code, or
cardinal-bound field. `allGeneratedNull_losesKernelStanding` is the paper's
null-regime contradiction, while `occupancy_binds_currentReference` is its
current-locus Reference-binding conclusion.
-/
structure AdversarialCurrentLocusPackage
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (_noSunflower : Not (Concrete.HasSunflower 3 F))
    (cell : Finset (InitialCarrier F)) where
  currentOccupancy : CellSource cell -> SeedCoordinate F -> Prop
  occupancy_generated :
    forall source locus,
      currentOccupancy source locus ->
        ReachesTerminalCarrier source.coordinate locus
  allGeneratedNull_losesKernelStanding :
    forall source,
      (forall locus,
        ReachesTerminalCarrier source.coordinate locus ->
          Not (currentOccupancy source locus)) ->
      Not (TerminalKernelStanding alpha baseRank)
  referenceSemantics :
    CurrentReferenceClassifierSemantics
      Unit (SeedCoordinate F) (CellSource cell)
  occupancy_binds_currentReference :
    forall source locus,
      currentOccupancy source locus ->
        referenceSemantics.currentReference () locus source

/-- The adversarial package instantiates the kernel's generated system. -/
def AdversarialCurrentLocusPackage.currentLocusSystem
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {cell : Finset (InitialCarrier F)}
    (package : AdversarialCurrentLocusPackage F noSunflower cell) :
    GeneratedCurrentLocusSystem (CellSource cell) (SeedCoordinate F) :=
  generatedCurrentLocusSystem F cell package.currentOccupancy
    package.occupancy_generated

/-- Null exclusion and forced endpoint Standing derive sourcewise occupancy. -/
def AdversarialCurrentLocusPackage.toCurrentLocusPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {cell : Finset (InitialCarrier F)}
    (package : AdversarialCurrentLocusPackage F noSunflower cell) :
    KernelForcedCurrentLocusPopulation package.currentLocusSystem where
  sourceStanding_holds := fun _ =>
    terminalKernelStanding_holds alpha baseRank
  liveSamePackage_holds := fun _ => trivial
  nullExclusion :=
    { allNullLosesStanding := by
        intro source _live allNull
        exact package.allGeneratedNull_losesKernelStanding source allNull }

/-- Occupied loci bind the lawful Current-Reference classifier. -/
def AdversarialCurrentLocusPackage.toCurrentReferenceBinding
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {cell : Finset (InitialCarrier F)}
    (package : AdversarialCurrentLocusPackage F noSunflower cell) :
    CurrentLocusReferenceBinding
      Unit (CellSource cell) (SeedCoordinate F)
      package.currentLocusSystem where
  packageOf := fun _ => ()
  referenceSemantics := package.referenceSemantics
  occupancy_binds_currentReference :=
    package.occupancy_binds_currentReference
  sharedOccupiedLocus_samePackage := by
    intro _left _right _locus _leftOccupancy _rightOccupancy
    rfl

/-- The manuscript dependency chain as one kernel closure object. -/
def AdversarialCurrentLocusPackage.toKernelForcedCurrentReferenceClosure
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {cell : Finset (InitialCarrier F)}
    (package : AdversarialCurrentLocusPackage F noSunflower cell) :
    KernelForcedCurrentReferenceClosure
      Unit (CellSource cell) (SeedCoordinate F)
      package.currentLocusSystem where
  population := package.toCurrentLocusPopulation
  binding := package.toCurrentReferenceBinding

/-- The all-null contradiction supplies one occupied generated seed per root. -/
theorem AdversarialCurrentLocusPackage.currentOccupancy_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {cell : Finset (InitialCarrier F)}
    (package : AdversarialCurrentLocusPackage F noSunflower cell)
    (source : CellSource cell) :
    Exists (package.currentOccupancy source) :=
  package.toCurrentLocusPopulation.currentOccupancy_nonempty source

/-- Classifier uniqueness supplies right-uniqueness only after occupancy. -/
theorem AdversarialCurrentLocusPackage.currentOccupancy_rightUnique
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {cell : Finset (InitialCarrier F)}
    (package : AdversarialCurrentLocusPackage F noSunflower cell)
    (left right : CellSource cell)
    (locus : SeedCoordinate F)
    (leftOccupancy : package.currentOccupancy left locus)
    (rightOccupancy : package.currentOccupancy right locus) :
    left = right :=
  package.toCurrentReferenceBinding.occupancy_rightUnique
    left right locus leftOccupancy rightOccupancy

/-- The adversarial package constructs the exact root-to-seed relation. -/
def AdversarialCurrentLocusPackage.toRootAuthenticScopeSeedClosure
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {cell : Finset (InitialCarrier F)}
    (package : AdversarialCurrentLocusPackage F noSunflower cell) :
    RootAuthenticScopeSeedClosure F cell where
  rootSeed := package.currentOccupancy
  rootSeed_generated := package.occupancy_generated
  rootSeed_total := package.currentOccupancy_nonempty
  rootSeed_rightUnique := by
    intro left right locus leftOccupancy rightOccupancy
    exact package.currentOccupancy_rightUnique
      left right locus leftOccupancy rightOccupancy

/-- The manuscript adversarial crossing yields finite reachable-role Hall. -/
theorem AdversarialCurrentLocusPackage.reachableRoleHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {cell : Finset (InitialCarrier F)}
    (package : AdversarialCurrentLocusPackage F noSunflower cell) :
    ReachableRoleHall F cell :=
  reachableRoleHall_of_rootAuthenticScopeSeedClosure
    package.toRootAuthenticScopeSeedClosure

/-- Hall reconstructs the adversarial package, for strength auditing only. -/
noncomputable def adversarialCurrentLocusPackageOfReachableRoleHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {cell : Finset (InitialCarrier F)}
    (hall : ReachableRoleHall F cell) :
    AdversarialCurrentLocusPackage F noSunflower cell := by
  let rootClosure := rootAuthenticScopeSeedClosureOfReachableRoleHall hall
  exact
    { currentOccupancy := rootClosure.rootSeed
      occupancy_generated := rootClosure.rootSeed_generated
      allGeneratedNull_losesKernelStanding := by
        intro source allNull _standing
        rcases rootClosure.rootSeed_total source with
          ⟨locus, occupancy⟩
        exact allNull locus
          (rootClosure.rootSeed_generated source locus occupancy)
          occupancy
      referenceSemantics :=
        referenceSemanticsOfRootAuthenticScopeSeedClosure rootClosure
      occupancy_binds_currentReference := by
        intro source locus occupancy
        exact occupancy }

/--
Exact-strength audit: the complete adversarial package has Hall strength. The
new decomposition nevertheless identifies its two independent proof tasks:
null-exclusion population and lawful Current-Reference collision closure.
-/
theorem nonempty_adversarialCurrentLocusPackage_iff_reachableRoleHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {cell : Finset (InitialCarrier F)} :
    Nonempty (AdversarialCurrentLocusPackage F noSunflower cell) <->
      ReachableRoleHall F cell := by
  constructor
  · intro package
    exact package.some.reachableRoleHall
  · intro hall
    exact ⟨adversarialCurrentLocusPackageOfReachableRoleHall hall⟩

end AdversarialCurrentLocusClosure
end V2
end SunflowerAASC
