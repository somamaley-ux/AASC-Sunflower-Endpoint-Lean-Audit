import MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.CurrentReferenceOccupancy
import SunflowerAASC.V2.RootAuthenticScopeCorrespondence

namespace SunflowerAASC
namespace V2
namespace CurrentReferenceClassifierAdapter

open GeneratedIncidenceTower
open GeneratedSeedCapacity
open ReachableRoleOccupancy
open RootAuthenticScopeCorrespondence
open MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction

/--
The manuscript's root-to-seed relation with its Current-Reference
functionality supplied by the relational kernel theorem. Generation and
sourcewise totality remain explicit combinatorial fields. There is no
right-uniqueness, injectivity, Hall, finite-code, or cardinal-bound field.
-/
structure ClassifierGovernedRootSeedClosure
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F)) where
  rootSeed : CellSource cell -> SeedCoordinate F -> Prop
  rootSeed_generated :
    forall source locus,
      rootSeed source locus ->
      ReachesTerminalCarrier source.coordinate locus
  rootSeed_total : forall source, Exists (rootSeed source)
  referenceSemantics :
    CurrentReferenceClassifierSemantics
      Unit (SeedCoordinate F) (CellSource cell)
  referenceSemantics_iff :
    forall source locus,
      referenceSemantics.currentReference () locus source <->
        rootSeed source locus

/-- Current-Reference classifier uniqueness supplies root-to-seed functionality. -/
theorem ClassifierGovernedRootSeedClosure.rootSeed_rightUnique
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (closure : ClassifierGovernedRootSeedClosure F cell)
    (left right : CellSource cell)
    (locus : SeedCoordinate F)
    (leftSeed : closure.rootSeed left locus)
    (rightSeed : closure.rootSeed right locus) :
    left = right := by
  apply closure.referenceSemantics.currentReference_rightUnique
    () locus left right
  · exact (closure.referenceSemantics_iff left locus).mpr leftSeed
  · exact (closure.referenceSemantics_iff right locus).mpr rightSeed

/-- The classifier-governed package realizes the manuscript package. -/
def ClassifierGovernedRootSeedClosure.toRootAuthenticScopeSeedClosure
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (closure : ClassifierGovernedRootSeedClosure F cell) :
    RootAuthenticScopeSeedClosure F cell where
  rootSeed := closure.rootSeed
  rootSeed_generated := closure.rootSeed_generated
  rootSeed_total := closure.rootSeed_total
  rootSeed_rightUnique := closure.rootSeed_rightUnique

/-- The relational kernel route derives finite reachable-role Hall occupancy. -/
theorem ClassifierGovernedRootSeedClosure.reachableRoleHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (closure : ClassifierGovernedRootSeedClosure F cell) :
    ReachableRoleHall F cell :=
  reachableRoleHall_of_rootAuthenticScopeSeedClosure
    closure.toRootAuthenticScopeSeedClosure

/--
Any already right-unique generated root-to-seed relation induces the lawful
singleton-classifier semantics consumed by the new kernel theorem.
-/
def referenceSemanticsOfRootAuthenticScopeSeedClosure
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (closure : RootAuthenticScopeSeedClosure F cell) :
    CurrentReferenceClassifierSemantics
      Unit (SeedCoordinate F) (CellSource cell) where
  currentReference := fun _ locus source => closure.rootSeed source locus
  classifierUniqueness := fun _ locus =>
    { lawful := fun classifier =>
        classifier = fun source => closure.rootSeed source locus
      classifier := fun source => closure.rootSeed source locus
      classifier_lawful := rfl
      uniqueClassifier := by
        intro other lawful
        exact lawful }
  claimClassifier_lawful := by
    intro _ locus reference referenceClaim
    funext candidate
    apply propext
    constructor
    · intro same
      subst candidate
      exact referenceClaim
    · intro candidateClaim
      exact closure.rootSeed_rightUnique
        candidate reference locus candidateClaim referenceClaim

/-- Hall occupancy constructs the classifier-governed package. -/
noncomputable def classifierGovernedRootSeedClosureOfHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (hall : ReachableRoleHall F cell) :
    ClassifierGovernedRootSeedClosure F cell := by
  let closure := rootAuthenticScopeSeedClosureOfReachableRoleHall hall
  exact
    { rootSeed := closure.rootSeed
      rootSeed_generated := closure.rootSeed_generated
      rootSeed_total := closure.rootSeed_total
      referenceSemantics :=
        referenceSemanticsOfRootAuthenticScopeSeedClosure closure
      referenceSemantics_iff := by
        intro source locus
        exact Iff.rfl }

/--
Exact-strength theorem for the kernel extension: inhabiting the complete
classifier-governed root-to-seed package has exactly Hall strength.
-/
theorem nonempty_classifierGovernedRootSeedClosure_iff_reachableRoleHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)} :
    Nonempty (ClassifierGovernedRootSeedClosure F cell) <->
      ReachableRoleHall F cell := by
  constructor
  · intro closure
    exact closure.some.reachableRoleHall
  · intro hall
    exact ⟨classifierGovernedRootSeedClosureOfHall hall⟩

end CurrentReferenceClassifierAdapter
end V2
end SunflowerAASC
