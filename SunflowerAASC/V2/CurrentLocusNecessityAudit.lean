import SunflowerAASC.V2.AdversarialCurrentLocusClosure

namespace SunflowerAASC
namespace V2
namespace CurrentLocusNecessityAudit

open MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction

/-!
Small-model audit of the current kernel import boundary.

The abstract `KernelPackage` governs admissibility, standing, fixed Reference,
and irreversible failure, but its fields do not mention generated continuation
loci. These examples show that sourcewise current-locus population and
collision-free Current-Reference binding cannot be derived from that package
alone. They must come either from a stronger, independently mechanized kernel
theorem or from the concrete generated incidence relation.
-/

/-- A fully governed two-source regime with faithful source identity. -/
def twoSourceKernelRegime : ConstructionRegime Bool Bool where
  target := id
  sameTarget := Eq
  admissible := fun _ => True
  standing := fun _ => True
  referenceFixed := fun _ => True
  irreversibleFailure := fun _ => True
  licensedContinuation := fun _ _ => True
  targetIdentityFixed := True
  stepEligibilityFixed := True
  actTimeFailureStable := True
  boundaryFixed := True
  governedConstructionUse := True
  noRawTraceSuffices := True
  noSelectorImport := True
  noDomainShift := True
  noBookkeepingOnly := True

theorem twoSourceKernelRegime_kernelPackage :
    MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.KernelPackage
      twoSourceKernelRegime := by
  exact
    ⟨trivial, (fun _ _ => trivial), (fun _ => trivial),
      (fun _ => trivial)⟩

/-- Both sources are live and standing, but every generated locus is null. -/
def allNullGeneratedSystem : GeneratedCurrentLocusSystem Bool Unit where
  generated := fun _ _ => True
  currentOccupancy := fun _ _ => False
  sourceStanding := fun _ => True
  liveSamePackage := fun _ => True
  generated_nonempty := fun _ => ⟨(), trivial⟩
  occupancy_generated := by
    intro _source _locus occupancy
    exact False.elim occupancy

theorem allNullGeneratedSystem_not_nullExcluded :
    Not (CurrentLocusNullExclusion allNullGeneratedSystem) := by
  intro exclusion
  have allNull :
      AllGeneratedCurrentLociNull allNullGeneratedSystem false := by
    intro _locus _generated occupancy
    exact occupancy
  exact
    (exclusion.allNullLosesStanding false trivial allNull) trivial

/--
The currently imported kernel roles do not by themselves imply the
manuscript's no-standing-sink clause.
-/
theorem kernelPackage_with_allNull_generated_system :
    MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.KernelPackage
        twoSourceKernelRegime /\
      Not (CurrentLocusNullExclusion allNullGeneratedSystem) :=
  ⟨twoSourceKernelRegime_kernelPackage,
    allNullGeneratedSystem_not_nullExcluded⟩

/-- Both distinct sources occupy the one generated locus. -/
def collidingGeneratedSystem : GeneratedCurrentLocusSystem Bool Unit where
  generated := fun _ _ => True
  currentOccupancy := fun _ _ => True
  sourceStanding := fun _ => True
  liveSamePackage := fun _ => True
  generated_nonempty := fun _ => ⟨(), trivial⟩
  occupancy_generated := fun _ _ _ => trivial

/-- Sourcewise population and null exclusion both hold in the collision model. -/
def collidingGeneratedPopulation :
    KernelForcedCurrentLocusPopulation collidingGeneratedSystem where
  sourceStanding_holds := fun _ => trivial
  liveSamePackage_holds := fun _ => trivial
  nullExclusion :=
    { allNullLosesStanding := by
        intro source _live allNull _standing
        exact allNull () trivial trivial }

/--
No lawful Current-Reference binding can make two distinct source identities
occupy one literal current locus in one package.
-/
theorem collidingGeneratedSystem_not_referenceBindable :
    Not (Nonempty (CurrentLocusReferenceBinding
      Unit Bool Unit collidingGeneratedSystem)) := by
  intro bindingPackage
  let binding := bindingPackage.some
  have impossible : false = true :=
    binding.occupancy_rightUnique false true () trivial trivial
  simp at impossible

/--
Even after sourcewise population is available, the imported kernel package
does not manufacture the collision law for an unrelated generated relation.
-/
theorem kernelPopulation_without_referenceBinding :
    MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.KernelPackage
        twoSourceKernelRegime /\
      Nonempty (KernelForcedCurrentLocusPopulation
        collidingGeneratedSystem) /\
      Not (Nonempty (CurrentLocusReferenceBinding
        Unit Bool Unit collidingGeneratedSystem)) :=
  ⟨twoSourceKernelRegime_kernelPackage,
    ⟨collidingGeneratedPopulation⟩,
    collidingGeneratedSystem_not_referenceBindable⟩

end CurrentLocusNecessityAudit
end V2
end SunflowerAASC
