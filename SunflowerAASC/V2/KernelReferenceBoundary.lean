import MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.FixedRoleOccupancy

namespace SunflowerAASC
namespace V2
namespace KernelReferenceBoundary

open MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction

/--
A two-act regime satisfying every proposition in the pinned `KernelPackage`.
The current kernel surface treats fixed Reference as a unary proposition, so
it places no relation between two acts and one external role carrier.
-/
def twoActKernelRegime : ConstructionRegime Bool Unit where
  target := fun _ => ()
  sameTarget := fun _ _ => True
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

/-- The pinned four-clause kernel is inhabited in the two-act model. -/
theorem twoActKernelRegime_kernelPackage :
    KernelPackage twoActKernelRegime := by
  exact ⟨True.intro, fun _ _ => True.intro,
    fun _ => True.intro, fun _ => True.intro⟩

/-- Both distinct acts occupy the sole external role in the countermodel. -/
def collapsedRole (_ : Bool) : Unit := ()

theorem collapsedRole_not_injective :
    Not (Function.Injective collapsedRole) := by
  intro injective
  have false_eq_true : false = true := injective rfl
  cases false_eq_true

/--
Model-level boundary theorem: `KernelPackage` alone does not imply injectivity
of an arbitrary concrete role map. A relational fixed-Reference/no-second-
classifier theorem is genuinely additional to the pinned unary surface.
-/
theorem kernelPackage_alone_does_not_force_role_injective :
    KernelPackage twoActKernelRegime ∧
      Not (Function.Injective collapsedRole) :=
  ⟨twoActKernelRegime_kernelPackage, collapsedRole_not_injective⟩

end KernelReferenceBoundary
end V2
end SunflowerAASC
