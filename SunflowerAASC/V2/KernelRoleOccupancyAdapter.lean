import MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.FixedRoleOccupancy
import SunflowerAASC.V2.MechanizedKernelImport
import SunflowerAASC.V2.ReachableRoleOccupancy

namespace SunflowerAASC
namespace V2
namespace KernelRoleOccupancyAdapter

open GeneratedIncidenceTower
open GeneratedSeedCapacity
open ReachableRoleOccupancy
open MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction

/-- The complete fixed-endpoint incidence reference of one initial source. -/
abbrev EndpointReference
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)) :=
  {edge // edge ∈ F.edges} -> Prop

def sourceReference
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F))
    (source : CellSource cell) : EndpointReference F :=
  MinimalBlocker.globalEndpointIncidenceProfile F source.coordinate

/-- Private witnesses make the source reference identity faithful. -/
theorem sourceReference_injective
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F)) :
    Function.Injective (sourceReference F cell) := by
  intro left right sameReference
  apply Subtype.ext
  exact MinimalBlocker.globalEndpointIncidenceProfile_injective F
    (by simpa [sourceReference] using sameReference)

/--
Pull a kernel-governed endpoint regime back to the finite source cell while
using the concrete incidence profile as its reference target.
-/
def cellReferenceRegime
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F))
    (R : ConstructionRegime
      (Concrete.UniformSetFamily alpha (baseRank + steps + 1))
      (Concrete.UniformSetFamily alpha (baseRank + steps + 1))) :
    ConstructionRegime (CellSource cell) (EndpointReference F) where
  target := sourceReference F cell
  sameTarget := Eq
  admissible := fun _ => R.admissible F
  standing := fun _ => R.standing F
  referenceFixed := fun _ => R.referenceFixed F
  irreversibleFailure := fun _ => R.irreversibleFailure F
  licensedContinuation := fun _ _ => R.licensedContinuation F F
  targetIdentityFixed := Function.Injective (sourceReference F cell)
  stepEligibilityFixed := R.stepEligibilityFixed
  actTimeFailureStable := R.actTimeFailureStable
  boundaryFixed := R.boundaryFixed
  governedConstructionUse := R.governedConstructionUse
  noRawTraceSuffices := R.noRawTraceSuffices
  noSelectorImport := R.noSelectorImport
  noDomainShift := R.noDomainShift
  noBookkeepingOnly := R.noBookkeepingOnly

/-- Kernel roles transfer pointwise to the finite source cell. -/
theorem cellReferenceRegime_kernelPackage
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F))
    (R : ConstructionRegime
      (Concrete.UniformSetFamily alpha (baseRank + steps + 1))
      (Concrete.UniformSetFamily alpha (baseRank + steps + 1)))
    (kernel :
      MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.KernelPackage R) :
    MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.KernelPackage
      (cellReferenceRegime F cell R) := by
  rcases kernel with
    ⟨boundary, standingAdmissible, referenceFixed, irreversible⟩
  exact ⟨boundary,
    (fun _ standing => standingAdmissible F standing),
    (fun _ => referenceFixed F),
    (fun _ => irreversible F)⟩

/--
The target-specific identity transport. It contains a generated reachable role
for every source and says that a shared role preserves the already faithful
fixed-endpoint reference. Injectivity is not a field.
-/
structure GeneratedRoleReferenceTransport
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F)) where
  carrierOf : CellSource cell ->
    {x // x ∈ MinimalBlocker.minimalBlocker
      (terminalFamily baseRank steps F)}
  reachable : forall source,
    ReachesTerminalCarrier source.coordinate (carrierOf source)
  sharedRolePreservesReference :
    forall left right : CellSource cell,
      carrierOf left = carrierOf right ->
        sourceReference F cell left = sourceReference F cell right

/-- Reference preservation already makes the concrete role map injective. -/
theorem GeneratedRoleReferenceTransport.referenceCarrier_injective
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (transport : GeneratedRoleReferenceTransport F cell) :
    Function.Injective transport.carrierOf := by
  intro left right sameRole
  exact sourceReference_injective F cell
    (transport.sharedRolePreservesReference left right sameRole)

/-- A reference-preserving generated transport supplies Hall occupancy. -/
theorem GeneratedRoleReferenceTransport.reachableRoleHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (transport : GeneratedRoleReferenceTransport F cell) :
    ReachableRoleHall F cell := by
  apply reachableRoleHall_iff_exists_injective_selector.mpr
  exact ⟨transport.carrierOf, transport.referenceCarrier_injective,
    transport.reachable⟩

/-- Hall occupancy constructs a generated fixed-reference transport. -/
noncomputable def generatedRoleReferenceTransportOfHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (hall : ReachableRoleHall F cell) :
    GeneratedRoleReferenceTransport F cell := by
  let witness := reachableRoleHall_iff_exists_injective_selector.mp hall
  let carrierOf := Classical.choose witness
  have specification := Classical.choose_spec witness
  exact {
    carrierOf := carrierOf
    reachable := specification.2
    sharedRolePreservesReference := by
      intro left right sameRole
      exact congrArg (sourceReference F cell)
        (specification.1 sameRole) }

/--
Exact semantic boundary: fixed-reference transport and Hall occupancy carry the
same mathematical content. The kernel adapter does not hide a weaker premise.
-/
theorem nonempty_generatedRoleReferenceTransport_iff_reachableRoleHall
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)} :
    Nonempty (GeneratedRoleReferenceTransport F cell) ↔
      ReachableRoleHall F cell := by
  constructor
  · intro transport
    exact transport.some.reachableRoleHall
  · intro hall
    exact ⟨generatedRoleReferenceTransportOfHall hall⟩

/-- The concrete transport realizes the generic kernel fixed-role semantics. -/
def GeneratedRoleReferenceTransport.toFixedRoleSemantics
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (transport : GeneratedRoleReferenceTransport F cell)
    (R : ConstructionRegime
      (Concrete.UniformSetFamily alpha (baseRank + steps + 1))
      (Concrete.UniformSetFamily alpha (baseRank + steps + 1)))
    (standingAtEndpoint : R.standing F) :
    FixedRoleReferenceSemantics
      (Role := {x // x ∈ MinimalBlocker.minimalBlocker
        (terminalFamily baseRank steps F)})
      (cellReferenceRegime F cell R) where
  role := transport.carrierOf
  standingBearing := fun _ => standingAtEndpoint
  targetFaithful := sourceReference_injective F cell
  sameTarget_extensional := by
    intro left right same
    exact same
  sharedRolePreservesReference := by
    intro left right _ _ _ _ _ _ sameRole
    exact transport.sharedRolePreservesReference left right sameRole

/-- Kernel reference semantics makes the transported role collision-free. -/
theorem GeneratedRoleReferenceTransport.carrierOf_injective
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (transport : GeneratedRoleReferenceTransport F cell)
    (R : ConstructionRegime
      (Concrete.UniformSetFamily alpha (baseRank + steps + 1))
      (Concrete.UniformSetFamily alpha (baseRank + steps + 1)))
    (kernel :
      MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.KernelPackage R)
    (standingAtEndpoint : R.standing F) :
    Function.Injective transport.carrierOf := by
  exact (transport.toFixedRoleSemantics R standingAtEndpoint).role_injective
    (cellReferenceRegime_kernelPackage F cell R kernel)

/-- The target-specific reference transport constructs the relation bridge. -/
noncomputable def GeneratedRoleReferenceTransport.toStandingPathBridge
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (transport : GeneratedRoleReferenceTransport F cell)
    (R : ConstructionRegime
      (Concrete.UniformSetFamily alpha (baseRank + steps + 1))
      (Concrete.UniformSetFamily alpha (baseRank + steps + 1)))
    (kernel :
      MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.KernelPackage R)
    (standingAtEndpoint : R.standing F) :
    GeneratedSeedCapacity.KernelFaithfulStandingPathBridge F cell :=
  standingPathBridgeOfInjectiveSelector
    transport.carrierOf
    (transport.carrierOf_injective R kernel standingAtEndpoint)
    transport.reachable

/-- The imported endpoint kernel is standing-bearing at every fixed family. -/
theorem endpointConstructionRegime_standing
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch)
    (corpus : KernelFirstCorpusMachinery S)
    (family : S.Family) :
    (MechanizedKernelImport.endpointConstructionRegime
      endpointUse corpus).standing family :=
  (corpus.kernelAtEndpointUse endpointUse).standing_holds

/--
The fully wired cross-repository adapter. The imported kernel supplies all
generic governance premises; the transport supplies only terminal reference
preservation for the generated finite role map.
-/
noncomputable def GeneratedRoleReferenceTransport.toImportedKernelBridge
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (transport : GeneratedRoleReferenceTransport F cell)
    (endpointUse : LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha
        (baseRank + steps + 1) 3)
      (fun family => Not (Concrete.HasSunflower 3 family)))
    (corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha
        (baseRank + steps + 1) 3)) :
    GeneratedSeedCapacity.KernelFaithfulStandingPathBridge F cell :=
  transport.toStandingPathBridge
    (MechanizedKernelImport.endpointConstructionRegime endpointUse corpus)
    (MechanizedKernelImport.endpointConstructionRegime_kernelPackage
      endpointUse corpus)
    (endpointConstructionRegime_standing endpointUse corpus F)

end KernelRoleOccupancyAdapter
end V2
end SunflowerAASC
