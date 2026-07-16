import SunflowerAASC.V2.ExplicitReductionPotential
import SunflowerAASC.V2.FixedIdentityPopulation
import SunflowerAASC.V2.MergeDispositionClosure

namespace SunflowerAASC
namespace V2
namespace TerminalRoleOccupancyCloseout

open ExplicitReductionPotential
open FixedIdentityPopulation
open InternalTensorProfiles
open MergeDispositionClosure
open PairLocalizedReferenceDivergence
open ResidualParentExhaustion

/-!
This module expands the manuscript-specific terminal handoff into its typed
proof components.

The four AASC roles remain skin, bounded certificate, tensor split, and
sunflower. Lower-rank reconstruction and scope change are not extra standing
roles: they are certified reduction exits. A certificate-terminal package
forbids every such exit, so bivalent skin/non-skin exhaustion leaves only skin,
and quotient finality turns skin equivalence into literal source identity.
-/

/--
Every non-skin terminal branch must become one of the three certificate kinds
already forbidden by `TerminalPackage`. Bounded and lower-rank branches are
direct closeouts; tensor and scope branches are endpoint-faithful splits; a
sunflower branch carries the literal sunflower certificate.
-/
inductive CertifiedTerminalExit
    {Pkg : Type}
    (measure : Pkg -> ReductionPotential)
    (Endpoint : Pkg -> Prop)
    (PreservesTargetScope : Pkg -> List Pkg -> Prop)
    (SunflowerCertificate : Pkg -> Prop)
    (P : Pkg) : Type
  | boundedFiber
      (certificate :
        Nonempty (DirectCloseoutCertificate measure Endpoint P))
  | tensorSplit
      (certificate :
        Nonempty
          (EndpointFaithfulSplit measure Endpoint PreservesTargetScope P))
  | sunflower
      (certificate : SunflowerCertificate P)
  | lowerRankReconstruction
      (certificate :
        Nonempty (DirectCloseoutCertificate measure Endpoint P))
  | scopeChange
      (certificate :
        Nonempty
          (EndpointFaithfulSplit measure Endpoint PreservesTargetScope P))

/-- Certificate terminality makes every certified non-skin exit impossible. -/
theorem CertifiedTerminalExit.impossible
    {Pkg : Type}
    {measure : Pkg -> ReductionPotential}
    {Endpoint : Pkg -> Prop}
    {PreservesTargetScope : Pkg -> List Pkg -> Prop}
    {SunflowerCertificate : Pkg -> Prop}
    {P : Pkg}
    (exit : CertifiedTerminalExit measure Endpoint PreservesTargetScope
      SunflowerCertificate P)
    (terminal :
      TerminalPackage measure Endpoint PreservesTargetScope
        SunflowerCertificate P) :
    False := by
  cases exit with
  | boundedFiber certificate =>
      exact terminal.2.1 certificate
  | tensorSplit certificate =>
      exact terminal.2.2 certificate
  | sunflower certificate =>
      exact terminal.1 certificate
  | lowerRankReconstruction certificate =>
      exact terminal.2.1 certificate
  | scopeChange certificate =>
      exact terminal.2.2 certificate

/--
Abstract fixed-role occupancy after all combinatorial distinctions have been
made explicit. Injectivity is not a field. Equal roles are split bivalently
into skin or a certified non-skin exit.
-/
structure TerminalRoleOccupancyExhaustion
    {Pkg Occupant Role : Type}
    (measure : Pkg -> ReductionPotential)
    (Endpoint : Pkg -> Prop)
    (PreservesTargetScope : Pkg -> List Pkg -> Prop)
    (SunflowerCertificate : Pkg -> Prop)
    (P : Pkg) where
  role : Occupant -> Role
  skinEquivalent : Occupant -> Occupant -> Prop
  skinFinality :
    forall left right, skinEquivalent left right -> left = right
  nonSkinExhaustive :
    forall left right,
      role left = role right ->
      Not (skinEquivalent left right) ->
      CertifiedTerminalExit measure Endpoint PreservesTargetScope
        SunflowerCertificate P

/-- Standing-bearing skin status is bivalent, not graded. -/
theorem TerminalRoleOccupancyExhaustion.skin_bivalent
    {Pkg Occupant Role : Type}
    {measure : Pkg -> ReductionPotential}
    {Endpoint : Pkg -> Prop}
    {PreservesTargetScope : Pkg -> List Pkg -> Prop}
    {SunflowerCertificate : Pkg -> Prop}
    {P : Pkg}
    (Exhaustion : TerminalRoleOccupancyExhaustion
      (Occupant := Occupant) (Role := Role)
      measure Endpoint PreservesTargetScope SunflowerCertificate P)
    (left right : Occupant) :
    Exhaustion.skinEquivalent left right \/
      Not (Exhaustion.skinEquivalent left right) := by
  exact Classical.em _

/--
Kernel-faithful terminal role occupancy is rigid. The proof uses only bivalent
skin/non-skin exhaustion, skin finality, and certificate terminality.
-/
theorem TerminalRoleOccupancyExhaustion.role_injective
    {Pkg Occupant Role : Type}
    {measure : Pkg -> ReductionPotential}
    {Endpoint : Pkg -> Prop}
    {PreservesTargetScope : Pkg -> List Pkg -> Prop}
    {SunflowerCertificate : Pkg -> Prop}
    {P : Pkg}
    (Exhaustion : TerminalRoleOccupancyExhaustion
      (Occupant := Occupant) (Role := Role)
      measure Endpoint PreservesTargetScope SunflowerCertificate P)
    (terminal :
      TerminalPackage measure Endpoint PreservesTargetScope
        SunflowerCertificate P) :
    Function.Injective Exhaustion.role := by
  intro left right sameRole
  rcases Exhaustion.skin_bivalent left right with skin | nonSkin
  · exact Exhaustion.skinFinality left right skin
  · exact False.elim <|
      (Exhaustion.nonSkinExhaustive left right sameRole nonSkin).impossible
        terminal

/--
The complete four-role population at one fixed support and finite identity.
This is the exhaustion half only: bounded, tensor, and sunflower outcomes have
not yet been discharged.
-/
structure AASCFourRoleIdentityPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) where
  tensorProfileBound_positive : 0 < tensorProfileBound
  identityOf :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      RefinedConstraintSignature tensorProfileBound
  skinEquivalent :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  boundedCertificateOutcome :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  tensorSplitOutcome :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  sameIdentityExhaustive :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩ ->
      identityOf left = identityOf right ->
      skinEquivalent left right \/
        boundedCertificateOutcome left right \/
        tensorSplitOutcome left right \/
        Concrete.HasSunflower k F
  skinFinality :
    forall left right, skinEquivalent left right -> left = right

/--
The impossibility half of four-role population. At equal finite identity the
bounded branch is quotient-final, the tensor branch is prime-incompatible, and
the sunflower branch is endpoint-incompatible.
-/
structure AASCFourRoleIdentityCloseout
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Population : AASCFourRoleIdentityPopulation
      (tensorProfileBound := tensorProfileBound) F noSunflower) where
  boundedCertificateIdentityFinality :
    forall left right,
      Population.boundedCertificateOutcome left right ->
      left = right
  tensorSplitExcluded :
    forall left right, Population.tensorSplitOutcome left right -> False
  sunflowerExcluded :
    Concrete.HasSunflower k F -> False

/-- The populated four-role ledger together with its terminal closeout. -/
structure AASCFourRoleIdentityClosure
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) where
  population : AASCFourRoleIdentityPopulation
    (tensorProfileBound := tensorProfileBound) F noSunflower
  closeout : AASCFourRoleIdentityCloseout population

/-- Four-role exhaustion and impossibility derive fixed-identity finality. -/
theorem AASCFourRoleIdentityPopulation.collision
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Population : AASCFourRoleIdentityPopulation
      (tensorProfileBound := tensorProfileBound) F noSunflower)
    (Closeout : AASCFourRoleIdentityCloseout Population)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameSupport :
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩)
    (sameIdentity : Population.identityOf left = Population.identityOf right) :
    left = right := by
  rcases Population.sameIdentityExhaustive
      left right sameSupport sameIdentity with skin | boundedOrTensorOrSunflower
  · exact Population.skinFinality left right skin
  · rcases boundedOrTensorOrSunflower with bounded | tensorOrSunflower
    · exact Closeout.boundedCertificateIdentityFinality left right bounded
    · rcases tensorOrSunflower with tensor | sunflower
      · exact False.elim <| Closeout.tensorSplitExcluded left right tensor
      · exact False.elim <| Closeout.sunflowerExcluded sunflower

/-- The explicit four-role closeout constructs the existing fixed identity. -/
def AASCFourRoleIdentityPopulation.toFixedIdentityRealization
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Population : AASCFourRoleIdentityPopulation
      (tensorProfileBound := tensorProfileBound) F noSunflower)
    (Closeout : AASCFourRoleIdentityCloseout Population) :
    KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower where
  tensorProfileBound_positive := Population.tensorProfileBound_positive
  identityOf := Population.identityOf
  identityFinality := by
    intro left right sameSupport sameIdentity
    exact Population.collision Closeout left right sameSupport sameIdentity

/-- The bundled four-role closure constructs fixed endpoint identity. -/
def AASCFourRoleIdentityClosure.toFixedIdentityRealization
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Closure : AASCFourRoleIdentityClosure
      (tensorProfileBound := tensorProfileBound) F noSunflower) :
    KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower :=
  Closure.population.toFixedIdentityRealization Closure.closeout

/-- The explicit four-role closeout also supplies the legacy same-side surface. -/
noncomputable def AASCFourRoleIdentityPopulation.toAASCSameSideIdentityExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Population : AASCFourRoleIdentityPopulation
      (tensorProfileBound := tensorProfileBound) F noSunflower)
    (Closeout : AASCFourRoleIdentityCloseout Population) :
    AASCSameSideIdentityExhaustion
      (tensorProfileBound := tensorProfileBound) F noSunflower :=
  (Population.toFixedIdentityRealization Closeout)
    |>.toAASCSameSideIdentityExhaustion

/-- The bundled four-role closure supplies the legacy same-side surface. -/
noncomputable def AASCFourRoleIdentityClosure.toAASCSameSideIdentityExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Closure : AASCFourRoleIdentityClosure
      (tensorProfileBound := tensorProfileBound) F noSunflower) :
    AASCSameSideIdentityExhaustion
      (tensorProfileBound := tensorProfileBound) F noSunflower :=
  Closure.population.toAASCSameSideIdentityExhaustion Closure.closeout

/--
Any already proved fixed identity has a conservative four-role presentation.
This adapter preserves compatibility; it is not used to claim that the
four-role population was independently reconstructed.
-/
def fourRoleIdentityPopulationOfFixedIdentity
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Realization : KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower) :
    AASCFourRoleIdentityPopulation
      (tensorProfileBound := tensorProfileBound) F noSunflower where
  tensorProfileBound_positive := Realization.tensorProfileBound_positive
  identityOf := Realization.identityOf
  skinEquivalent := fun left right => left = right
  boundedCertificateOutcome := fun _ _ => False
  tensorSplitOutcome := fun _ _ => False
  sameIdentityExhaustive := by
    intro left right sameSupport sameIdentity
    exact Or.inl <| Realization.identityFinality
      left right sameSupport sameIdentity
  skinFinality := fun _ _ same => same

/-- Compatibility closeout for an already proved fixed identity. -/
def fourRoleIdentityCloseoutOfFixedIdentity
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Realization : KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower) :
    AASCFourRoleIdentityCloseout
      (fourRoleIdentityPopulationOfFixedIdentity Realization) where
  boundedCertificateIdentityFinality := fun _ _ impossible =>
    False.elim impossible
  tensorSplitExcluded := fun _ _ impossible => impossible
  sunflowerExcluded := noSunflower

/-- Compatibility bundle for an already proved fixed identity. -/
def fourRoleIdentityClosureOfFixedIdentity
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Realization : KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower) :
    AASCFourRoleIdentityClosure
      (tensorProfileBound := tensorProfileBound) F noSunflower where
  population := fourRoleIdentityPopulationOfFixedIdentity Realization
  closeout := fourRoleIdentityCloseoutOfFixedIdentity Realization

/-- Four-role closure and fixed identity have exactly the same endpoint strength. -/
theorem nonempty_fourRoleIdentityClosure_iff_fixedIdentityRealization
    {alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)} :
    Nonempty (AASCFourRoleIdentityClosure
      (tensorProfileBound := tensorProfileBound) F noSunflower) <->
      Nonempty (KernelFaithfulFixedIdentityRealization
        (tensorProfileBound := tensorProfileBound) F noSunflower) := by
  constructor
  · intro Closure
    exact ⟨Closure.some.toFixedIdentityRealization⟩
  · intro Realization
    exact ⟨fourRoleIdentityClosureOfFixedIdentity Realization.some⟩

/--
Certificate realization of every non-skin branch of a four-role population.
No source injectivity, finite-code injectivity, support-fibre bound, or endpoint
bound is a field.
-/
structure CertifiedAASCFourRoleBranchRealization
    {Pkg alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    (measure : Pkg -> ReductionPotential)
    (Endpoint : Pkg -> Prop)
    (PreservesTargetScope : Pkg -> List Pkg -> Prop)
    (SunflowerCertificate : Pkg -> Prop)
    (P : Pkg)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (Population : AASCFourRoleIdentityPopulation
      (tensorProfileBound := tensorProfileBound) F noSunflower) where
  boundedCertificate :
    forall left right,
      Population.boundedCertificateOutcome left right ->
      Nonempty (DirectCloseoutCertificate measure Endpoint P)
  tensorSplitCertificate :
    forall left right,
      Population.tensorSplitOutcome left right ->
      Nonempty
        (EndpointFaithfulSplit measure Endpoint PreservesTargetScope P)
  sunflowerCertificate :
    Concrete.HasSunflower k F -> SunflowerCertificate P

/--
Certificate terminality mechanically supplies the impossibility half of the
four-role closeout.
-/
def CertifiedAASCFourRoleBranchRealization.toIdentityCloseout
    {Pkg alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {measure : Pkg -> ReductionPotential}
    {Endpoint : Pkg -> Prop}
    {PreservesTargetScope : Pkg -> List Pkg -> Prop}
    {SunflowerCertificate : Pkg -> Prop}
    {P : Pkg}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {Population : AASCFourRoleIdentityPopulation
      (tensorProfileBound := tensorProfileBound) F noSunflower}
    (Realization : CertifiedAASCFourRoleBranchRealization measure Endpoint
      PreservesTargetScope SunflowerCertificate P F noSunflower Population)
    (terminal :
      TerminalPackage measure Endpoint PreservesTargetScope
        SunflowerCertificate P) :
    AASCFourRoleIdentityCloseout Population where
  boundedCertificateIdentityFinality := by
    intro left right bounded
    exact False.elim <| terminal.2.1 <|
      Realization.boundedCertificate left right bounded
  tensorSplitExcluded := by
    intro left right tensor
    exact terminal.2.2 <|
      Realization.tensorSplitCertificate left right tensor
  sunflowerExcluded := by
    intro sunflower
    exact terminal.1 <| Realization.sunflowerCertificate sunflower

/-- Certified branch realization plus terminality constructs fixed identity. -/
def CertifiedAASCFourRoleBranchRealization.toFixedIdentityRealization
    {Pkg alpha : Type}
    [DecidableEq alpha]
    {r k tensorProfileBound : Nat}
    {measure : Pkg -> ReductionPotential}
    {Endpoint : Pkg -> Prop}
    {PreservesTargetScope : Pkg -> List Pkg -> Prop}
    {SunflowerCertificate : Pkg -> Prop}
    {P : Pkg}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {Population : AASCFourRoleIdentityPopulation
      (tensorProfileBound := tensorProfileBound) F noSunflower}
    (Realization : CertifiedAASCFourRoleBranchRealization measure Endpoint
      PreservesTargetScope SunflowerCertificate P F noSunflower Population)
    (terminal :
      TerminalPackage measure Endpoint PreservesTargetScope
        SunflowerCertificate P) :
    KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower :=
  Population.toFixedIdentityRealization
    (Realization.toIdentityCloseout terminal)

/--
The already constructed fine-fibre merge ledger needs only two certificate
maps: bounded charges settle directly, and strict lower-rank reconstructions
settle through the direct reconstruction certificate.
-/
structure FineFiberCertifiedDischarge
    {Pkg alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (measure : Pkg -> ReductionPotential)
    (Endpoint : Pkg -> Prop)
    (PreservesTargetScope : Pkg -> List Pkg -> Prop)
    (SunflowerCertificate : Pkg -> Prop)
    (P : Pkg)
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower 3 F)) where
  boundedChargeCertificate :
    forall left right,
      BoundedResidualCharge F noSunflower left right ->
      Nonempty (DirectCloseoutCertificate measure Endpoint P)
  rankSplitCertificate :
    forall left right,
      StrictLowerRankReconstruction F left right ->
      Nonempty (DirectCloseoutCertificate measure Endpoint P)

/-- A genuine fine-fibre merge produces a certified terminal exit. -/
noncomputable def fineFiberCertifiedExitOfMerge
    {Pkg alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {measure : Pkg -> ReductionPotential}
    {Endpoint : Pkg -> Prop}
    {PreservesTargetScope : Pkg -> List Pkg -> Prop}
    {SunflowerCertificate : Pkg -> Prop}
    {P : Pkg}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {classifiers : ResidualParentClassifiers F}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (Discharge : FineFiberCertifiedDischarge measure Endpoint
      PreservesTargetScope SunflowerCertificate P F noSunflower)
    (agreement : FineFiberAgreement
      F noSunflower classifiers left right)
    (merge : OneStepPairMerge F left right) :
    CertifiedTerminalExit measure Endpoint PreservesTargetScope
      SunflowerCertificate P := by
  let disposition :=
    Classical.choice (fineFiberMerge_disposition agreement merge)
  cases disposition with
  | boundedCharge charge =>
      exact CertifiedTerminalExit.boundedFiber
        (Discharge.boundedChargeCertificate left right charge)
  | rankSplit reconstruction =>
      exact CertifiedTerminalExit.lowerRankReconstruction
        (Discharge.rankSplitCertificate left right reconstruction)

/--
A certificate-terminal package has no unresolved one-step merge inside a
genuine support/profile/role/Venn fibre.
-/
theorem noFineFiberOneStepMerge_at_terminal
    {Pkg alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {measure : Pkg -> ReductionPotential}
    {Endpoint : Pkg -> Prop}
    {PreservesTargetScope : Pkg -> List Pkg -> Prop}
    {SunflowerCertificate : Pkg -> Prop}
    {P : Pkg}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {classifiers : ResidualParentClassifiers F}
    {left right : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (Discharge : FineFiberCertifiedDischarge measure Endpoint
      PreservesTargetScope SunflowerCertificate P F noSunflower)
    (terminal :
      TerminalPackage measure Endpoint PreservesTargetScope
        SunflowerCertificate P)
    (agreement : FineFiberAgreement
      F noSunflower classifiers left right) :
    OneStepPairMerge F left right -> False := by
  intro merge
  exact (fineFiberCertifiedExitOfMerge Discharge agreement merge).impossible
    terminal

/--
Fine-fibre semantics for a finite fixed identity. The two nontrivial fields are
the exact remaining combinatorial bridges: equal identity must determine the
genuine fine fibre, and a surviving non-skin distinction must realize a merge.
-/
structure FineFiberFixedIdentitySemantics
    {alpha : Type}
    [DecidableEq alpha]
    {r tensorProfileBound : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower 3 F))
    (classifiers : ResidualParentClassifiers F) where
  tensorProfileBound_positive : 0 < tensorProfileBound
  identityOf :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      RefinedConstraintSignature tensorProfileBound
  skinEquivalent :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  skinFinality :
    forall left right, skinEquivalent left right -> left = right
  sameIdentityFineFiber :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩ ->
      identityOf left = identityOf right ->
      FineFiberAgreement F noSunflower classifiers left right
  nonSkinSameIdentityMerge :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩ ->
      identityOf left = identityOf right ->
      Not (skinEquivalent left right) ->
      OneStepPairMerge F left right

/--
Fine-fibre merge exhaustion plus certificate terminality proves fixed identity.
This is the concrete post-exhaustion replacement for raw root-to-seed
injectivity.
-/
theorem FineFiberFixedIdentitySemantics.identityFinality_of_terminal
    {Pkg alpha : Type}
    [DecidableEq alpha]
    {r tensorProfileBound : Nat}
    {measure : Pkg -> ReductionPotential}
    {Endpoint : Pkg -> Prop}
    {PreservesTargetScope : Pkg -> List Pkg -> Prop}
    {SunflowerCertificate : Pkg -> Prop}
    {P : Pkg}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {classifiers : ResidualParentClassifiers F}
    (Semantics : FineFiberFixedIdentitySemantics
      (tensorProfileBound := tensorProfileBound) F noSunflower classifiers)
    (Discharge : FineFiberCertifiedDischarge measure Endpoint
      PreservesTargetScope SunflowerCertificate P F noSunflower)
    (terminal :
      TerminalPackage measure Endpoint PreservesTargetScope
        SunflowerCertificate P)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameSupport :
      BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        BlockerSupportLayers.canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩)
    (sameIdentity : Semantics.identityOf left = Semantics.identityOf right) :
    left = right := by
  by_cases skin : Semantics.skinEquivalent left right
  · exact Semantics.skinFinality left right skin
  · have agreement :=
      Semantics.sameIdentityFineFiber left right sameSupport sameIdentity
    have merge :=
      Semantics.nonSkinSameIdentityMerge
        left right sameSupport sameIdentity skin
    exact False.elim <|
      noFineFiberOneStepMerge_at_terminal
        Discharge terminal agreement merge

/-- The complete fine-fibre terminal derivation constructs fixed identity. -/
def FineFiberFixedIdentitySemantics.toFixedIdentityRealization
    {Pkg alpha : Type}
    [DecidableEq alpha]
    {r tensorProfileBound : Nat}
    {measure : Pkg -> ReductionPotential}
    {Endpoint : Pkg -> Prop}
    {PreservesTargetScope : Pkg -> List Pkg -> Prop}
    {SunflowerCertificate : Pkg -> Prop}
    {P : Pkg}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    {classifiers : ResidualParentClassifiers F}
    (Semantics : FineFiberFixedIdentitySemantics
      (tensorProfileBound := tensorProfileBound) F noSunflower classifiers)
    (Discharge : FineFiberCertifiedDischarge measure Endpoint
      PreservesTargetScope SunflowerCertificate P F noSunflower)
    (terminal :
      TerminalPackage measure Endpoint PreservesTargetScope
        SunflowerCertificate P) :
    KernelFaithfulFixedIdentityRealization
      (tensorProfileBound := tensorProfileBound) F noSunflower where
  tensorProfileBound_positive := Semantics.tensorProfileBound_positive
  identityOf := Semantics.identityOf
  identityFinality := by
    intro left right sameSupport sameIdentity
    exact Semantics.identityFinality_of_terminal
      Discharge terminal left right sameSupport sameIdentity

end TerminalRoleOccupancyCloseout
end V2
end SunflowerAASC
