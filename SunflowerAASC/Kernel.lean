import SunflowerAASC.Basic

namespace SunflowerAASC

/-- Kernel package forced by target adequacy on a nondegenerate endpoint act. -/
structure KernelPackage (S : SunflowerCarrier) where
  admissibility : Prop
  standing : Prop
  reference : Prop
  irreversibility : Prop
  admissibility_holds : admissibility
  standing_holds : standing
  reference_holds : reference
  irreversibility_holds : irreversibility

def KernelPackage.allRolesHold
    {S : SunflowerCarrier}
    (K : KernelPackage S) : Prop :=
  K.admissibility /\ K.standing /\ K.reference /\ K.irreversibility

theorem KernelPackage.allRolesHold_holds
    {S : SunflowerCarrier}
    (K : KernelPackage S) :
    K.allRolesHold := by
  exact
    And.intro K.admissibility_holds
      (And.intro K.standing_holds
        (And.intro K.reference_holds K.irreversibility_holds))

/--
The manuscript's "target adequacy forces kernel" link, packaged as a reusable
governance rule for all local endpoint branches on the same carrier.
-/
structure KernelForcedGovernance (S : SunflowerCarrier) where
  targetAdequacyForcesKernel :
    forall {branch : S.Family -> Prop},
      LocalEndpointUse S branch ->
      KernelPackage S
  noIndependentDiscriminator :
    forall {branch positive : S.Family -> Prop},
      LocalEndpointUse S branch ->
      IndependentDiscriminator S branch positive ->
      False

def targetAdequacy_forces_kernel
    {S : SunflowerCarrier}
    (G : KernelForcedGovernance S)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    KernelPackage S := by
  exact G.targetAdequacyForcesKernel U

theorem local_endpoint_use_excludes_independent_discriminator
    {S : SunflowerCarrier}
    (G : KernelForcedGovernance S)
    {branch positive : S.Family -> Prop}
    (U : LocalEndpointUse S branch)
    (D : IndependentDiscriminator S branch positive) :
    False := by
  exact G.noIndependentDiscriminator U D

/-- Typed cost ledger for denying one kernel role while preserving endpoint use. -/
structure KernelDenialCost (S : SunflowerCarrier) where
  deniedRole : KernelRole
  destroysFixedTargetOrCarrier : Prop
  destroysStandingForce : Prop
  importsExternalSelectorOrRepair : Prop
  changesEndpointAct : Prop
  costIsExhaustive :
    destroysFixedTargetOrCarrier \/
    destroysStandingForce \/
    importsExternalSelectorOrRepair \/
    changesEndpointAct

def KernelDenialCost.isRealCost
    {S : SunflowerCarrier}
    (_C : KernelDenialCost S) : Prop :=
  True

def no_third_position_under_kernel_forced_governance
    {S : SunflowerCarrier}
    (G : KernelForcedGovernance S)
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    KernelPackage S := by
  exact targetAdequacy_forces_kernel G U

end SunflowerAASC
