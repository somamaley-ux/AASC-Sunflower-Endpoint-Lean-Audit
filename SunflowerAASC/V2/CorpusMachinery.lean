import SunflowerAASC.V2.ConcreteCarrier

namespace SunflowerAASC
namespace V2
namespace CorpusMachinery

/-- The five possible loci for an attempted fixed-base strengthening. -/
inductive FixedBaseStrengtheningLocus where
  | oldGraphAlteration
  | carrierChange
  | auxiliaryData
  | conservativeDefinition
  | admissibilityPolicyChange
deriving DecidableEq, Repr

/-- A strengthening attempt records both its locus and any auxiliary factor. -/
structure FixedBaseStrengtheningAttempt where
  locus : FixedBaseStrengtheningLocus
  auxiliaryFactor : Concrete.FixedDomainStandingFactor
deriving DecidableEq, Repr

/--
The fixed-base exhaustion map.  Altering the graph or carrier changes scope;
auxiliary data receives its actual fixed-domain classification; a conservative
definition is bookkeeping; and a policy change is gate-equivalent.
-/
def strengtheningDisposition
    (attempt : FixedBaseStrengtheningAttempt) : SameScopeFactorDisposition :=
  match attempt.locus with
  | .oldGraphAlteration => .scopeChange
  | .carrierChange => .scopeChange
  | .auxiliaryData =>
      match attempt.auxiliaryFactor with
      | .bookkeeping => .bookkeeping
      | .gateEquivalent => .gateEquivalent
      | .sameSideRefinement => .sameSideRefinement
      | .scopeChange => .scopeChange
  | .conservativeDefinition => .bookkeeping
  | .admissibilityPolicyChange => .gateEquivalent

theorem strengtheningDisposition_ne_independentAuthorizer
    (attempt : FixedBaseStrengtheningAttempt) :
    Not (strengtheningDisposition attempt =
      SameScopeFactorDisposition.independentAuthorizer) := by
  cases attempt with
  | mk locus auxiliaryFactor =>
      cases locus <;> simp [strengtheningDisposition]
      cases auxiliaryFactor <;> simp

/-- The concrete factor ledger is the auxiliary-data branch of exhaustion. -/
def standingFactorDisposition
    (factor : Concrete.FixedDomainStandingFactor) :
    SameScopeFactorDisposition :=
  strengtheningDisposition
    { locus := .auxiliaryData, auxiliaryFactor := factor }

theorem standingFactorDisposition_ne_independentAuthorizer
    (factor : Concrete.FixedDomainStandingFactor) :
    Not (standingFactorDisposition factor =
      SameScopeFactorDisposition.independentAuthorizer) := by
  exact strengtheningDisposition_ne_independentAuthorizer
    { locus := .auxiliaryData, auxiliaryFactor := factor }

/--
Kernel necessity instantiated from the fields of a determinate local endpoint
use.  The roles are identified with their endpoint work rather than filled by
unrelated propositions.
-/
def kernelNecessityOfNondegenerate
    (S : SunflowerCarrier)
    (nondegenerate : S.nondegenerate) : KernelNecessitySource S where
  carrierNondegenerate := nondegenerate
  kernelAtEndpointUse := by
    intro branch U
    exact
      { admissibility := U.branchRoleFixed
        standing := U.reportable /\ U.downstreamReusable
        reference := U.targetFixed /\ U.carrierFixed
        irreversibility := U.lawfulActTimeBoundary
        admissibility_holds := U.branchRoleFixed_holds
        standing_holds := And.intro U.reportable_holds U.downstreamReusable_holds
        reference_holds := And.intro U.targetFixed_holds U.carrierFixed_holds
        irreversibility_holds := U.lawfulActTimeBoundary_holds }

/-- Fixed-domain A+ closure for the concrete standing-factor ledger. -/
def concreteFixedDomainClosure
    (alpha : Type)
    [DecidableEq alpha]
    (n k : Nat) :
    FixedDomainAPlusClosureSource
      (Concrete.concreteSunflowerCarrier alpha n k) where
  disposition := standingFactorDisposition
  noIndependentAuthorizer :=
    standingFactorDisposition_ne_independentAuthorizer

/-- The first two corpus blocks are now constructed for the finite-set carrier. -/
def concreteKernelFirstCorpusMachinery
    (alpha : Type)
    [DecidableEq alpha]
    (n k : Nat)
    (nondegenerate : 0 < n /\ 3 <= k) :
    KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha n k) where
  kernelNecessity :=
    kernelNecessityOfNondegenerate
      (Concrete.concreteSunflowerCarrier alpha n k)
      nondegenerate
  fixedDomainClosure := concreteFixedDomainClosure alpha n k

/-- The concrete negative endpoint used by the kernel-first exhaustion proof. -/
def concreteNoSunflowerEndpointUse
    (alpha : Type)
    [DecidableEq alpha]
    (n k : Nat)
    (nondegenerate : 0 < n /\ 3 <= k) :
    LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha n k)
      (fun F => Not (Concrete.HasSunflower k F)) where
  targetFixed := forall F,
    (Concrete.concreteSunflowerCarrier alpha n k).negativeEndpoint F <->
      Not (Concrete.HasSunflower k F)
  carrierFixed :=
    (Concrete.concreteSunflowerCarrier alpha n k).rank = n /\
      (Concrete.concreteSunflowerCarrier alpha n k).k = k
  branchRoleFixed := forall F,
    Not (Concrete.HasSunflower k F) <->
      (Concrete.concreteSunflowerCarrier alpha n k).noSunflower F
  reportable := forall F,
    (Concrete.concreteSunflowerCarrier alpha n k).familySize F = F.edges.card
  downstreamReusable := forall F,
    (Concrete.concreteSunflowerCarrier alpha n k).sunflower F <->
      (Concrete.concreteSunflowerCarrier alpha n k).corePetalEndpoint F
  lawfulActTimeBoundary :=
    (Concrete.concreteSunflowerCarrier alpha n k).nondegenerate
  targetFixed_holds := by
    intro F
    rfl
  carrierFixed_holds := ⟨rfl, rfl⟩
  branchRoleFixed_holds := by
    intro F
    rfl
  reportable_holds := by
    intro F
    rfl
  downstreamReusable_holds := by
    intro F
    exact (Concrete.concreteSunflowerCarrier alpha n k).corePetalEquivalence F
  lawfulActTimeBoundary_holds := nondegenerate

def concreteKernelLicensedSameness
    (alpha : Type)
    [DecidableEq alpha]
    (n k : Nat)
    (nondegenerate : 0 < n /\ 3 <= k) :
    KernelLicensedSameness
      (Concrete.concreteSunflowerCarrier alpha n k) :=
  (concreteKernelFirstCorpusMachinery alpha n k nondegenerate).samenessAtEndpointUse
    (concreteNoSunflowerEndpointUse alpha n k nondegenerate)

theorem concreteSamenessMeaningful
    (alpha : Type)
    [DecidableEq alpha]
    (n k : Nat)
    (nondegenerate : 0 < n /\ 3 <= k) :
    (concreteKernelLicensedSameness alpha n k nondegenerate).sameness := by
  exact (concreteKernelLicensedSameness alpha n k nondegenerate).sameness_holds

theorem concreteKernelRolesHold
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (nondegenerate : 0 < n /\ 3 <= k)
    {branch : Concrete.UniformSetFamily alpha n -> Prop}
    (U : LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha n k) branch) :
    (KernelFirstCorpusMachinery.kernelAtEndpointUse
      (concreteKernelFirstCorpusMachinery alpha n k nondegenerate)
      U).allRolesHold := by
  exact
    KernelFirstCorpusMachinery.kernelRolesHoldAtEndpointUse
      (concreteKernelFirstCorpusMachinery alpha n k nondegenerate)
      U

end CorpusMachinery
end V2
end SunflowerAASC
