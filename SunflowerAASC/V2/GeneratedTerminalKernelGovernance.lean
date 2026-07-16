import SunflowerAASC.V2.FixedCellRoleLocusExclusion

namespace SunflowerAASC
namespace V2
namespace GeneratedTerminalKernelGovernance

open GeneratedIncidenceTower
open GeneratedSeedCapacity
open FixedCellStandingClosure

/--
A literal generated terminal incidence, retaining its source identity, terminal
locus, and combinatorial generation proof.
-/
structure GeneratedTerminalIncidence
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F)) where
  source : CellSource cell
  locus : TerminalCarrier F
  generated : ReachesTerminalCarrier source.coordinate locus

/-- Combinatorics populates a generated terminal incidence for every source. -/
theorem generatedTerminalIncidence_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (cell : Finset (InitialCarrier F))
    (source : CellSource cell) :
    Nonempty {incidence : GeneratedTerminalIncidence F cell //
      incidence.source = source} := by
  rcases exists_reachesTerminalCarrier baseRank steps F source.coordinate with
    ⟨locus, generated⟩
  exact ⟨⟨⟨source, locus, generated⟩, rfl⟩⟩

/-- The determinate identity of an incidence is its source/locus pair. -/
def GeneratedTerminalIncidence.identity
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (incidence : GeneratedTerminalIncidence F cell) :
    CellSource cell × TerminalCarrier F :=
  (incidence.source, incidence.locus)

/-- Generated terminal incidences have faithful typed identity. -/
theorem generatedTerminalIncidence_identity_injective
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)} :
    Function.Injective
      (@GeneratedTerminalIncidence.identity alpha _ baseRank steps F cell) := by
  intro left right sameIdentity
  cases left with
  | mk leftSource leftLocus leftGenerated =>
      cases right with
      | mk rightSource rightLocus rightGenerated =>
          have sameSource : leftSource = rightSource :=
            congrArg Prod.fst sameIdentity
          have sameLocus : leftLocus = rightLocus :=
            congrArg Prod.snd sameIdentity
          subst rightSource
          subst rightLocus
          rfl

/--
Concrete nondegeneracy of a generated incidence: its source is indispensable
in the minimal blocker and its source-to-locus continuation is realized.
-/
def GeneratedTerminalIncidence.PrivateWitnessNondegenerate
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (incidence : GeneratedTerminalIncidence F cell) : Prop :=
  incidence.source.coordinate.val ∈
      MinimalBlocker.privateEdge F incidence.source.coordinate ∧
    ReachesTerminalCarrier incidence.source.coordinate incidence.locus

theorem GeneratedTerminalIncidence.privateWitnessNondegenerate_holds
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (incidence : GeneratedTerminalIncidence F cell) :
    incidence.PrivateWitnessNondegenerate := by
  exact ⟨MinimalBlocker.privateEdge_contains F incidence.source.coordinate,
    incidence.generated⟩

/-- Every terminal three-petal carrier is nondegenerate, at every base rank. -/
theorem terminalThreePetalCarrier_nondegenerate
    (alpha : Type)
    [DecidableEq alpha]
    (baseRank : Nat) :
    (Concrete.concreteSunflowerCarrier alpha (baseRank + 1) 3).nondegenerate := by
  exact ⟨by omega, by decide⟩

/-- Kernel-first corpus machinery forced at the literal terminal rank. -/
def terminalKernelFirstCorpusMachinery
    (alpha : Type)
    [DecidableEq alpha]
    (baseRank : Nat) :
    KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (baseRank + 1) 3) :=
  CorpusMachinery.concreteKernelFirstCorpusMachinery alpha (baseRank + 1) 3
    (terminalThreePetalCarrier_nondegenerate alpha baseRank)

/-- The fixed no-sunflower endpoint use at the literal terminal rank. -/
def terminalNoSunflowerEndpointUse
    (alpha : Type)
    [DecidableEq alpha]
    (baseRank : Nat) :
    LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha (baseRank + 1) 3)
      (fun family => Not (Concrete.HasSunflower 3 family)) :=
  CorpusMachinery.concreteNoSunflowerEndpointUse alpha (baseRank + 1) 3
    (terminalThreePetalCarrier_nondegenerate alpha baseRank)

/-- The generated terminal family remains inside the governed negative branch. -/
theorem terminalFamily_at_noSunflowerEndpoint
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (noSunflower : Not (Concrete.HasSunflower 3 F)) :
    Not (Concrete.HasSunflower 3 (terminalFamily baseRank steps F)) :=
  terminalFamily_noSunflower baseRank steps F noSunflower

/--
Kernel governance of the terminal endpoint is forced by nondegeneracy and
determinate endpoint use; it is not an optional predicate on the family.
-/
theorem terminalEndpoint_kernelRolesHold
    (alpha : Type)
    [DecidableEq alpha]
    (baseRank : Nat) :
    ((terminalKernelFirstCorpusMachinery alpha baseRank).kernelAtEndpointUse
      (terminalNoSunflowerEndpointUse alpha baseRank)).allRolesHold := by
  exact
    (terminalKernelFirstCorpusMachinery alpha baseRank).kernelRolesHoldAtEndpointUse
      (terminalNoSunflowerEndpointUse alpha baseRank)

/-- Every generated terminal incidence lies at that necessarily governed endpoint. -/
theorem GeneratedTerminalIncidence.kernelRolesHold
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {cell : Finset (InitialCarrier F)}
    (_incidence : GeneratedTerminalIncidence F cell) :
    ((terminalKernelFirstCorpusMachinery alpha baseRank).kernelAtEndpointUse
      (terminalNoSunflowerEndpointUse alpha baseRank)).allRolesHold :=
  terminalEndpoint_kernelRolesHold alpha baseRank

end GeneratedTerminalKernelGovernance
end V2
end SunflowerAASC
