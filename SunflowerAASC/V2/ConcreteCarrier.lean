import Mathlib.Data.Finset.Card
import SunflowerAASC.Transfer

namespace SunflowerAASC
namespace V2
namespace Concrete

/-- The four admissible standing-factor outcomes on a fixed AASC domain. -/
inductive FixedDomainStandingFactor where
  | bookkeeping
  | gateEquivalent
  | sameSideRefinement
  | scopeChange
deriving DecidableEq, Repr

/-- A finite `n`-uniform family of finite subsets of `alpha`. -/
structure UniformSetFamily (alpha : Type) [DecidableEq alpha] (n : Nat) where
  edges : Finset (Finset alpha)
  uniform : forall edge : Finset alpha, edge ∈ edges -> edge.card = n

/-- A concrete core-petal witness with `k` distinct members of the family. -/
structure CorePetalSunflowerWitness
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (k : Nat)
    (F : UniformSetFamily alpha n)
    (core : Finset alpha) where
  petals : Fin k -> Finset alpha
  petals_mem : forall i : Fin k, petals i ∈ F.edges
  petals_injective : Function.Injective petals
  pairwise_intersection :
    forall i j : Fin k, Not (i = j) -> petals i ∩ petals j = core

def HasSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (k : Nat)
    (F : UniformSetFamily alpha n) : Prop :=
  Exists (fun core : Finset alpha =>
    Nonempty (CorePetalSunflowerWitness k F core))

/--
Mathlib-backed carrier for finite uniform set families.  The positive endpoint
is definitionally the core-petal witness, so the abstract carrier equivalence
is no longer a supplied mathematical assumption at this layer.
-/
def concreteSunflowerCarrier
    (alpha : Type)
    [DecidableEq alpha]
    (n k : Nat) : SunflowerCarrier where
  Family := UniformSetFamily alpha n
  Core := Finset alpha
  Petal := Finset alpha
  NegativeMotif := UniformSetFamily alpha n
  StandingFactor := FixedDomainStandingFactor
  k := k
  rank := n
  nondegenerate := 0 < n /\ 3 <= k
  familySize := fun F => F.edges.card
  ceilingBound := fun H r => H ^ r
  sunflower := HasSunflower k
  residualWitness := fun F core =>
    Nonempty (CorePetalSunflowerWitness k F core)
  standingFactorBranch := fun factor F =>
    match factor with
    | .bookkeeping => False
    | .gateEquivalent => HasSunflower k F
    | .sameSideRefinement => Not (HasSunflower k F)
    | .scopeChange => False
  lawfulNegativeMotif := fun F => Not (HasSunflower k F)
  motifDensityExceeds := fun H F => H ^ n < F.edges.card
  motifExcludedByCarrierCriterion := fun _ => False
  corePetalEquivalence := by
    intro F
    rfl

theorem concrete_familySize_eq
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (F : UniformSetFamily alpha n) :
    (concreteSunflowerCarrier alpha n k).familySize F = F.edges.card := by
  rfl

theorem concrete_ceilingBound_eq
    {alpha : Type}
    [DecidableEq alpha]
    {n k H r : Nat} :
    (concreteSunflowerCarrier alpha n k).ceilingBound H r = H ^ r := by
  rfl

theorem concrete_noSunflower_iff
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    (F : UniformSetFamily alpha n) :
    (concreteSunflowerCarrier alpha n k).noSunflower F <->
      Not (HasSunflower k F) := by
  rfl

theorem quantitativeCountercase_cardinality_excess
    {alpha : Type}
    [DecidableEq alpha]
    {n k H : Nat}
    {F : UniformSetFamily alpha n}
    (E : QuantitativeExactCountercaseUse
      (concreteSunflowerCarrier alpha n k) H F) :
    H ^ n < F.edges.card := by
  exact E.sizeExcess_holds

end Concrete
end V2
end SunflowerAASC
