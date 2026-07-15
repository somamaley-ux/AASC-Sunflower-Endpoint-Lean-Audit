import SunflowerAASC.V2.PrivateWitnessReduction

namespace SunflowerAASC
namespace V2
namespace GeneratedIncidenceTower

/--
A generated one-rank continuation from a private blocker coordinate.  The next
coordinate is not identified with the current residual: it is a point of the
next minimal blocker that lies in that residual.
-/
def NextCoordinate
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) : Type :=
  {target : {x // x ∈ MinimalBlocker.minimalBlocker
      (PrivateWitnessReduction.residualFamily F)} //
    target.val ∈ PrivateWitnessReduction.residual F source}

/--
The blocker-incidence continuation is always populated.  This is the positive
combinatorial generation step: the next blocker hits every current residual.
-/
theorem nextCoordinate_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    Nonempty (NextCoordinate F source) := by
  have residual_mem :
      PrivateWitnessReduction.residual F source ∈
        (PrivateWitnessReduction.residualFamily F).edges :=
    PrivateWitnessReduction.mem_residualFamily_iff.mpr ⟨source, rfl⟩
  rcases Finset.not_disjoint_iff.mp
      (MinimalBlocker.minimalBlocker_hitsEveryEdge
        (PrivateWitnessReduction.residualFamily F)
        (PrivateWitnessReduction.residual F source)
        residual_mem) with ⟨target, target_mem_residual, target_mem_blocker⟩
  exact ⟨⟨⟨target, target_mem_blocker⟩, target_mem_residual⟩⟩

/-- The finite relation corresponding to the generated next-coordinate type. -/
def NextRel
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (target : {x // x ∈ MinimalBlocker.minimalBlocker
      (PrivateWitnessReduction.residualFamily F)}) : Prop :=
  target.val ∈ PrivateWitnessReduction.residual F source

theorem exists_nextRel
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    ∃ target, NextRel F source target := by
  rcases nextCoordinate_nonempty F source with ⟨target⟩
  exact ⟨target.val, target.property⟩

/--
The family obtained after exactly `steps` private-residual operations, stopping
at rank `baseRank + 1`.
-/
noncomputable def terminalFamily
    {alpha : Type}
    [DecidableEq alpha]
    (baseRank : Nat) :
    (steps : Nat) →
      Concrete.UniformSetFamily alpha (baseRank + steps + 1) →
      Concrete.UniformSetFamily alpha (baseRank + 1)
  | 0, F => F
  | steps + 1, F =>
      terminalFamily baseRank steps
        (PrivateWitnessReduction.residualFamily F)

/--
All generated blocker-incidence continuations of one initial private witness.
Branching is retained as data; no matching or selector is assumed.
-/
inductive IncidencePath
    {alpha : Type}
    [DecidableEq alpha]
    (baseRank : Nat) :
    (steps : Nat) →
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)) →
    {x // x ∈ MinimalBlocker.minimalBlocker F} → Type
  | stop
      (F : Concrete.UniformSetFamily alpha (baseRank + 1))
      (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
      IncidencePath baseRank 0 F source
  | next
      {steps : Nat}
      (F : Concrete.UniformSetFamily alpha (baseRank + (steps + 1) + 1))
      (source : {x // x ∈ MinimalBlocker.minimalBlocker F})
      (target : {x // x ∈ MinimalBlocker.minimalBlocker
        (PrivateWitnessReduction.residualFamily F)})
      (incident : NextRel F source target)
      (tail : IncidencePath baseRank steps
        (PrivateWitnessReduction.residualFamily F) target) :
      IncidencePath baseRank (steps + 1) F source

/-- Every initial blocker coordinate has a generated path to the cutoff rank. -/
theorem incidencePath_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    (baseRank : Nat)
    (steps : Nat)
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    Nonempty (IncidencePath baseRank steps F source) := by
  induction steps with
  | zero =>
      exact ⟨IncidencePath.stop F source⟩
  | succ steps ih =>
      rcases exists_nextRel F source with ⟨target, incident⟩
      rcases ih (PrivateWitnessReduction.residualFamily F) target with ⟨tail⟩
      exact ⟨IncidencePath.next F source target incident tail⟩

/-- The literal final minimal-blocker coordinate carried by a generated path. -/
noncomputable def IncidencePath.terminalCoordinate
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    {source : {x // x ∈ MinimalBlocker.minimalBlocker F}}
    (path : IncidencePath baseRank steps F source) :
      {x // x ∈ MinimalBlocker.minimalBlocker
        (terminalFamily baseRank steps F)} := by
  induction path with
  | stop F source =>
      exact source
  | next F source target incident tail ih =>
      exact ih

/-- A generated terminal path together with the initial coordinate it continues. -/
def TerminalPath
    {alpha : Type}
    [DecidableEq alpha]
    (baseRank steps : Nat)
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)) : Type :=
  Σ source : {x // x ∈ MinimalBlocker.minimalBlocker F},
    IncidencePath baseRank steps F source

def TerminalPath.source
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    (path : TerminalPath baseRank steps F) :
    {x // x ∈ MinimalBlocker.minimalBlocker F} :=
  path.1

noncomputable def TerminalPath.carrierOf
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    (path : TerminalPath baseRank steps F) :
    {x // x ∈ MinimalBlocker.minimalBlocker
      (terminalFamily baseRank steps F)} :=
  path.2.terminalCoordinate

/-- A source reaches a terminal blocker carrier through generated incidence. -/
def ReachesTerminalCarrier
    {alpha : Type}
    [DecidableEq alpha]
    {baseRank steps : Nat}
    {F : Concrete.UniformSetFamily alpha (baseRank + steps + 1)}
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (carrier : {x // x ∈ MinimalBlocker.minimalBlocker
      (terminalFamily baseRank steps F)}) : Prop :=
  ∃ path : IncidencePath baseRank steps F source,
    path.terminalCoordinate = carrier

/-- Every source reaches at least one literal terminal blocker carrier. -/
theorem exists_reachesTerminalCarrier
    {alpha : Type}
    [DecidableEq alpha]
    (baseRank steps : Nat)
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    ∃ carrier, ReachesTerminalCarrier source carrier := by
  rcases incidencePath_nonempty baseRank steps F source with ⟨path⟩
  exact ⟨path.terminalCoordinate, path, rfl⟩

/-- Private residualization preserves the no-sunflower countercase to cutoff. -/
theorem terminalFamily_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {k : Nat}
    (baseRank steps : Nat)
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) :
    Not (Concrete.HasSunflower k (terminalFamily baseRank steps F)) := by
  induction steps with
  | zero =>
      exact noSunflower
  | succ steps ih =>
      exact ih (PrivateWitnessReduction.residualFamily F)
        (PrivateWitnessReduction.residualFamily_noSunflower
          (F := F) noSunflower)

/-- Every initial coordinate occurs as the source of a generated terminal path. -/
theorem exists_terminalPath_source
    {alpha : Type}
    [DecidableEq alpha]
    (baseRank steps : Nat)
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    ∃ path : TerminalPath baseRank steps F, path.source = source := by
  rcases incidencePath_nonempty baseRank steps F source with ⟨path⟩
  exact ⟨⟨source, path⟩, rfl⟩

/--
A downstream representative of the already inhabited path relation.  The
relation and its totality are prior; this choice is not part of endpoint
governance and carries no standing authority.
-/
noncomputable def generatedTerminalPath
    {alpha : Type}
    [DecidableEq alpha]
    (baseRank steps : Nat)
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    TerminalPath baseRank steps F :=
  ⟨source, Classical.choice
    (incidencePath_nonempty baseRank steps F source)⟩

@[simp] theorem generatedTerminalPath_source
    {alpha : Type}
    [DecidableEq alpha]
    (baseRank steps : Nat)
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    (generatedTerminalPath baseRank steps F source).source = source :=
  rfl

/-- The literal terminal carrier selected from the generated nonempty relation. -/
noncomputable def generatedCarrier
    {alpha : Type}
    [DecidableEq alpha]
    (baseRank steps : Nat)
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    {x // x ∈ MinimalBlocker.minimalBlocker
      (terminalFamily baseRank steps F)} :=
  (generatedTerminalPath baseRank steps F source).carrierOf

theorem generatedCarrier_reachable
    {alpha : Type}
    [DecidableEq alpha]
    (baseRank steps : Nat)
    (F : Concrete.UniformSetFamily alpha (baseRank + steps + 1))
    (source : {x // x ∈ MinimalBlocker.minimalBlocker F}) :
    ReachesTerminalCarrier source
      (generatedCarrier baseRank steps F source) := by
  exact ⟨(generatedTerminalPath baseRank steps F source).2, rfl⟩

end GeneratedIncidenceTower
end V2
end SunflowerAASC
