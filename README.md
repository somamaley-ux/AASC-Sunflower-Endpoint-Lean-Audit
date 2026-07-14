# Three-Petal Sunflower Endpoint: Combinatorics and Structural Closure

[![Lean audit](https://github.com/somamaley-ux/AASC-Sunflower-Endpoint-Lean-Audit/actions/workflows/lean.yml/badge.svg)](https://github.com/somamaley-ux/AASC-Sunflower-Endpoint-Lean-Audit/actions/workflows/lean.yml)

This repository contains the clean Lean proof spine accompanying **Two-Track
Closure for the Three-Petal Sunflower Endpoint**. It is first a finite
combinatorics project. The combinatorial track builds the carrier, reductions,
counting bounds, inheritance machinery, and final three-petal sunflower. At
one residual high-rank obstruction, the proof hands off to AASC structural
closure, then returns to the combinatorial endpoint.

## Proof at a Glance

1. **Combinatorial generation and reduction.** Core/link/matching analysis,
   blocker carriers, private witnesses, rank deletion, finite tensor profiles,
   and low-to-high-rank inheritance reduce a dense countercase to an oversized
   canonical support fibre.
2. **AASC structural closeout.** AASC supplies no competing construction and
   no numerical input. It excludes the residual fibre by fixed-domain role
   exhaustion and impossibility. This handoff is available because the
   Admissibility, Standing, Reference, and Irreversibility conditions identified
   by the kernel are necessity conditions of non-degenerate determinacy itself.
3. **Return to combinatorics.** The resulting fibre bound constructs the
   rank-uniform source, produces an actual three-petal sunflower, and proves
   `|F| <= 8384512^n`.

The handoff is therefore not from combinatorics to an optional interpretation.
It is from generative finite combinatorics to a structural closure theorem
whose applicability is already forced by the determinate identity,
comparison, deletion, inheritance, and endpoint used in the combinatorial
argument.

## Result and Scope

> The manuscript's two-track proof establishes the three-petal endpoint for
> every non-degenerate determinate finite uniform-family regime. The
> combinatorial track performs the constructive and quantitative work. The
> AASC track closes the one surviving structural case through exhaustion and
> impossibility, under necessity conditions inherent in determinate
> finite-family reasoning rather than an elective predicate imposed on a
> subclass of families.

Lean machine-checks the manuscript-matched transfer from the finite
profile/role/slot population theorem to a genuine three-petal sunflower and
the endpoint `|F| <= 8384512^n`.

## Combinatorial Track

The checked development formalizes the following combinatorial spine:

- concrete finite uniform families, cores, links, matching petals, and raw
  blocker bounds;
- private-witness reduction and deletion-compatible rank projection;
- the traditional seed cutoff `2047`;
- the finite tensor-profile reservoir `4094`;
- the refined constraint base `8384512` and controlled range `8384511`;
- fixed-identity and high-rank population inheritance;
- the population-or-oversized-support-fibre dichotomy;
- conversion of the closed fibre bound into a rank-uniform source; and
- construction of `Concrete.HasSunflower 3 F` and the final endpoint bound.

These are not retrospective labels placed on an AASC proof. They are the
generative content that supplies the objects and quantitative structure on
which the final structural exclusion operates.

## Structural Handoff

The separately mechanized kernel dependency is pinned from
[`non-degenerate-construction-kernel-admissibility`](https://github.com/somamaley-ux/non-degenerate-construction-kernel-admissibility)
at commit `8b51f035f86f781e5eeb18cbaef8b46e74ed4924`.

`V2.MechanizedKernelImport` translates the concrete endpoint use into that
repository's `ConstructionRegime` and constructs its kernel package,
fixed-domain closure packet, fixed-domain uniqueness, no-derivation-below
result, no-faithful-lower-generator result, and global synthesis certificate.
The imported kernel theorems and this bridge are axiom-free.

This mechanization identifies why the structural handoff is licensed. Denying
the kernel does not leave the same determinate combinatorial problem intact;
it removes or changes the identity, comparison, transformation, reference, or
endpoint conditions required to state and preserve that problem.

## Lean Closure Spine

The public entrypoint imports one terminal module:

```lean
import SunflowerAASC.V2.ManuscriptKernelTransfer
```

The terminal dependency chain is:

1. the concrete combinatorial modules establish the finite carrier,
   blocker, seed, projection, and inheritance infrastructure;
2. `population_or_oversizedCanonicalSupportFiber` isolates the residual
   support-fibre obstruction;
3. `MechanizedKernelImport.endpointConstructionRegime` maps the already fixed
   endpoint to the separately mechanized kernel regime;
4. `mechanizedKernelDependencyCertificate` imports kernel necessity,
   fixed-domain closure and uniqueness, and no derivation below the kernel;
5. `KernelImportRoute.activation` and
   `KernelImportRoute.denialAndStrictWeakeningExhausted` activate and exhaust
   the structural alternatives;
6. `ImportedManuscriptKernelGovernedPopulationTheorem` internalizes the
   manuscript's finite profile/role/slot population conclusion;
7. `fixedIdentityPopulation` and `canonicalSupportFiberBound` preserve the
   inherited combinatorial identity and close the residual fibre;
8. `toKernelGovernedFiberClosureSource` constructs the rank-uniform source;
9. `sunflower_of_importedManuscriptKernelGovernedClosure` produces an actual
   `Concrete.HasSunflower 3 F`; and
10. `provesEndpointBound` proves the complete base-`8384512` endpoint.

The publish tree contains 28 dependency modules in the transitive closure of
the terminal theorem, including 23 V2 modules, plus the one-module public root.
Exploratory branches that do not feed the terminal theorem are excluded.

## Formalization Boundary

The target-specific corpus theorem is represented by the explicit structure
`ImportedManuscriptKernelGovernedPopulationTheorem`; it is not hidden in a
Lean `axiom`. The theorem
`nonempty_importedManuscriptPopulationTheorem_iff_endpointBound` verifies that
this proof object has exactly endpoint strength.

The release does not claim that Lean independently reconstructs manuscript
Theorem 6.2 from Mathlib, or that conventional combinatorics already contains
an AASC-free analogue of its fixed-domain exhaustion. The first is the stated
formalization boundary; the second is precisely why the two-track handoff is
needed. Neither makes kernel governance an optional condition on the
mathematical theorem's determinate domain.

## Main Anchors

- `V2.PopulationInheritance.threePetalTraditionalSeedConstraintBase_eq`
- `V2.HighRankPopulationInheritance.population_or_oversizedCanonicalSupportFiber`
- `V2.FixedIdentityPopulation.KernelFaithfulFixedIdentityRealization.identity_preserved_at_rank`
- `V2.MechanizedKernelImport.mechanizedKernelDependencyCertificate`
- `V2.ManuscriptKernelTransfer.KernelImportRoute.noSameDomainDerivationBelowKernel`
- `V2.ManuscriptKernelTransfer.sunflower_of_importedManuscriptKernelGovernedClosure`
- `V2.ManuscriptKernelTransfer.ImportedManuscriptKernelGovernedPopulationTheorem.provesEndpointBound`
- `V2.ManuscriptKernelTransfer.nonempty_importedManuscriptPopulationTheorem_iff_endpointBound`

## Validation

The release uses Lean `v4.28.0` and Mathlib `v4.28.0`.

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check-sunflower-a-plus-audit.ps1
```

The audit:

- scans `SunflowerAASC/` and `Checks/Axiom/` for live `axiom`, `unsafe`,
  `sorry`, or `admit` declarations;
- builds the terminal `SunflowerAASC` target; and
- runs 25 focused `#print axioms` checks on the combinatorial, imported-kernel,
  and load-bearing transfer anchors.

The reported dependencies are standard Lean/Mathlib principles such as
`propext`, `Classical.choice`, and `Quot.sound`, not project-specific axioms.

## Manuscript

The synchronized manuscript snapshot is under [`papers/sunflower`](papers/sunflower):

- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint.pdf`
- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint_Source.zip`

The manuscript and Lean release use the same two-track boundary: combinatorics
generates and reduces, AASC excludes the final structurally inadmissible
alternative, and the checked transfer returns the result to a genuine
sunflower and the numerical endpoint.
