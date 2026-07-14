# AASC Sunflower Endpoint Lean Audit

[![Lean audit](https://github.com/somamaley-ux/AASC-Sunflower-Endpoint-Lean-Audit/actions/workflows/lean.yml/badge.svg)](https://github.com/somamaley-ux/AASC-Sunflower-Endpoint-Lean-Audit/actions/workflows/lean.yml)

This repository contains the clean Lean proof spine accompanying **Two-Track
Closure for the Three-Petal Sunflower Endpoint**.

## Strongest Truthful Claim

> The manuscript proves the three-petal endpoint for every non-degenerate
> determinate finite uniform-family regime. AASC is not an optional predicate
> imposed on a subclass of families: it names the Admissibility, Standing,
> Reference, and Irreversibility conditions already required for the family,
> identity, comparison, deletion, inheritance, and endpoint to be determinate.
> Lean machine-checks the manuscript-matched closure from the finite
> profile/role/slot population theorem to a genuine three-petal sunflower and
> the endpoint `|F| <= 8384512^n`.

The kernel dependency is executable. This project pins
[`non-degenerate-construction-kernel-admissibility`](https://github.com/somamaley-ux/non-degenerate-construction-kernel-admissibility)
at commit `8b51f035f86f781e5eeb18cbaef8b46e74ed4924`.
`V2.MechanizedKernelImport` translates the concrete endpoint use into that
repository's `ConstructionRegime` and constructs its kernel package,
fixed-domain closure packet, fixed-domain uniqueness, no-derivation-below
result, no-faithful-lower-generator result, and global synthesis certificate.
The imported kernel theorems and this bridge are axiom-free.

There is no additional Lean-only support-fibre premise after the manuscript
import. The external corpus theorem is represented by the explicit structure
`ImportedManuscriptKernelGovernedPopulationTheorem`; it is not hidden in a
Lean `axiom`. The theorem
`nonempty_importedManuscriptPopulationTheorem_iff_endpointBound` proves that
this imported statement has exactly endpoint strength.

The release does **not** claim that Lean independently reconstructs the corpus
proof of manuscript Theorem 6.2, or that conventional combinatorics already
contains an AASC-free analogue of its fixed-domain exhaustion. Those are
formalization and translation boundaries, not an optional condition on the
mathematical theorem's determinate domain.

## Closure Spine

The public entrypoint imports one terminal module:

```lean
import SunflowerAASC.V2.ManuscriptKernelTransfer
```

The checked dependency chain is:

1. `NeutralEndpointAdequacy` is equivalent to the existing live endpoint-use
   adequacy surface.
2. `MechanizedKernelImport.endpointConstructionRegime` maps that endpoint to
   the separately mechanized kernel repository's fixed-domain regime.
3. `mechanizedKernelDependencyCertificate` imports kernel necessity,
   fixed-domain closure and uniqueness, and no derivation below the kernel.
4. `KernelImportRoute.activation` instantiates Admissibility, Standing,
   Reference, and Irreversibility before downstream classification.
5. `KernelImportRoute.denialAndStrictWeakeningExhausted` assigns the explicit
   cost of denying or weakening that governance.
6. `ImportedManuscriptKernelGovernedPopulationTheorem` states exactly the
   manuscript's finite profile/role/slot population theorem under its generated
   high-rank context.
7. `ThreePetalLocalManuscriptPopulation.fixedIdentityPopulation` preserves
   inherited identity through the populated role ledger.
8. `ThreePetalLocalManuscriptPopulation.canonicalSupportFiberBound` converts
   that population into the required finite support-fibre bound.
9. `toKernelGovernedFiberClosureSource` constructs the rank-uniform high-rank
   source; no second source is assumed.
10. `sunflower_of_importedManuscriptKernelGovernedClosure` produces an actual
   `Concrete.HasSunflower 3 F`.
11. `ImportedManuscriptKernelGovernedPopulationTheorem.provesEndpointBound`
   proves the complete base-`8384512` endpoint.

The numerical base is checked inside Lean:

```text
traditional cutoff             = 2047
finite tensor-profile reservoir = 4094
refined constraint base         = 8384512
reflected controlled range      = 8384511
```

The publish tree contains 28 dependency modules in the transitive closure of
the terminal theorem, including 23 V2 modules, plus the one-module public root.
Exploratory branches that do not feed the terminal theorem are intentionally
excluded from this release.

## Main Anchors

- `V2.ManuscriptKernelTransfer.sunflower_of_importedManuscriptKernelGovernedClosure`
- `V2.ManuscriptKernelTransfer.ImportedManuscriptKernelGovernedPopulationTheorem.provesEndpointBound`
- `V2.ManuscriptKernelTransfer.nonempty_importedManuscriptPopulationTheorem_iff_endpointBound`
- `V2.MechanizedKernelImport.mechanizedKernelDependencyCertificate`
- `V2.ManuscriptKernelTransfer.KernelImportRoute.noSameDomainDerivationBelowKernel`
- `V2.PopulationInheritance.threePetalTraditionalSeedConstraintBase_eq`
- `V2.HighRankPopulationInheritance.population_or_oversizedCanonicalSupportFiber`
- `V2.FixedIdentityPopulation.KernelFaithfulFixedIdentityRealization.identity_preserved_at_rank`

## Validation

The release uses Lean `v4.28.0` and Mathlib `v4.28.0`.

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check-sunflower-a-plus-audit.ps1
```

The audit:

- scans `SunflowerAASC/` and `Checks/Axiom/` for live `axiom`, `unsafe`,
  `sorry`, or `admit` declarations;
- builds the terminal `SunflowerAASC` target; and
- runs 25 focused `#print axioms` checks on the imported kernel and
  load-bearing closure anchors.

The reported dependencies are standard Lean/Mathlib principles such as
`propext`, `Classical.choice`, and `Quot.sound`, not project-specific axioms.

## Manuscript

The synchronized manuscript snapshot is under [`papers/sunflower`](papers/sunflower):

- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint.pdf`
- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint_Source.zip`

The manuscript and Lean release use the same closure boundary. Kernel
necessity is imported from its own mechanized repository; the target-specific
population theorem remains the explicit manuscript proof object; and every
step from that object to the sunflower and numerical endpoint is checked in
Lean.
