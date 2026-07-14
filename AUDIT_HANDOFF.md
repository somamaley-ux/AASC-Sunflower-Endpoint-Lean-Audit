# Audit Handoff

## Reviewer Entry

Start with `SunflowerAASC/V2/MechanizedKernelImport.lean`, then read
`SunflowerAASC/V2/ManuscriptKernelTransfer.lean`. The first file is the actual
bridge to the pinned standalone kernel repository. The terminal theorems are:

- `sunflower_of_importedManuscriptKernelGovernedClosure`;
- `ImportedManuscriptKernelGovernedPopulationTheorem.provesEndpointBound`; and
- `nonempty_importedManuscriptPopulationTheorem_iff_endpointBound`.

The first proves an actual three-petal sunflower from a base-`8384512` size
excess. The second states the complete endpoint. The third audits the exact
strength of the manuscript import.

Also inspect:

- `mechanizedKernelDependencyCertificate`;
- `KernelImportRoute.noSameDomainDerivationBelowKernel`; and
- `KernelImportRoute.governanceEquivalentReplacement_hasKernel`.

These show that kernel necessity and fixed-domain no-lower-governance are
machine-linked rather than prose-only dependencies.

## Validation

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check-sunflower-a-plus-audit.ps1
```

The script scans all published Lean source, builds the one-module public
entrypoint, and runs the focused axiom audit in
`Checks/Axiom/SunflowerAPlusAudit.lean`.

## Claim Discipline

The strongest supported description is:

> A manuscript-faithful Lean mechanization that imports the separately
> mechanized necessity kernel, instantiates it on the determinate Sunflower
> endpoint, and verifies the complete closure from the typed manuscript
> population theorem to a genuine three-petal sunflower and the
> base-`8384512` endpoint.

The exact boundary is load-bearing. Kernel necessity is a pinned Lean
dependency; the corpus proof of the target-specific population theorem remains
in the manuscript/corpus rather than being independently formalized here. An
AASC-free conventional analogue is not claimed.

Calling the mathematical theorem conditional on an optional AASC regime is
incorrect: AASC names the necessity conditions of the determinate objects and
operations already quantified. Calling the Lean population field a modular
proof boundary is correct.

No other Lean-side closure source remains uninstantiated after that import.
