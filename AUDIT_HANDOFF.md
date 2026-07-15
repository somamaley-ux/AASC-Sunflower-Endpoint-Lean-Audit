# Audit Handoff

## Reviewer Entry

Start with:

1. `SunflowerAASC/V2/GeneratedIncidenceTower.lean`;
2. `SunflowerAASC/V2/GeneratedSeedCapacity.lean`;
3. `SunflowerAASC/V2/MechanizedKernelImport.lean`; and
4. `SunflowerAASC/V2/ManuscriptKernelTransfer.lean`.

The first file is the constructive repair. Its main anchors are:

- `nextCoordinate_nonempty`;
- `incidencePath_nonempty`;
- `exists_reachesTerminalCarrier`; and
- `terminalFamily_noSunflower`.

They prove that every initial blocker coordinate has a generated path to a
literal terminal blocker coordinate. This result has no governance,
population, code, fibre-bound, or endpoint premise.

The second file gives the exact handoff:

- `KernelFaithfulStandingPathBridge.standingCarrier_reachable`;
- `standingCarrier_choice_independent`;
- `standingCarrierOf_injective`; and
- `cell_card_le_4094`.

Inspect the structure fields before the consequences. They make the remaining
paper-level obligations visible and prevent AASC from being credited with
positive generation.

## Legacy Endpoint Route

`ManuscriptKernelTransfer.lean` still contains:

- `sunflower_of_importedManuscriptKernelGovernedClosure`;
- `ImportedManuscriptKernelGovernedPopulationTheorem.provesEndpointBound`; and
- `nonempty_importedManuscriptPopulationTheorem_iff_endpointBound`.

These audit every downstream step and the exact endpoint strength of the older
population import. They are retained for correspondence, not presented as the
new constructive repair.

## Validation

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check-sunflower-a-plus-audit.ps1
```

The script scans the published Lean tree, builds the public entrypoint, and
runs the 42 focused axiom checks in
`Checks/Axiom/SunflowerAPlusAudit.lean`.

## Claim Discipline

The strongest supported description is:

> Lean constructs the complete source-by-source blocker-incidence path
> relation and literal terminal carriers without AASC, then verifies the
> choice-independent injective `4094` consequence of an explicit
> relation-level kernel bridge. The manuscript supplies the
> sunflower-specific proof of that bridge; its direct corpus-to-Lean
> constructor remains the stated internalization boundary.

Do not describe the path theorem as conditional. Do not describe the full
corpus-to-bridge theorem as already unparameterized in Lean. Do not call the
mathematical kernel dependency an optional family predicate.
