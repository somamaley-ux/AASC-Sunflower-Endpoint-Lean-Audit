# Two-Track Sunflower Manuscript

This folder contains the release snapshot of **Two-Track Closure for the
Three-Petal Sunflower Endpoint**.

- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint.pdf` is the compiled
  31-page manuscript.
- `Two_Track_Closure_for_the_Three_Petal_Sunflower_Endpoint_Source.zip` contains
  the complete source package and the same compiled PDF.

The manuscript foregrounds the conventional combinatorial construction while
making the necessary kernel-governed crossing explicit. The kernel is imported
from its own pinned Lean repository and instantiated on the concrete Sunflower
endpoint. Manuscript Theorem 6.2's target-specific population result is
represented in Lean by
`ImportedManuscriptKernelGovernedPopulationTheorem`; all downstream steps to
the genuine sunflower and base-`8384512` endpoint are machine-checked.

The theorem is not restricted to an optional AASC regime: AASC identifies the
necessity conditions of non-degenerate determinate endpoint use. The release
does not claim a conventional AASC-free analogue or an independent Lean
reconstruction of the manuscript population proof.
