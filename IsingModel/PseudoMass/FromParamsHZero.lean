import IsingModel.PseudoMass.FromParamsHZero.JZeroJointRegularity

/-!
# Pseudo-Mass h-zero parameter specializations compatibility umbrella

This module preserves the historical import path for the split
`FromParamsHZero` wrapper layer.

## Standalone module (intentional)

This aggregator is not imported by the root umbrella `IsingModel.lean` and has
no downstream consumers in the import graph.  It is retained deliberately: it
aggregates the standalone `FromParamsHZero/*` regularity chain (genuine
regularity / value results for the `J = 0` / `h = 0` slices of
`pseudoMassFromParamsAtPair`, built on the live `PseudoMass/FromParamsBasic`
results).  It is NOT dead code and must NOT be removed; it is simply not wired
into the umbrella.
-/
