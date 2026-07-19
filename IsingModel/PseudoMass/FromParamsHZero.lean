import IsingModel.PseudoMass.FromParamsHZero.JZeroJointRegularity

/-!
# Pseudo-Mass h-zero parameter specializations compatibility umbrella

This module preserves the historical import path for the split
`FromParamsHZero` wrapper layer.

## Standalone module (intentional)

This aggregator lies outside the transitive import closure of the root umbrella
`IsingModel.lean`, so it is not part of the assembled library: no
umbrella-reachable ("live") module imports it.  It is imported only within this
standalone cluster (by a sibling module), which is deliberately not wired into
the umbrella.  It should be retained rather than treated as dead code: it
aggregates the standalone `FromParamsHZero/*` regularity chain — genuine
regularity / value results for the `J = 0` / `h = 0` slices of
`pseudoMassFromParamsAtPair`, built on the live `PseudoMass/FromParamsBasic`
results.
-/
