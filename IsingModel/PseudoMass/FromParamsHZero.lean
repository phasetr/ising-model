import IsingModel.PseudoMass.FromParamsHZero.JZeroJointRegularity

/-!
# Pseudo-Mass h-zero parameter specializations compatibility umbrella

This module preserves the historical import path for the split
`FromParamsHZero` wrapper layer.

## Umbrella-reachable via its cluster head

This module has no importers outside its own cluster.  The cluster head is
registered in the root umbrella `IsingModel.lean`, so this module lies inside
the transitive import closure of `import IsingModel` and is therefore covered by
the capstone axiom audit (`scripts/audit_gate.py`, check V3).  It
aggregates the standalone `FromParamsHZero/*` regularity chain — genuine
regularity / value results for the `J = 0` / `h = 0` slices of
`pseudoMassFromParamsAtPair`, built on the live `PseudoMass/FromParamsBasic`
results.
-/
