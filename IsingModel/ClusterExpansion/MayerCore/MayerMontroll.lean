import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ProperColorings
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.EdgeInclusionExclusion
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre

/-!
# Mayer–Montroll identity `log Ξ = ∑ₙ mayerExpansionTerm` (GJ §18.4, Issue #1499 Phase C)

This file is an umbrella re-exporting the §18.4 capstone, the general-`t` Mayer
expansion identity `polymerFreeEnergy G t = ∑' n, mayerExpansionTerm G n t` at
finite volume, split for build modularity into the child modules under
`IsingModel.ClusterExpansion.MayerCore.MayerMontroll`.

The content is organized as:

* `MayerMontroll.ProperColorings` — log-Taylor term as a family-tuple sum and the
  proper surjective colouring universe;
* `MayerMontroll.EdgeInclusionExclusion` — edge inclusion–exclusion for proper
  colourings and the Mayer–Montroll colouring identity;
* `MayerMontroll.ColorClassFibre` — the `r!`-to-one colour-class fibre and the
  assembled Mayer–Montroll identity.

Importing this module re-exports every declaration of the split, so existing
downstream imports of `IsingModel.ClusterExpansion.MayerCore.MayerMontroll` are
unaffected.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (p. 332) – §18.5 (p. 335).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7.3 (Mayer–Cayley).
-/
