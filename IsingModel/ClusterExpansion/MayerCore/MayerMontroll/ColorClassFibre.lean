import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre.FibreBijection
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre.FibreFilterSum
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre.FamilyTupleSum
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre.ColorDegreeBounds
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre.MayerMontrollIdentity

/-!
# The `r!`-to-one colour-class fibre (GJ §18.4)

The final stage of the Mayer–Montroll regrouping.  A family-tuple is recovered
as the colour classes of `r!` distinct sequence/colouring pairs
(`card_proper_colorClass_fiber`), so the fibre activity sum is `r! · W(Ω)`
(`fiber_sum_clusterSeqActivity`).  Assembling the fibre factor with the
colouring form of the Mayer terms yields the Mayer–Montroll identity
`log Ξ = ∑ₙ mayerExpansionTerm` at finite volume
(`mayer_identity_general_t`, `mayer_identity_general_t_eventually`).  Part of the
`MayerMontroll` identity split.

## Contents

The declarations live in five child modules, re-exported by this declaration-free facade:

* `….ColorClassFibre.FibreBijection` — the labelled-polymer set `labelledPolymers` and its
  cardinality, the forward map `(ω, c) ↦ (i ↦ ⟨c i, ω i⟩)` with well-definedness,
  injectivity and surjectivity, the inverse direction (`invColorClass`, `invProper`), the
  fibre cardinality `card_proper_colorClass_fiber = r!` and the fibre activity sum
  `r! · W(Ω)`.
* `….ColorClassFibre.FibreFilterSum` — the `Finset`-filter reformulations: the fibre sum as
  a filtered product-`Finset` sum, the colour-count sum as a product-`Finset` sum, its
  regrouping by colour classes, and the evaluated inner fibre sum (`r!·W(Ω)` or `0`).
* `….ColorClassFibre.FamilyTupleSum` — the per-`m` Mayer–Montroll identity
  `vdFamilyTuple_sum_eq_seq_coloring_sum` and the over-long-sequence vanishing
  `properSurjectiveColorings_empty_of_card_lt`.
* `….ColorClassFibre.ColorDegreeBounds` — the Mayer term and the log-Taylor term in
  colouring form together with the analytic majorants (`#colourings ≤ k^r`, the per-`(r,k)`
  bound, the row bound, and the summability of `∑ (r^r/r!)|A|^r`).
* `….ColorClassFibre.MayerMontrollIdentity` — the colour-degree term `colorDegreeTerm` with
  its vanishing lemmas, the row and column `tsum` collapses, the double summability, and the
  capstones `mayer_identity_general_t` / `mayer_identity_general_t_eventually`.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (p. 332) – §18.5 (p. 335).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7.3 (Mayer–Cayley).
-/
