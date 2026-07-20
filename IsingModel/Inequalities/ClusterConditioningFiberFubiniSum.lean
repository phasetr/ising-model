import IsingModel.Inequalities.ClusterConditioningFiberFubiniSum.BlocksAndRestrict
import IsingModel.Inequalities.ClusterConditioningFiberFubiniSum.EquivAndFubini

/-!
# SL-D brick D1b part 2b: the gluing bijection `Φ` and the weight-level `tsum` Fubini

This module implements **ingredient SL-D, brick D1b part 2b** — the
**completion of `SL-D₁` (range independence)**
(`.self-local/tex/rc-oz-lemma51-SLD1b-part2.tex`, §③/④). Building on the part 2a
decoupling foundation (`Current.reachableCluster_confined_eq`,
`Current.sources_eq_sourcesOn_of_supported`,
`Current.summable_block_weight_if_sourcesOn`) it delivers the restriction/gluing
bijection between the pinned pivotal fiber and the product of the interior/exterior
block ensembles, and the resulting weight-level `tsum` Fubini
\[
  \Sigma_C \;=\; (\beta J)\cdot \Xi_{\mathrm{int}}\cdot \Xi_{\mathrm{ext}} .
\]

## Contents

* `Current.pivotalFiberSet`, `Current.interiorBlockSet`, `Current.exteriorBlockSet` —
  the pinned pivotal fiber `𝓕_C` and the interior/exterior block ensembles
  `𝒜_int`/`𝒜_ext`, all as subsets of the single ambient current type
  `Current G Λ = E → ℕ` (symmetric-difference source constraints `{x} △ {a}`,
  `{b} △ {y}`, part 1 correction). `𝒜_ext` is an **ambient** block weight sum; no
  subgraph current is ever formed.
* `Current.glueBlocks` — the gluing map `Ψ`, realised as the ambient sum
  `n_int + n_ext + 1_{e₀}` (equal, on block-supported inputs, to the piecewise glue
  that is `n_int` on `E_int`, `n_ext` on `E_ext`, `1` on the bridge `e₀`, and `0`
  on the remaining crossing edges).
* `Current.pivotalFiberEquiv` — the SL-D₁ range-independence **bijection**
  `Φ : 𝓕_C ≃ 𝒜_int × 𝒜_ext`, `Φ(M) = (M|_{E_int}, M|_{E_ext})`, with inverse the
  gluing `Ψ`. Its round-trips are per-edge `funext` case splits plus F2/F3 pinning;
  the reverse `EdgePivotal` reconstruction concatenates the three legs
  `x ⤳ a` / `a — b` / `b ⤳ y` and uses the part 2a confinement lemma for the
  non-reachability clause, and the D1a `ZMod 2` parity split for `sources = {x, y}`.
* `Current.pivotalNumerator_fiber_factor` — the headline **weight-level `tsum`
  Fubini** `Σ_C = (βJ)·Ξ_int·Ξ_ext`, proved by reindexing along `Φ`
  (`Equiv.tsum_eq`), the SL-C pointwise weight factorisation
  (`Current.weight_pivotal_fiber_factor`), and the product split
  `Summable.tsum_mul_tsum` fed by the part 2a block-summability lemma.

## Honest status: D1b part 2b = SL-D₁ complete, but Lemma 5.1 is NOT complete

D1b part 2b **completes `SL-D₁` (range independence)**: together with D1a, part 1
and part 2a it establishes the weight-level factorisation of the pinned pivotal
fiber sum with `Ξ_int`, `Ξ_ext` **ambient** block weight sums. It is an explicitly
**tracked ingredient** (Group 1a, SL-D₁), on the downstream path to the (future)
Lemma 5.1 → P2-ii → `hLogLip` → the lower-semicontinuity half of GJ Theorem 17.5.1
(§17.5, issue #4386 / thread #4418).

It introduces **no** subgraph current, **no** switching lemma, and **no**
identification of `Ξ_ext` with a two-point function. Therefore **the SL-D₂ core**
(the exterior → two-point collapse: conditioned-switching / subgraph-conditioning,
Aizenman Lemma 4.1) **awaits explicit user authorisation** and remains the gate:
**SL-D₁ completion does not complete Lemma 5.1** (SL-D₂ gates it). This module
touches none of SL-D₂; it stays reference-count zero into the live capstone. The
weight `Current.weight` is `∏_e (βJ)^{n_e}/n_e!`, the random-current weight of
Friedli–Velenik, eq. (3.45).

## References

* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §3.7, eq. (3.45).
* Glimm–Jaffe, *Quantum Physics* (2nd ed.), Theorem 17.5.1, p. 312 (lsc half,
  issue #4386 / thread #4418).
* Aizenman (1982), Lemma 4.1; Fernández–Fröhlich–Sokal (1992), Ch. 12.
-/
