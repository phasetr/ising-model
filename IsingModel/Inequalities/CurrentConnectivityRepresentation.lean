import IsingModel.Inequalities.SimonLieb
import IsingModel.RandomCurrent.Switching.GlobalSwitchingLimit

/-!
# Connectivity (percolation) representation of the two-point function

This file assembles **Stage B** of the random-current build toward the
lower-semicontinuous half of Glimm–Jaffe Theorem 17.5.1 (issue #4386,
thread #4418): the *weighted-sum connectivity representation*
\[
  \langle\sigma_x\sigma_y\rangle^{\Lambda}\cdot Z_\emptyset^{2}
  = \sum_{\substack{M\ :\ x\leftrightarrow y}}
    \sum_{\substack{m\le M,\ \partial m=\{x,y\},\ \partial(M-m)=\emptyset}}
      w(m)\,w(M-m),
\]
i.e. the two-point function (times the sourcefree normalization squared)
equals the weighted `tsum` over *doubled currents whose support connects
`x` to `y`*. This is Aizenman's
`⟨σ_xσ_y⟩ = ℙ^{∅,∅}[x ↔ y]` with **no probability measure formalized**:
`weightSum ∅` plays the role of the (unnormalized) partition mass of the
doubled sourcefree ensemble, and the restricted `tsum` is the mass of the
connection event.

The identity is *true* — every step is an equality:
* (P) `correlation_inducedGraph_eq_weightSum_ratio` (the ratio form);
* (GS∞) `Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset`
  (Stage A brick 2, the unbounded switching identity);
* support-exactness of a `tsum` via
  `tsum_subtype_eq_of_support_subset`, justified by B2
  (`Current.doubled_pair_sum_eq_zero_of_not_reachable`) which vanishes off
  the connection set.

No inequality is introduced at this stage.

## References

* Aizenman, M. (1982). Geometric analysis of φ⁴ fields, Lemma 4.1.
* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and
  Triviality* (1992), Chapter 12.
* Glimm–Jaffe, *Quantum Physics*, §5.1 and §17.5 Theorem 17.5.1 (p. 312);
  Friedli–Velenik, §3.7 and Theorem 9.35.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **Connectivity representation, weighted-sum form (Stage B capstone)**:
for `x ≠ y ∈ Λ` and non-negative coupling `0 ≤ β J` (zero field `h = 0`),
\[
  \langle\sigma_x\sigma_y\rangle^{\Lambda}\cdot Z_\emptyset^{2}
  = \sum_{\substack{M\ :\ (M.\mathrm{toSimpleGraph}).\mathrm{Reachable}\ x\ y}}
    \sum_{\substack{m\le M,\ \partial m=\{x,y\},\ \partial(M-m)=\emptyset}}
      w(m)\,w(M-m),
\]
where the outer sum is a `tsum` over the *subtype* of doubled currents `M`
whose support graph connects `x` to `y`.

Proof: (P) `correlation_inducedGraph_eq_weightSum_ratio` gives
`correlation {x,y} · (weightSum ∅)² = weightSum {x,y} · weightSum ∅`
(cancelling the positive `weightSum ∅`, `Current.weightSum_empty_pos`);
(GS∞) `Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset` with
`A = {x,y}`, `B = ∅` rewrites the right side as `∑' M, F M`; finally
`tsum_subtype_eq_of_support_subset` restricts the sum to the connection
subtype, since `Function.support F` sits inside it by the contrapositive
of B2 (`Current.doubled_pair_sum_eq_zero_of_not_reachable`).
(Aizenman 1982 Lemma 4.1 / FV Theorem 9.35 / GJ §17.5.) -/
theorem Current.correlation_mul_weightSum_empty_sq_eq_tsum_reachable_doubled
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {x y : ↑Λ} (hxy : x ≠ y) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y}
        * Current.weightSum G Λ ∅ β J ^ 2
      = ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          ∑ m ∈ (Current.subFinset G Λ (M : Current G Λ)).filter
              (fun m => m.sources G Λ = {x, y}
                ∧ ((M : Current G Λ) - m).sources G Λ = ∅),
            m.weight G Λ β J * ((M : Current G Λ) - m).weight G Λ β J := by
  classical
  set F : Current G Λ → ℝ := fun M =>
    ∑ m ∈ (Current.subFinset G Λ M).filter
        (fun m => m.sources G Λ = {x, y} ∧ (M - m).sources G Λ = ∅),
      m.weight G Λ β J * (M - m).weight G Λ β J with hFdef
  have hW : 0 < Current.weightSum G Λ ∅ β J := Current.weightSum_empty_pos G Λ hβJ
  -- Step (P): the left side equals `weightSum {x,y} · weightSum ∅`.
  have h1 : correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y}
        * Current.weightSum G Λ ∅ β J ^ 2
      = Current.weightSum G Λ {x, y} β J * Current.weightSum G Λ ∅ β J := by
    rw [correlation_inducedGraph_eq_weightSum_ratio G Λ hβJ {x, y}]
    field_simp
  -- Step (GS∞): brick 2 with `A = {x,y}`, `B = ∅`.
  have h2 : Current.weightSum G Λ {x, y} β J * Current.weightSum G Λ ∅ β J
      = ∑' M : Current G Λ, F M := by
    simpa only [hFdef] using
      Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset G Λ {x, y} ∅ hβJ
  -- The summand `F` is supported on the `x ↔ y` connection set (B2).
  have hsupp : Function.support F ⊆ {M | (M.toSimpleGraph G Λ).Reachable x y} := by
    intro M hM
    rw [Function.mem_support, hFdef] at hM
    by_contra hnr
    exact hM (Current.doubled_pair_sum_eq_zero_of_not_reachable G Λ hxy M hnr)
  rw [h1, h2]
  exact (tsum_subtype_eq_of_support_subset hsupp).symm

end Ambient
end IsingModel
