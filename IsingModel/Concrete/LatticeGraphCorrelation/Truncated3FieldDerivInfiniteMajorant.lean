import IsingModel.Concrete.LatticeGraphCorrelation.Truncated3FieldDerivCollarTail
import IsingModel.AmbientLattice.TruncatedFunctions.ThreePoint

/-!
# Infinite-volume Weierstrass majorant for the ∂/∂h site-sum (GJ Thm 17.6.1)

Reduced brick 3c toward the `h`-derivative of the connected two-point function
on `ℤ^d` (tracking issue #4413) and the **first infinite-volume statement** of
the `∂/∂h` brick chain (bricks 1--3 are all finite-volume).  It is the static
domination/summability layer behind Glimm--Jaffe Theorem 17.6.1 (*Quantum
Physics*, 2nd ed., p. 313): the infinite-volume side of the Weierstrass
`M`-test for the Ursell site-sum
`∂/∂h ⟨σ_i; σ_j⟩ = β · ∑_k U₃^∞(i, j, k)`.

Writing `m = simonLiebRate β J d` and, for a fixed site `a`,
`g_a(x) = exp(m) · exp(-m · d_{ℓ¹}(a, x))` (brick 2's per-site majorant term),
and `B(k) = g_i(k) + g_j(k)` for a fixed pair `i ≠ j`, this file transports the
field- and volume-uniform finite-volume bound of bricks 1+2 through the
exhaustion limit to the infinite-volume Ursell function
`U₃^∞(i, j, k) = truncated3Infinite (latticeGraph d) Λ p i j k`, and proves the
three consequences that constitute the `∞`-volume `M`-test:

* **(3c-i)** `abs_truncated3Infinite_le`: the per-term majorant
  `|U₃^∞(i, j, k)| ≤ B(k)` for distinct `i, j, k`.  At each exhaustion stage
  `n` with `i, j, k ∈ Λ.volume n`, the finite bricks
  `abs_truncated3_le` (brick 1) and two copies of brick 2a
  `truncated2_inducedLatticeGraph_le_exp_neg_simonLiebRate_of_field_nonneg` give
  `|truncated3AlongExhaustion n| ≤ B(k)` uniformly in `n` (via the stagewise
  identification `truncated3AlongExhaustion_eq_truncated3`); the bound passes to
  the limit by `le_of_tendsto` along
  `tendsto_truncated3AlongExhaustion_truncated3Infinite` and continuity of `|·|`.
* **(3c-ii)** `summable_truncated3Infinite`: summability of
  `k ↦ U₃^∞(i, j, k)`.  By `Finset.summable_compl_iff` on the finite diagonal
  `{i, j}` and the comparison test `Summable.of_norm_bounded` against the
  summable majorant `B` (brick 2b `summable_truncated2FiniteVolumeMajorant`).
* **(3c-iii)** `sum_abs_truncated3Infinite_compl_le_majorant_tail`: the
  complement-tail bound
  `∑_{k ∉ Λcut} |U₃^∞(i, j, k)| ≤ ∑_{x ∉ Λcut} g_i(x) + ∑_{x ∉ Λcut} g_j(x)`,
  whose right-hand side (the `Rem(m)` of brick 3a) tends to `0` by
  `tendsto_finiteVolumeMajorant_compl_atTop_zero`.  By `Summable.tsum_le_tsum`
  on the complement subtype and `Summable.tsum_add`.

**Scope caveat (load-bearing).** The derivative identity
`g'(h) = β · ∑_k U₃^∞(i, j, k)` — equivalently differentiation-under-the-tsum of
the infinite-volume two-point function — is **out of scope**: it presupposes the
frozen head-equicontinuity "wall" (isomorphic to #4386) and is **not** touched
here.  This file establishes only the domination/summability layer; it makes no
claim about `g'`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Theorem 17.6.1 (p. 313);
  §4.3, Cor. 4.3.4 (GHS), Cor. 4.3.3 (GKS-II); §18.7 (exponential decay).
* Fernández--Fröhlich--Sokal, *Random Walks, Critical Phenomena, and
  Triviality* (1992), Ch 12 (Simon--Lieb decay).
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **(3c-i) Per-term `∞`-volume Weierstrass majorant** (GJ Thm 17.6.1, p. 313):
for a ferromagnetic field `⟨J, h, β⟩` with `h ≥ 0`, strict high temperature
`0 < β J · 2d < 1`, an exhaustion with every induced subgraph `Preconnected`,
and pairwise distinct sites `i, j, k`,
`|truncated3Infinite (latticeGraph d) Λ ⟨J,h,β⟩ i j k| ≤ B(k)`,
`B(k) = exp(m) · exp(-m · d_{ℓ¹}(i,k)) + exp(m) · exp(-m · d_{ℓ¹}(j,k))`,
`m = simonLiebRate β J d`.

At each stage `n` with `i, j, k ∈ Λ.volume n`, the stagewise identification
`truncated3AlongExhaustion_eq_truncated3` turns the along-exhaustion Ursell term
into the finite-volume `truncated3` on `inducedGraph (latticeGraph d)
(Λ.volume n)`, where brick 1 `abs_truncated3_le` gives
`|U₃| ≤ τ₂(i,k) + τ₂(j,k)` and two applications of brick 2a bound each
`τ₂(a,k) ≤ g_a(k)` (reachability from `Preconnected`), uniformly in `n`.  The
constant majorant `B(k)` passes to the limit by `le_of_tendsto` along
`tendsto_truncated3AlongExhaustion_truncated3Infinite` and continuity of `|·|`. -/
theorem abs_truncated3Infinite_le
    (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J h : ℝ} (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ))
    (hβJ2d_pos : 0 < β * J * (2 * (d : ℝ))) (hβJ2d_lt : β * J * (2 * (d : ℝ)) < 1)
    (hconn : ∀ n, (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).Preconnected)
    {i j k : Fin d → ℤ} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    |truncated3Infinite (IsingModel.latticeGraph d) Λ (⟨J, h, β⟩ : IsingParams ℝ) i j k|
      ≤ Real.exp (simonLiebRate β J d)
            * Real.exp (-(simonLiebRate β J d) * (latticeDistance d i k : ℝ))
        + Real.exp (simonLiebRate β J d)
            * Real.exp (-(simonLiebRate β J d) * (latticeDistance d j k : ℝ)) := by
  have hβJ2d_le : β * J * (2 * (d : ℝ)) ≤ 1 := hβJ2d_lt.le
  have htend := tendsto_truncated3AlongExhaustion_truncated3Infinite
    (IsingModel.latticeGraph d) Λ (⟨J, h, β⟩ : IsingParams ℝ) hf i j k
  refine le_of_tendsto htend.abs ?_
  obtain ⟨N, hN⟩ := Λ.exhaust ({i, j, k} : Finset (Fin d → ℤ))
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have habc : ({i, j, k} : Finset (Fin d → ℤ)) ⊆ Λ.volume n := hN n hn
  have hi : i ∈ Λ.volume n := habc (by simp)
  have hj : j ∈ Λ.volume n := habc (by simp)
  have hk : k ∈ Λ.volume n := habc (by simp)
  simp only [truncated3AlongExhaustion_eq_truncated3
    (IsingModel.latticeGraph d) Λ (⟨J, h, β⟩ : IsingParams ℝ) i j k hi hj hk]
  have hik' : (⟨i, hi⟩ : ↑(Λ.volume n)) ≠ ⟨k, hk⟩ := fun h => hik (Subtype.mk.inj h)
  have hjk' : (⟨j, hj⟩ : ↑(Λ.volume n)) ≠ ⟨k, hk⟩ := fun h => hjk (Subtype.mk.inj h)
  have hij' : (⟨i, hi⟩ : ↑(Λ.volume n)) ≠ ⟨j, hj⟩ := fun h => hij (Subtype.mk.inj h)
  have hbrick := abs_truncated3_le
    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
    (⟨J, h, β⟩ : IsingParams ℝ) hf hij' hjk' hik'
  have hik2 := truncated2_inducedLatticeGraph_le_exp_neg_simonLiebRate_of_field_nonneg
    d (Λ.volume n) hf hβJ2d_pos hβJ2d_le hik' (hconn n ⟨i, hi⟩ ⟨k, hk⟩)
  have hjk2 := truncated2_inducedLatticeGraph_le_exp_neg_simonLiebRate_of_field_nonneg
    d (Λ.volume n) hf hβJ2d_pos hβJ2d_le hjk' (hconn n ⟨j, hj⟩ ⟨k, hk⟩)
  have ei : ((⟨i, hi⟩ : ↑(Λ.volume n)) : Fin d → ℤ) = i := rfl
  have ej : ((⟨j, hj⟩ : ↑(Λ.volume n)) : Fin d → ℤ) = j := rfl
  have ek : ((⟨k, hk⟩ : ↑(Λ.volume n)) : Fin d → ℤ) = k := rfl
  rw [ei, ek] at hik2
  rw [ej, ek] at hjk2
  linarith

/-- **(3c-ii) Summability of the `∞`-volume site-sum** (GJ Thm 17.6.1, p. 313):
for a ferromagnetic field `⟨J, h, β⟩` with `h ≥ 0`, strict high temperature
`0 < β J · 2d < 1`, an exhaustion with every induced subgraph `Preconnected`,
and fixed distinct `i ≠ j`, the family
`k ↦ truncated3Infinite (latticeGraph d) Λ ⟨J,h,β⟩ i j k` is summable over `ℤ^d`.

Removing the two diagonal indices `{i, j}` (a finite modification, harmless for
summability by `Finset.summable_compl_iff`), the off-diagonal family is
dominated on the complement subtype by the summable majorant
`B(k) = g_i(k) + g_j(k)` (brick 2b `summable_truncated2FiniteVolumeMajorant`,
term-bound (3c-i) `abs_truncated3Infinite_le`), so the comparison test
`Summable.of_norm_bounded` concludes. -/
theorem summable_truncated3Infinite
    (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J h : ℝ} (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ))
    (hβJ2d_pos : 0 < β * J * (2 * (d : ℝ))) (hβJ2d_lt : β * J * (2 * (d : ℝ)) < 1)
    (hconn : ∀ n, (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).Preconnected)
    {i j : Fin d → ℤ} (hij : i ≠ j) :
    Summable (fun k : Fin d → ℤ =>
      truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i j k) := by
  have hm : 0 < simonLiebRate β J d := simonLiebRate_pos hβJ2d_pos hβJ2d_lt
  rw [← Finset.summable_compl_iff (s := ({i, j} : Finset (Fin d → ℤ)))]
  refine Summable.of_norm_bounded
    (((summable_truncated2FiniteVolumeMajorant hm i).add
        (summable_truncated2FiniteVolumeMajorant hm j)).comp_injective
      Subtype.coe_injective) (fun k => ?_)
  have hki : i ≠ (k : Fin d → ℤ) := fun h => k.2 (by simp [← h])
  have hkj : j ≠ (k : Fin d → ℤ) := fun h => k.2 (by simp [← h])
  rw [Real.norm_eq_abs]
  exact abs_truncated3Infinite_le d Λ hf hβJ2d_pos hβJ2d_lt hconn hij hki hkj

/-- **(3c-iii) Complement-tail bound of the `∞`-volume site-sum** (GJ
Thm 17.6.1, p. 313, Weierstrass `M`-test tail): for a ferromagnetic field
`⟨J, h, β⟩` with `h ≥ 0`, strict high temperature `0 < β J · 2d < 1`, an
exhaustion with every induced subgraph `Preconnected`, and distinct `i ≠ j` with
`i, j ∈ Λcut`, the complement-tail absolute Ursell site-sum is bounded by the two
complement majorant tsums:
`∑_{k ∉ Λcut} |truncated3Infinite (latticeGraph d) Λ ⟨J,h,β⟩ i j k|
≤ ∑_{x ∉ Λcut} g_i(x) + ∑_{x ∉ Λcut} g_j(x)`,
`g_a(x) = exp(m) · exp(-m · d_{ℓ¹}(a,x))`, `m = simonLiebRate β J d`.

Each `k ∉ Λcut` satisfies `k ≠ i, j` (since `i, j ∈ Λcut`), so the term-bound
(3c-i) `abs_truncated3Infinite_le` gives `|U₃^∞(i,j,k)| ≤ g_i(k) + g_j(k)`;
`Summable.of_nonneg_of_le` makes the absolute family summable on the complement
subtype, and `Summable.tsum_le_tsum` with `Summable.tsum_add` splits the bound
into the two complement tsums.  The right-hand side is the `Rem(m)` that brick 3a
`tendsto_finiteVolumeMajorant_compl_atTop_zero` sends to `0`. -/
theorem sum_abs_truncated3Infinite_compl_le_majorant_tail
    (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J h : ℝ} (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ))
    (hβJ2d_pos : 0 < β * J * (2 * (d : ℝ))) (hβJ2d_lt : β * J * (2 * (d : ℝ)) < 1)
    (hconn : ∀ n, (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).Preconnected)
    (Λcut : Finset (Fin d → ℤ)) {i j : Fin d → ℤ}
    (hi : i ∈ Λcut) (hj : j ∈ Λcut) (hij : i ≠ j) :
    ∑' k : {k : Fin d → ℤ // k ∉ Λcut},
        |truncated3Infinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i j (k : Fin d → ℤ)|
      ≤ (∑' x : {x : Fin d → ℤ // x ∉ Λcut},
            Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d i (x : Fin d → ℤ) : ℝ)))
        + (∑' x : {x : Fin d → ℤ // x ∉ Λcut},
            Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d j (x : Fin d → ℤ) : ℝ))) := by
  have hm : 0 < simonLiebRate β J d := simonLiebRate_pos hβJ2d_pos hβJ2d_lt
  have hsi : Summable (fun x : {x : Fin d → ℤ // x ∉ Λcut} =>
      Real.exp (simonLiebRate β J d)
        * Real.exp (-(simonLiebRate β J d)
            * (latticeDistance d i (x : Fin d → ℤ) : ℝ))) :=
    (summable_truncated2FiniteVolumeMajorant hm i).comp_injective Subtype.coe_injective
  have hsj : Summable (fun x : {x : Fin d → ℤ // x ∉ Λcut} =>
      Real.exp (simonLiebRate β J d)
        * Real.exp (-(simonLiebRate β J d)
            * (latticeDistance d j (x : Fin d → ℤ) : ℝ))) :=
    (summable_truncated2FiniteVolumeMajorant hm j).comp_injective Subtype.coe_injective
  have hbound : ∀ k : {k : Fin d → ℤ // k ∉ Λcut},
      |truncated3Infinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i j (k : Fin d → ℤ)|
        ≤ Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d i (k : Fin d → ℤ) : ℝ))
          + Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d j (k : Fin d → ℤ) : ℝ)) := by
    intro k
    have hki : i ≠ (k : Fin d → ℤ) := fun h => k.2 (h ▸ hi)
    have hkj : j ≠ (k : Fin d → ℤ) := fun h => k.2 (h ▸ hj)
    exact abs_truncated3Infinite_le d Λ hf hβJ2d_pos hβJ2d_lt hconn hij hki hkj
  have hsum_abs : Summable (fun k : {k : Fin d → ℤ // k ∉ Λcut} =>
      |truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i j (k : Fin d → ℤ)|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hbound (hsi.add hsj)
  calc ∑' k : {k : Fin d → ℤ // k ∉ Λcut},
          |truncated3Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, h, β⟩ : IsingParams ℝ) i j (k : Fin d → ℤ)|
      ≤ ∑' k : {k : Fin d → ℤ // k ∉ Λcut},
          (Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d i (k : Fin d → ℤ) : ℝ))
            + Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d j (k : Fin d → ℤ) : ℝ))) :=
        hsum_abs.tsum_le_tsum hbound (hsi.add hsj)
    _ = (∑' x : {x : Fin d → ℤ // x ∉ Λcut},
            Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d i (x : Fin d → ℤ) : ℝ)))
          + (∑' x : {x : Fin d → ℤ // x ∉ Λcut},
              Real.exp (simonLiebRate β J d)
                * Real.exp (-(simonLiebRate β J d)
                    * (latticeDistance d j (x : Fin d → ℤ) : ℝ))) :=
        hsi.tsum_add hsj

end Ambient

end IsingModel
