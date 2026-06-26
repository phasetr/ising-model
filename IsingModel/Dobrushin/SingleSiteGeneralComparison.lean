import IsingModel.Dobrushin.OscillationPropagation
import IsingModel.Dobrushin.BoundaryInfluence

/-!
# The general single-site Dobrushin comparison inequality (GJ §17.1, Issue #4201)

The boundary-influence bound `gibbsExpectationBC_singleton_localObs_agreesOff_dist_le` handles only
observables **local at the resampled site** `x`. The Dobrushin comparison capstone, however,
applies the heat-bath operator `K_x` to *non-local* observables (the results of partial Gibbs
sweeps), so the single-site comparison is needed for a **general** observable. This file supplies
it, together with the underlying "observable telescoping" bound.

* `abs_sub_update_spin_le_siteOsc` — changing the spin at `x` (between any two values) changes `f`
  by at most `siteOsc x f`.
* `agreesOff_dist_le_sum_siteOsc` — the **observable telescoping**: if `η, η'` agree off `S` then
  `|f η − f η'| ≤ ∑_{y∈S} siteOsc y f` (flip the differing spins one at a time).
* `heatBath_agreesOff_dist_le` — the **general single-site comparison** (the per-site Dobrushin
  inequality): for `η, η'` agreeing off `S`,
  `|K_x f η − K_x f η'| ≤ #(S ∩ nbr(x))·tanh(βJ)·siteOsc x f + ∑_{y∈S} siteOsc y f` — the
  C-propagated `x`-oscillation plus the direct observable oscillation.
* `sum_isingInfluence_eq` / `heatBath_agreesOff_dist_le_influence` — the influence-matrix form,
  `#(S ∩ nbr(x))·tanh(βJ) = ∑_{y∈S} C_{xy}`, feeding the resolvent comparison.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

omit [Fintype G.edgeSet] [DecidableRel G.Adj] in
/-- **The single-site change between any two spin values is at most the oscillation**: for any
configuration `σ` and spins `a, b`, `|f (σ[x↦a]) − f (σ[x↦b])| ≤ siteOsc x f`. -/
theorem abs_sub_update_spin_le_siteOsc (x : ι) (f : Config ι → ℝ) (σ : Config ι) (a b : Spin) :
    |f (Function.update σ x a) - f (Function.update σ x b)| ≤ siteOsc x f := by
  cases a <;> cases b
  · simp only [sub_self, abs_zero]; exact siteOsc_nonneg x f
  · exact abs_sub_update_le_siteOsc x f σ
  · rw [abs_sub_comm]; exact abs_sub_update_le_siteOsc x f σ
  · simp only [sub_self, abs_zero]; exact siteOsc_nonneg x f

omit [Fintype G.edgeSet] [DecidableRel G.Adj] in
/-- **Observable telescoping** (GJ §17.1): if `η` and `η'` agree off a finite set `S`, then the
values of any observable `f` differ by at most the sum of the single-site oscillations over `S`,
`|f η − f η'| ≤ ∑_{y∈S} siteOsc y f`. Proved by flipping the differing spins one at a time, each
flip bounded by `abs_sub_update_spin_le_siteOsc`. -/
theorem agreesOff_dist_le_sum_siteOsc (f : Config ι → ℝ) {S : Finset ι} {η η' : Config ι}
    (hagree : agreesOff S η η') :
    |f η - f η'| ≤ ∑ y ∈ S, siteOsc y f := by
  classical
  induction S using Finset.induction_on generalizing η' with
  | empty =>
    obtain rfl : η' = η := funext fun i => hagree i (Finset.notMem_empty i)
    simp
  | @insert a S' ha ih =>
    set τ := Function.update η' a (η a) with hτ
    have hagrτ : agreesOff S' η τ := by
      intro i hi
      by_cases hia : i = a
      · subst hia; rw [hτ, Function.update_self]
      · rw [hτ, Function.update_of_ne hia]
        exact hagree i (fun hins => hi ((Finset.mem_insert.mp hins).resolve_left hia))
    have h1 := ih hagrτ
    have h2 : |f τ - f η'| ≤ siteOsc a f := by
      have heq : f η' = f (Function.update η' a (η' a)) := by rw [Function.update_eq_self]
      rw [hτ, heq]
      exact abs_sub_update_spin_le_siteOsc a f η' (η a) (η' a)
    have hsplit : |f η - f η'| ≤ |f η - f τ| + |f τ - f η'| := by
      have := abs_add_le (f η - f τ) (f τ - f η')
      rwa [sub_add_sub_cancel] at this
    rw [Finset.sum_insert ha]
    calc |f η - f η'| ≤ |f η - f τ| + |f τ - f η'| := hsplit
      _ ≤ (∑ y ∈ S', siteOsc y f) + siteOsc a f := add_le_add h1 h2
      _ = siteOsc a f + ∑ y ∈ S', siteOsc y f := by ring

/-- **The general single-site Dobrushin comparison inequality** (GJ §17.1): for `0 ≤ βJ` and two
boundary configurations `η, η'` agreeing off a finite set `S`, the single-site heat-bath expectation
of *any* observable `f` differs by at most the C-propagated `x`-oscillation plus the direct
observable oscillation,
`|K_x f η − K_x f η'| ≤ #(S ∩ nbr(x))·tanh(βJ)·siteOsc x f + ∑_{y∈S} siteOsc y f`. -/
theorem heatBath_agreesOff_dist_le {β J : ℝ} (hβJ : 0 ≤ β * J) (h : ℝ) (x : ι)
    {S : Finset ι} {η η' : Config ι} (f : Config ι → ℝ) (hagree : agreesOff S η η') :
    |heatBath G β J h x f η - heatBath G β J h x f η'|
      ≤ ((S ∩ G.neighborFinset x).card : ℝ) * Real.tanh (β * J) * siteOsc x f
        + ∑ y ∈ S, siteOsc y f := by
  classical
  have htanh_nonneg : 0 ≤ Real.tanh (β * J) := real_tanh_nonneg hβJ
  simp only [heatBath]
  rw [gibbsExpectationBC_singleton_eq G β J h x η f, gibbsExpectationBC_singleton_eq G β J h x η' f]
  set p := singleSiteUpProbBC G β J h x η with hp
  set p' := singleSiteUpProbBC G β J h x η' with hp'
  set Aη := f (Function.update η x Spin.up) with hAη
  set Bη := f (Function.update η x Spin.down) with hBη
  set Aη' := f (Function.update η' x Spin.up) with hAη'
  set Bη' := f (Function.update η' x Spin.down) with hBη'
  have key : p * Aη + (1 - p) * Bη - (p' * Aη' + (1 - p') * Bη')
      = (p - p') * (Aη - Bη) + (p' * (Aη - Aη') + (1 - p') * (Bη - Bη')) := by ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  have hbound1 : |(p - p') * (Aη - Bη)|
      ≤ ((S ∩ G.neighborFinset x).card : ℝ) * Real.tanh (β * J) * siteOsc x f := by
    rw [abs_mul]
    refine mul_le_mul (singleSiteUpProbBC_agreesOff_dist_le G hβJ h x hagree)
      (abs_sub_update_le_siteOsc x f η) (abs_nonneg _) ?_
    exact mul_nonneg (Nat.cast_nonneg _) htanh_nonneg
  have hp'_nonneg : 0 ≤ p' := by rw [hp', singleSiteUpProbBC]; exact isingSingleSiteUpProb_nonneg _
  have hp'_le_one : p' ≤ 1 := by rw [hp', singleSiteUpProbBC]; exact isingSingleSiteUpProb_le_one _
  have hAdiff : |Aη - Aη'| ≤ ∑ y ∈ S, siteOsc y f := by
    have hag2 : agreesOff S (Function.update η x Spin.up) (Function.update η' x Spin.up) := by
      intro i hi
      by_cases hix : i = x
      · subst hix; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hix, Function.update_of_ne hix]; exact hagree i hi
    exact agreesOff_dist_le_sum_siteOsc f hag2
  have hBdiff : |Bη - Bη'| ≤ ∑ y ∈ S, siteOsc y f := by
    have hag2 : agreesOff S (Function.update η x Spin.down) (Function.update η' x Spin.down) := by
      intro i hi
      by_cases hix : i = x
      · subst hix; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hix, Function.update_of_ne hix]; exact hagree i hi
    exact agreesOff_dist_le_sum_siteOsc f hag2
  have hbound2 : |p' * (Aη - Aη') + (1 - p') * (Bη - Bη')| ≤ ∑ y ∈ S, siteOsc y f := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hp'_nonneg,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - p')]
    calc p' * |Aη - Aη'| + (1 - p') * |Bη - Bη'|
        ≤ p' * (∑ y ∈ S, siteOsc y f) + (1 - p') * (∑ y ∈ S, siteOsc y f) :=
          add_le_add (mul_le_mul_of_nonneg_left hAdiff hp'_nonneg)
            (mul_le_mul_of_nonneg_left hBdiff (by linarith))
      _ = ∑ y ∈ S, siteOsc y f := by ring
  exact add_le_add hbound1 hbound2

omit [Fintype G.edgeSet] in
/-- **The total single-neighbour influence over a set equals the C-row sum**: summing the influence
matrix entry `C_{xy} = tanh(βJ)·[y∼x]` over `y ∈ S` gives `#(S ∩ nbr(x))·tanh(βJ)`. -/
theorem sum_isingInfluence_eq (β J : ℝ) (x : ι) (S : Finset ι) :
    ∑ y ∈ S, isingInfluence G β J x y
      = ((S ∩ G.neighborFinset x).card : ℝ) * Real.tanh (β * J) := by
  classical
  simp only [isingInfluence]
  rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]

/-- **Influence-matrix form of the general single-site comparison** (GJ §17.1): the C-propagated
term is written as the influence-matrix row sum `∑_{y∈S} C_{xy}·siteOsc x f`, the shape consumed by
the resolvent comparison. -/
theorem heatBath_agreesOff_dist_le_influence {β J : ℝ} (hβJ : 0 ≤ β * J) (h : ℝ) (x : ι)
    {S : Finset ι} {η η' : Config ι} (f : Config ι → ℝ) (hagree : agreesOff S η η') :
    |heatBath G β J h x f η - heatBath G β J h x f η'|
      ≤ (∑ y ∈ S, isingInfluence G β J x y) * siteOsc x f + ∑ y ∈ S, siteOsc y f := by
  rw [sum_isingInfluence_eq]
  exact heatBath_agreesOff_dist_le G hβJ h x f hagree

end Dobrushin

end IsingModel
