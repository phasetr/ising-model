import IsingModel.Peierls.PeierlsPlusGibbs
import IsingModel.Peierls.LowTempTail

/-!
# The down-spin probability vanishes at low temperature (FV §3.7.2)

For a fixed box `Λ` whose filled connected droplets are all neighbour-closed, dual-support-bounded,
and single boundary-dart orbits, the `+`-boundary probability of `σ_i = -1` tends to `0` as
`β → ∞`. This squeezes the finite-volume Peierls bound `μ⁺_Λ(σ_i = -1) ≤ 32 q / (1 - 32 q)` between
`0` and the vanishing geometric tail, the analytic core of `m*(β) > 0`.

* `plusGibbsExpectation_nonneg` — the `+`-expectation of a nonnegative observable is nonnegative.
* `peierls_plusGibbs_tendsto_zero` — `μ⁺_Λ(σ_i = -1) → 0` as `β → ∞`.

The single-orbit (discrete Jordan) input enters only through `hone`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, (3.49), pp. 109–116.
-/

namespace IsingModel

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedDecidableInType false in
/-- **The `+`-expectation of a nonnegative observable is nonnegative**. -/
theorem plusGibbsExpectation_nonneg (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (p : IsingParams ℝ) (B : Finset ι) (F : Config ι → ℝ) (hF : ∀ σ, 0 ≤ F σ) :
    0 ≤ plusGibbsExpectation G p B F := by
  rw [plusGibbsExpectation]
  refine mul_nonneg (inv_nonneg.mpr (plusPartitionFunction_pos' G p B).le) ?_
  exact Finset.sum_nonneg fun σ _ => mul_nonneg (hF σ) (boltzmannWeight_pos G p σ).le

open scoped Classical in
/-- **The finite-volume down-spin probability vanishes at low temperature**. -/
theorem peierls_plusGibbs_tendsto_zero {Λ Λd : Finset (Fin 2 → ℤ)}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (B : Finset ↑Λ) (i g : ↑Λ)
    (hBconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) B) (hgB : g ∈ B)
    (hdual : ∀ S ∈ Finset.univ.filter (fun S : Finset ↑Λ =>
        i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S ∧
          IsFilled (Ambient.inducedGraph (latticeGraph 2) Λ) g S),
      dualSupport (S.image Subtype.val) ⊆ Λd)
    (hne : ∀ S ∈ Finset.univ.filter (fun S : Finset ↑Λ =>
        i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S ∧
          IsFilled (Ambient.inducedGraph (latticeGraph 2) Λ) g S),
      NeighbourClosed Λ S)
    (hone : ∀ S ∈ Finset.univ.filter (fun S : Finset ↑Λ =>
        i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S ∧
          IsFilled (Ambient.inducedGraph (latticeGraph 2) Λ) g S),
      ∀ d e : BoundaryDart (S.image Subtype.val), d.SameOrbit e)
    (J : ℝ) (hJ : 0 < J) :
    Tendsto (fun β : ℝ => plusGibbsExpectation (Ambient.inducedGraph (latticeGraph 2) Λ) ⟨J, 0, β⟩ B
        (fun σ => if σ i = Spin.down then 1 else 0)) atTop (𝓝 0) := by
  have hrate : Tendsto (fun β : ℝ => 32 * Real.exp (-2 * β * J)) atTop (𝓝 0) := by
    have := lowTempRate_tendsto_zero 32 J hJ
    refine this.congr (fun β => ?_)
    ring_nf
  refine squeeze_zero' (g := fun β => 32 * Real.exp (-2 * β * J)
      * (1 - 32 * Real.exp (-2 * β * J))⁻¹) ?_ ?_ ?_
  · -- `0 ≤ μ⁺`
    filter_upwards with β
    exact plusGibbsExpectation_nonneg _ _ B _
      (fun σ => by by_cases h : σ i = Spin.down <;> simp [h])
  · -- eventually `μ⁺ ≤ 32 q (1 - 32 q)⁻¹`
    filter_upwards [hrate.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with β h32
    have hr0 : 0 < 32 * Real.exp (-2 * β * J) := by positivity
    have := peierls_plusGibbs_le hpre J β B i g hBconn hgB hdual hne hone hr0 h32
    rwa [div_eq_mul_inv] at this
  · -- `32 q (1 - 32 q)⁻¹ → 0`
    have := peierls_low_temp_tail_tendsto_zero 32 J hJ
    refine this.congr (fun β => ?_)
    ring_nf

end IsingModel
