import IsingModel.BetaDerivative.Lebowitz
import IsingModel.Concrete.CubicExhaustion
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Tight Lebowitz bound for the cubic finite-volume β-derivative profile (Issue #2965, Phase C)

The finite-volume β-derivative profile
`F_n(β) = ∂_β ⟨σ_xσ_z⟩_{box_n}` (a finite truncated/Ursell edge sum, by
`lemma_17_5_2_finite_derivative_profile_eq_beta_edge_sum`) is bounded by the *tight*
Lebowitz two-point cross sum over the stage-`n` edges plus an `O(1)` error counting
only the edges incident to `x` or `z` (`correlation_beta_deriv_le_lebowitz_tight`).

This expresses the β-derivative profile entirely in terms of two-point correlations
— the same objects controlled by the spatial-decay machinery of the correlation
side (Phase A–B) — and is the foundational input for the β-derivative increment
analysis required by the GJ §17.5 Lemma 17.5.2 capstone.

## Main declaration

* `IsingModel.Ambient.derivative_profile_cubic_le_lebowitz_tight`.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- **Tight Lebowitz bound for the cubic β-derivative profile** (Issue #2965,
Phase C): for `0 ≤ J`, `0 < β`, distinct sites `x ≠ z` with
`{x,z} ⊆ (cubicExhaustion d).volume n`, the β-derivative of the finite-volume
two-point profile is bounded by `J` times the tight Lebowitz two-point cross sum
over the stage-`n` edges, plus `J` times the count of edges incident to `⟨x⟩` or
`⟨z⟩`:
`∂_β c_n ≤ J·∑_{⟨u,v⟩∈E}[⟨σ_xσ_u⟩⟨σ_zσ_v⟩ + ⟨σ_xσ_v⟩⟨σ_zσ_u⟩] + J·|incident|`.
The error term counts only incident edges (`O(1)` in `n`), and the cross sum is the
two-point object governed by the Phase A–B spatial decay. Wraps
`correlation_beta_deriv_le_lebowitz_tight` applied to the induced lattice graph,
identifying the profile with the induced-graph correlation via
`correlationAlongExhaustion_of_subset` and `liftFinset_pair`. -/
theorem derivative_profile_cubic_le_lebowitz_tight (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J)
    (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) {n : ℕ}
    (hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n) :
    deriv (fun β' => correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β
      ≤ J * ∑ e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset,
          Sym2.lift ⟨fun u v =>
              correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {⟨x, hsub (Finset.mem_insert_self x {z})⟩, u} *
                correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {⟨z, hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))⟩, v} +
              correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {⟨x, hsub (Finset.mem_insert_self x {z})⟩, v} *
                correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {⟨z, hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))⟩, u},
            fun u v => by ring⟩ e
        + J * ((inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
            (fun e => (⟨x, hsub (Finset.mem_insert_self x {z})⟩ :
                (↑((cubicExhaustion d).volume n) : Type _)) ∈ e ∨
              (⟨z, hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))⟩ :
                (↑((cubicExhaustion d).volume n) : Type _)) ∈ e)).card := by
  have hx : x ∈ (cubicExhaustion d).volume n := hsub (Finset.mem_insert_self x {z})
  have hz : z ∈ (cubicExhaustion d).volume n :=
    hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
  have hrs : (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ≠ ⟨z, hz⟩ := by
    simpa [Subtype.ext_iff] using hxz
  -- The profile equals the induced-graph correlation of the lifted pair.
  have hfun : (fun β' => correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n)
      = (fun β' => correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
          (⟨J, 0, β'⟩ : IsingParams ℝ) {⟨x, hx⟩, ⟨z, hz⟩}) := by
    funext β'
    rw [correlationAlongExhaustion_of_subset (latticeGraph d) (cubicExhaustion d) _ hsub,
      correlationΛ_apply, liftFinset_pair hsub hx hz]
  obtain ⟨dval, hd, hbound⟩ :=
    correlation_beta_deriv_le_lebowitz_tight
      (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)) J β hJ hβ ⟨x, hx⟩ ⟨z, hz⟩ hrs
  rw [hfun, hd.deriv]
  exact hbound

end Ambient
end IsingModel
