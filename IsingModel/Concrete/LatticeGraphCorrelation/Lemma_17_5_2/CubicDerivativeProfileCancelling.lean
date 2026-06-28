import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CubicDerivativeProfileLebowitz
import IsingModel.BetaDerivative.LebowitzCancelling

/-!
# c-cancelling tight Lebowitz bound for the cubic finite-volume β-derivative profile (GJ §17.5)

The c-cancelling counterpart of `derivative_profile_cubic_le_lebowitz_tight`: the finite-volume
β-derivative profile is bounded by the tight Lebowitz two-point cross sum over the stage-`n` edges
plus the **c-cancelling** incident error — the incident (degenerate) edges contribute the *reduced*
correlation `corr({⟨x⟩,⟨z⟩}△{e})` instead of the coarse `1` per edge.  This is GJ's bounded `2A`
mechanism (p.312): dividing the reduced incident correlation by `c = ⟨σ_x σ_z⟩` stays bounded,
whereas dividing the loose incident *count* by `c` blows up.

## Main declaration

* `IsingModel.Ambient.derivative_profile_cubic_le_lebowitz_cancelling`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- **c-cancelling tight Lebowitz bound for the cubic β-derivative profile** (GJ §17.5, p.312):
for `0 ≤ J`, `0 < β`, distinct sites `x ≠ z` with `{x,z} ⊆ (cubicExhaustion d).volume n`, the
β-derivative of the finite-volume two-point profile is bounded by `J` times the tight Lebowitz
two-point cross sum over the stage-`n` edges, plus `J` times the sum of the *reduced* correlations
`corr({⟨x⟩,⟨z⟩}△{e})` over the edges incident to `⟨x⟩` or `⟨z⟩`:
`∂_β c_n ≤ J·∑_{⟨u,v⟩∈E}[⟨σ_xσ_u⟩⟨σ_zσ_v⟩ + ⟨σ_xσ_v⟩⟨σ_zσ_u⟩]`
`+ J·∑_{e incident} corr({⟨x⟩,⟨z⟩}△{e})`.
Wraps `correlation_beta_deriv_le_lebowitz_cancelling` applied to the induced lattice graph,
identifying the profile with the induced-graph correlation via
`correlationAlongExhaustion_of_subset` and `liftFinset_pair`. -/
theorem derivative_profile_cubic_le_lebowitz_cancelling (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J)
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
        + J * ∑ e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
            (fun e => (⟨x, hsub (Finset.mem_insert_self x {z})⟩ :
                (↑((cubicExhaustion d).volume n) : Type _)) ∈ e ∨
              (⟨z, hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))⟩ :
                (↑((cubicExhaustion d).volume n) : Type _)) ∈ e),
          Sym2.lift ⟨fun u v =>
              correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ)
                (symmDiff {⟨x, hsub (Finset.mem_insert_self x {z})⟩,
                    ⟨z, hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))⟩} {u, v}),
            fun u v => by simp only [Finset.pair_comm u v]⟩ e := by
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
    correlation_beta_deriv_le_lebowitz_cancelling
      (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)) J β hJ hβ ⟨x, hx⟩ ⟨z, hz⟩ hrs
  rw [hfun, hd.deriv]
  exact hbound

end Ambient
end IsingModel
