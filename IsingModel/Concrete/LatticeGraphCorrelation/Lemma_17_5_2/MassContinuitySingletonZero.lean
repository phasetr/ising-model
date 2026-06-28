import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExBasicCorrelation
import IsingModel.AmbientLattice.CorrelationInfinite.Basic

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1i prerequisite: zero-field single-site vanishing

In the c-cancelling Lebowitz cross-sum (#4341
`derivative_profile_cubic_le_infiniteVolume_lebowitz_cancelling`), converting the edge `Sym2`-sum to
a dart sum (`sum_edgeFinset_sym2_lift_prod_eq_sum_dart`) produces *degenerate* darts whose endpoint
coincides with the binding site, e.g. `g{x,⟨x⟩.val} = correlationInfinite {x, x}`.  Since
`{x, x} = {x}` is a singleton, this is the single-site magnetization, which **vanishes at zero
external field** `h = 0` by the `ℤ₂` spin-flip symmetry.

This module supplies that vanishing for the infinite-volume two-point function: each finite
stage has zero single-site correlation (the `_at_singleton_eq_zero_le_one` lemma), so the limit
(`tendsto_correlationAlongExhaustion_correlationInfinite`) is zero.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

/-- **Zero-field single-site vanishing (infinite volume).**  At zero external field, the
infinite-volume single-site correlation `⟨φ_i⟩ = correlationInfinite … {i}` is zero (`ℤ₂` spin-flip
symmetry).  Every exhaustion stage has `correlationAlongExhaustion … {i} n = 0` (the
`_at_singleton_eq_zero_le_one` lemma), so the limit is zero
(`tendsto_correlationAlongExhaustion_correlationInfinite` + uniqueness of limits). -/
theorem correlationInfinite_latticeGraph_singleton_zero_field
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ)) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (i : Fin d → ℤ) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) = 0 := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have htend := Ambient.tendsto_correlationAlongExhaustion_correlationInfinite
    (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf ({i} : Finset (Fin d → ℤ))
  have hzero : ∀ n, Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 := fun n =>
    (correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton_eq_zero_le_one
      d Λ J β i n).1
  exact tendsto_nhds_unique (Filter.Tendsto.congr hzero htend) tendsto_const_nhds

end Ambient
end IsingModel
