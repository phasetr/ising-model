import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeIncidentEdge
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityIncidentSum

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV3g: the finite-volume bounded incident-sum `/c` bound (p.312)

The finite-volume analogue of `incident_sum_corr_fin_div_c_le_tight` (#4355): for an in-box binding
pair `x ≠ z` (**adjacent or not**), the finite-volume c-cancelling incident sum (from #4340) divided
by `c = ⟨φ_x φ_z⟩_{σ,A}` is bounded by the **constant**
`4d·((1+2^α)·e^{m⁻_FV} + (1+(m⁻_FV)^α)·e^{m⁻_FV}/2)` — GJ p.312's bounded `2A` incident
contribution, independent of `d(x,z)`.  The per-edge bound (PR-FV3f) is now adjacency-general (it
includes the self-edge `1/c` term `(1+(m⁻_FV)^α)e^{m⁻_FV}/2` for the case `x ∼ z`), so a single
uniform per-edge constant `Cedge` covers every incident edge, including the self-edge.

`Finset.sum_div` + the per-edge constant bound (PR-FV3f
`incident_symmDiff_corr_fin_div_c_le_tight_finiteRegionFV`) + the incident-edge count `≤ 4d`
(`incident_edge_card_le`, #4344).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **Finite-volume bounded incident-sum `/c` bound** (GJ p.312 `2A`): for an in-box binding pair
`x ≠ z` (adjacent or not), the finite-volume c-cancelling incident sum divided by
`c = ⟨φ_x φ_z⟩_{σ,A}` is bounded by `4d·((1+2^α)·e^{m⁻_FV} + (1+(m⁻_FV)^α)·e^{m⁻_FV}/2)`.
`Finset.sum_div` + the adjacency-general per-edge bound (PR-FV3f) + the incident-edge count `≤ 4d`
(#4344). -/
theorem incident_sum_corr_fin_div_c_le_tight_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ} (hx : x ∈ (cubicExhaustion d).volume n)
    (hz : z ∈ (cubicExhaustion d).volume n)
    (hxz : x ≠ z)
    (hbind : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z
      = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) :
    (∑ e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
        (fun e => (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e ∨
          (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e),
        Sym2.lift ⟨fun u v =>
            correlation (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
              (⟨J, 0, β⟩ : IsingParams ℝ)
              (symmDiff {(⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)), ⟨z, hz⟩} {u, v}),
          fun u v => by simp only [Finset.pair_comm u v]⟩ e)
      / Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
      ≤ (4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
          * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
        + (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) ^ α)
          * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) / 2) := by
  classical
  set m : ℝ := finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA with hm_def
  have hm_nn : 0 ≤ m := by rw [hm_def]; exact (finiteRegionPseudoMassDistFV_pos hα hJ hβ hA).le
  set Cedge : ℝ := (1 + (2 : ℝ) ^ α) * Real.exp m + (1 + m ^ α) * Real.exp m / 2 with hCedge
  have hCedge_nn : 0 ≤ Cedge := by
    rw [hCedge]
    have : (0 : ℝ) ≤ m ^ α := pow_nonneg hm_nn α
    have h1 : (0 : ℝ) ≤ (1 + (2 : ℝ) ^ α) * Real.exp m :=
      mul_nonneg (by positivity) (Real.exp_nonneg _)
    have h2 : (0 : ℝ) ≤ (1 + m ^ α) * Real.exp m / 2 :=
      div_nonneg (mul_nonneg (by linarith) (Real.exp_nonneg _)) (by norm_num)
    linarith
  rw [Finset.sum_div]
  calc ∑ e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
          (fun e => (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e ∨
            (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e),
          (Sym2.lift ⟨fun u v =>
              correlation (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ)
                (symmDiff {(⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)), ⟨z, hz⟩} {u, v}),
            fun u v => by simp only [Finset.pair_comm u v]⟩ e)
            / Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
      ≤ ∑ _e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
          (fun e => (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e ∨
            (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e), Cedge := by
        refine Finset.sum_le_sum (fun e he => ?_)
        rw [Finset.mem_filter] at he
        obtain ⟨heE, hpred_s⟩ := he
        obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
        simp only [Sym2.lift_mk]
        have hadj : (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).Adj u v :=
          SimpleGraph.mem_edgeFinset.mp heE
        have hpred : ((⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = u ∨
              (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = v) ∨
            ((⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = u ∨
              (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = v) := by
          rcases hpred_s with h | h
          · exact Or.inl (Sym2.mem_iff.mp h)
          · exact Or.inr (Sym2.mem_iff.mp h)
        rw [hCedge, hm_def]
        exact incident_symmDiff_corr_fin_div_c_le_tight_finiteRegionFV hα hJ hβ hA hx hz hxz
          u v hadj hpred hbind
    _ = ((inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
          (fun e => (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e ∨
            (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e)).card • Cedge :=
        Finset.sum_const _
    _ = (((inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
          (fun e => (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e ∨
            (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e)).card : ℝ) * Cedge := by
        rw [nsmul_eq_mul]
    _ ≤ (4 * d : ℝ) * Cedge :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast incident_edge_card_le d n ⟨x, hx⟩ ⟨z, hz⟩)
          hCedge_nn

end Ambient
end IsingModel
