import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeIncidentEdge
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityIncidentSum

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV3g: the finite-volume bounded incident-sum `/c` bound (p.312)

The finite-volume analogue of `incident_sum_corr_fin_div_c_le_tight` (#4355): for a non-adjacent
in-box binding pair `x ≠ z`, the finite-volume c-cancelling incident sum (from #4340) divided by
`c = ⟨φ_x φ_z⟩_{σ,A}` is bounded by the **constant** `4d·(1+2^α)·e^{m⁻_FV}` — GJ p.312's genuine
bounded `2A` incident contribution, independent of `d(x,z)`.

`Finset.sum_div` + the per-edge constant bound (PR-FV3f
`incident_symmDiff_corr_fin_div_c_le_tight_finiteRegionFV`) + the incident-edge count `≤ 4d`
(`incident_edge_card_le`, #4344).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **Finite-volume bounded incident-sum `/c` bound** (GJ p.312 `2A`): for a non-adjacent in-box
binding pair `x ≠ z`, the finite-volume c-cancelling incident sum divided by
`c = ⟨φ_x φ_z⟩_{σ,A}` is bounded by `4d·(1+2^α)·e^{m⁻_FV}`.  `Finset.sum_div` + the per-edge bound
(PR-FV3f) + the incident-edge count `≤ 4d` (#4344). -/
theorem incident_sum_corr_fin_div_c_le_tight_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ} (hx : x ∈ (cubicExhaustion d).volume n)
    (hz : z ∈ (cubicExhaustion d).volume n)
    (hxz : x ≠ z) (hxz_nonadj : ¬ (IsingModel.latticeGraph d).Adj x z)
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
          * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)) := by
  classical
  set m : ℝ := finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA with hm_def
  set Cinc : ℝ := (1 + (2 : ℝ) ^ α) * Real.exp m with hCinc
  have hCinc_nn : 0 ≤ Cinc := by rw [hCinc]; positivity
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
            (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e), Cinc := by
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
        rw [hCinc, hm_def]
        exact incident_symmDiff_corr_fin_div_c_le_tight_finiteRegionFV hα hJ hβ hA hx hz hxz
          hxz_nonadj u v hadj hpred hbind
    _ = ((inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
          (fun e => (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e ∨
            (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e)).card • Cinc :=
        Finset.sum_const _
    _ = (((inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
          (fun e => (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e ∨
            (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e)).card : ℝ) * Cinc := by
        rw [nsmul_eq_mul]
    _ ≤ (4 * d : ℝ) * Cinc :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast incident_edge_card_le d n ⟨x, hx⟩ ⟨z, hz⟩)
          hCinc_nn

end Ambient
end IsingModel
