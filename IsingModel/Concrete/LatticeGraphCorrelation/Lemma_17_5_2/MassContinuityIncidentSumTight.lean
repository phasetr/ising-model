import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityIncidentDivCTight
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityIncidentSum

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1m: the GJ-faithful BOUNDED incident-sum `/c` bound (p.312)

Sums the GJ-faithful per-edge incident `/c` bound (#4354, the bounded `2A`) over the incident edges:
for a non-adjacent binding pair `x ≠ z`, the c-cancelling incident sum divided by `c = ⟨φ_x φ_z⟩` is
bounded by the **constant** `4d·(1+2^α)·e^{m⁻}` — independent of `d(x,z)`.  This replaces the loose
`4d·(1+(m⁻r)^α)·e^{m⁻}` of #4344 with GJ p.312's genuine bounded incident contribution.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **GJ-faithful bounded incident-sum `/c` bound** (GJ p.312 `2A`): for a non-adjacent binding pair
`x ≠ z`, the c-cancelling incident sum (from #4340) divided by `c = ⟨φ_x φ_z⟩` is bounded by the
**constant** `4d·(1+2^α)·e^{m⁻}`.  `Finset.sum_div` + the per-edge constant bound #4354
(`incident_symmDiff_corr_fin_div_c_le_tight`) + the incident-edge count `≤ 4d`
(`incident_edge_card_le`). -/
theorem incident_sum_corr_fin_div_c_le_tight {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ_pos : 0 < J) (hβ : 0 < β)
    {n : ℕ} {x z : Fin d → ℤ} (hx : x ∈ (cubicExhaustion d).volume n)
    (hz : z ∈ (cubicExhaustion d).volume n)
    (hxz : x ≠ z) (hxz_nonadj : ¬ (latticeGraph d).Adj x z)
    (hbind : pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    (∑ e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
        (fun e => (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e ∨
          (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e),
        Sym2.lift ⟨fun u v =>
            correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
              (⟨J, 0, β⟩ : IsingParams ℝ)
              (symmDiff {(⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)), ⟨z, hz⟩} {u, v}),
          fun u v => by simp only [Finset.pair_comm u v]⟩ e)
      / correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ≤ (4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
          * Real.exp (globalPseudoMassDist hα (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ))) := by
  classical
  set m : ℝ := globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) with hm_def
  set Cinc : ℝ := (1 + (2 : ℝ) ^ α) * Real.exp m with hCinc
  have hCinc_nn : 0 ≤ Cinc := by rw [hCinc]; positivity
  rw [Finset.sum_div]
  calc ∑ e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
          (fun e => (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e ∨
            (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ∈ e),
          (Sym2.lift ⟨fun u v =>
              correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ)
                (symmDiff {(⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)), ⟨z, hz⟩} {u, v}),
            fun u v => by simp only [Finset.pair_comm u v]⟩ e
            / correlationInfinite (latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
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
        exact incident_symmDiff_corr_fin_div_c_le_tight hα hJ_pos hβ hx hz hxz hxz_nonadj
          u v hadj hpred hbind
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
