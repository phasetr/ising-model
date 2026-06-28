import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityIncidentDivC
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1h: the incident-sum `/c` bound (p.312)

Summing the per-edge incident `/c` uniform bound (#4343) over the incident edges of the induced
cubic graph: since each incident summand `corr_fin({⟨x⟩,⟨z⟩}△{e})/c` is bounded by the GJ p.312
constant `(1+(m⁻·d(x,z))^α)·e^{m⁻}`, and the incident edges number at most `deg(⟨x⟩)+deg(⟨z⟩) ≤ 4d`
(lattice degree `≤ 2d`, `inducedLatticeGraph_degree_le`), the whole incident-sum divided by
`c = ⟨φ_x φ_z⟩` is bounded by `4d·(1+(m⁻·d(x,z))^α)·e^{m⁻}` — uniform in the exhaustion stage.

This module supplies:

* `incident_edge_card_le` — the incident-edge count bound `≤ 4d`;
* `incident_sum_corr_fin_div_c_le` — the incident-sum `/c` bound.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **Incident-edge count bound** (lattice degree `≤ 2d`): the number of edges of the induced cubic
graph incident to `⟨x⟩` or `⟨z⟩` is at most `4d = deg(⟨x⟩)+deg(⟨z⟩)`.  The incident filter splits
as a union of the two incidence finsets, whose cardinalities are the degrees
(`card_incidenceFinset_eq_degree`), each `≤ 2d` (`inducedLatticeGraph_degree_le`). -/
theorem incident_edge_card_le (d n : ℕ)
    (X Z : (↑((cubicExhaustion d).volume n) : Type _)) :
    ((inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
        (fun e => X ∈ e ∨ Z ∈ e)).card ≤ 4 * d := by
  classical
  rw [Finset.filter_or]
  refine (Finset.card_union_le _ _).trans ?_
  rw [← SimpleGraph.incidenceFinset_eq_filter, ← SimpleGraph.incidenceFinset_eq_filter,
    SimpleGraph.card_incidenceFinset_eq_degree, SimpleGraph.card_incidenceFinset_eq_degree]
  have hX := inducedLatticeGraph_degree_le d ((cubicExhaustion d).volume n) X
  have hZ := inducedLatticeGraph_degree_le d ((cubicExhaustion d).volume n) Z
  omega

/-- **Incident-sum `/c` bound** (GJ p.312): for a non-adjacent binding pair `x ≠ z`
(`m⁻(x,z) = globalPseudoMassDist`), the c-cancelling incident sum (from
`derivative_profile_cubic_le_lebowitz_cancelling`, #4340) divided by `c = ⟨φ_x φ_z⟩` is bounded by
`4d·(1+(m⁻·d(x,z))^α)·e^{m⁻}`:
`(∑_{e incident} corr_fin({⟨x⟩,⟨z⟩}△{e})) / ⟨φ_x φ_z⟩ ≤ 4d·(1+(m⁻·d(x,z))^α)·e^{m⁻}`.

Distributes `/c` over the sum (`Finset.sum_div`), bounds each incident term by the per-edge uniform
constant (#4343 `incident_symmDiff_corr_fin_div_c_le`), and counts the incident edges
(`incident_edge_card_le`, `≤ 4d`). -/
theorem incident_sum_corr_fin_div_c_le {α d : ℕ} (hα : 1 ≤ α)
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
      ≤ (4 * d : ℝ) * ((1 + (globalPseudoMassDist hα (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d x z : ℝ)) ^ α)
          * Real.exp (globalPseudoMassDist hα (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ))) := by
  classical
  set m : ℝ := globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) with hm_def
  have hm_nn : 0 ≤ m := by rw [hm_def]; exact globalPseudoMassDist_nonneg hα _ _
  set Cinc : ℝ := (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * Real.exp m with hCinc
  have hCinc_nn : 0 ≤ Cinc := by
    rw [hCinc]; positivity
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
        exact incident_symmDiff_corr_fin_div_c_le hα hJ_pos hβ hx hz hxz hxz_nonadj u v hadj hpred
          hbind
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
