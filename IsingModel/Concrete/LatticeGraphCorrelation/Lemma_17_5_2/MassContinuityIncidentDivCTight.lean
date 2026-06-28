import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityIncidentDivC
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDenomRatio

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1l: the GJ-faithful BOUNDED incident `/c` bound (p.312)

The tight, GJ-faithful per-edge incident `/c` bound: for a non-adjacent binding pair `x ≠ z`
(`r = d(x,z) ≥ 2`) and an incident edge `{u,v}`, the c-cancelling reduced incident correlation
divided by `c = ⟨φ_x φ_z⟩` is bounded by the **constant** `(1+2^α)·e^{m⁻}` — GJ p.312's bounded
`2A`.  This corrects `incident_symmDiff_corr_fin_div_c_le` (#4343), which dropped the
per-incident-dart denominator (leaving the unbounded `(1+(m⁻r)^α)`); here it is **kept** and
bounded via `pseudoMass_denom_ratio_le` (#4353), using `d(z,v) ≥ r−1` (`v ∼ x`, triangle).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **GJ-faithful bounded per-edge incident `/c` bound** (GJ p.312 `2A`): for a non-adjacent binding
pair `x ≠ z` and an incident edge `{u,v}` of the induced cubic graph,
`corr_fin({⟨x⟩,⟨z⟩}△{u,v}) / ⟨φ_x φ_z⟩ ≤ (1+2^α)·e^{m⁻}` — a **constant** (independent of the edge
and of `d(x,z)`).  Non-adjacency gives `r = d(x,z) ≥ 2`; the reduced pair (e.g. `{z,v}`, `v∼x`) has
`d(z,v) ≥ r−1`, so the per-incident-dart ratio (#4342) has its denominator ratio bounded by `1+2^α`
(#4353 `pseudoMass_denom_ratio_le`). -/
theorem incident_symmDiff_corr_fin_div_c_le_tight {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ_pos : 0 < J) (hβ : 0 < β)
    {n : ℕ} {x z : Fin d → ℤ} (hx : x ∈ (cubicExhaustion d).volume n)
    (hz : z ∈ (cubicExhaustion d).volume n)
    (hxz : x ≠ z) (hxz_nonadj : ¬ (latticeGraph d).Adj x z)
    (u v : (↑((cubicExhaustion d).volume n) : Type _))
    (hadj : (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).Adj u v)
    (hpred : ((⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = u ∨ (⟨x, hx⟩ :
        (↑((cubicExhaustion d).volume n) : Type _)) = v) ∨
      ((⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = u ∨ (⟨z, hz⟩ :
        (↑((cubicExhaustion d).volume n) : Type _)) = v))
    (hbind : pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ)
        (symmDiff {(⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)), ⟨z, hz⟩} {u, v})
      / correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ≤ (1 + (2 : ℝ) ^ α)
          * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) := by
  classical
  set X : (↑((cubicExhaustion d).volume n) : Type _) := ⟨x, hx⟩ with hX
  set Z : (↑((cubicExhaustion d).volume n) : Type _) := ⟨z, hz⟩ with hZ
  set m : ℝ := globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) with hm_def
  have hm_nn : 0 ≤ m := by rw [hm_def]; exact globalPseudoMassDist_nonneg hα _ _
  have hXZ : X ≠ Z := by rw [hX, hZ]; simpa [Subtype.ext_iff] using hxz
  have huv : u ≠ v := hadj.ne
  set c : ℝ := correlationInfinite (latticeGraph d) (cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]; exact (correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (cubicExhaustion d) hβ (mul_pos hβ hJ_pos) x z hxz).1
  set Cinc : ℝ := (1 + (2 : ℝ) ^ α) * Real.exp m with hCinc
  -- `r = d(x,z) ≥ 2` from non-adjacency.
  have hr2 : (2 : ℝ) ≤ (latticeDistance d x z : ℝ) := by
    have h1 : 1 ≤ latticeDistance d x z :=
      Nat.one_le_iff_ne_zero.mpr (fun h => hxz ((latticeDistance_eq_zero_iff d x z).mp h))
    have hne1 : latticeDistance d x z ≠ 1 :=
      fun h => hxz_nonadj ((latticeGraph_adj_iff_latticeDistance_eq_one d x z).mpr h)
    have : 2 ≤ latticeDistance d x z := by omega
    exact_mod_cast this
  have bridge : ∀ a b : (↑((cubicExhaustion d).volume n) : Type _),
      correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
          (⟨J, 0, β⟩ : IsingParams ℝ) {a, b}
        ≤ correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {a.val, b.val} := fun a b =>
    correlation_inducedGraph_cubic_le_correlationInfinite d (⟨J, 0, β⟩ : IsingParams ℝ) n a b
  -- "keep denominator": the #4342 ratio RHS at distance `b ≥ r−1` is bounded by `Cinc`.
  have drop_tight : ∀ b : ℝ, (latticeDistance d x z : ℝ) - 1 ≤ b →
      (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * (1 / (1 + (m * b) ^ α)) * Real.exp m
        ≤ Cinc := by
    intro b hb
    rw [hCinc]
    have hratio := pseudoMass_denom_ratio_le (α := α) (m := m)
      (r := (latticeDistance d x z : ℝ)) (s := b) hm_nn hr2 hb
    calc (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * (1 / (1 + (m * b) ^ α)) * Real.exp m
        = ((1 + (m * (latticeDistance d x z : ℝ)) ^ α) / (1 + (m * b) ^ α)) * Real.exp m := by
          rw [mul_one_div]
      _ ≤ (1 + (2 : ℝ) ^ α) * Real.exp m := mul_le_mul_of_nonneg_right hratio (Real.exp_nonneg m)
  have hnotboth : ¬ ((X = u ∨ X = v) ∧ (Z = u ∨ Z = v)) := by
    rintro ⟨hXin, hZin⟩
    apply hxz_nonadj
    rcases hXin with rfl | rfl <;> rcases hZin with hZin | hZin
    · exact absurd hZin.symm hXZ
    · subst hZin; exact hadj
    · subst hZin; exact hadj.symm
    · exact absurd hZin.symm hXZ
  -- per-incident-dart `g{z,w}/c ≤ Cinc` for `w ∼ x`.
  have helper_x : ∀ w : (↑((cubicExhaustion d).volume n) : Type _),
      (latticeGraph d).Adj x w.val → z ≠ w.val →
      correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {z, w.val} / c ≤ Cinc := by
    intro w hadjxw hzw
    have hr := correlationInfinite_incident_ratio_le hα hJ_pos hβ hxz hzw hadjxw hbind
    rw [← hc_def, ← hm_def] at hr
    have htri : (latticeDistance d x z : ℝ) - 1 ≤ (latticeDistance d z w.val : ℝ) := by
      have hxw1 : latticeDistance d x w.val = 1 :=
        (latticeGraph_adj_iff_latticeDistance_eq_one d x w.val).mp hadjxw
      have htri_nat : latticeDistance d x z
          ≤ latticeDistance d x w.val + latticeDistance d w.val z :=
        latticeDistance_triangle d x w.val z
      have hcomm : latticeDistance d w.val z = latticeDistance d z w.val :=
        latticeDistance_comm d w.val z
      have hle : latticeDistance d x z ≤ 1 + latticeDistance d z w.val := by
        rw [hxw1, hcomm] at htri_nat; omega
      have : (latticeDistance d x z : ℝ) ≤ 1 + (latticeDistance d z w.val : ℝ) := by
        exact_mod_cast hle
      linarith
    exact hr.trans (drop_tight _ htri)
  -- per-incident-dart `g{x,w}/c ≤ Cinc` for `w ∼ z` (binding symmetry).
  have helper_z : ∀ w : (↑((cubicExhaustion d).volume n) : Type _),
      (latticeGraph d).Adj z w.val → x ≠ w.val →
      correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, w.val} / c ≤ Cinc := by
    intro w hadjzw hxw
    have hbind' : pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) z x
      = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
      rw [pseudoMassFromParamsAtPairDist_comm hα (cubicExhaustion d) _ z x]; exact hbind
    have hr := correlationInfinite_incident_ratio_le hα hJ_pos hβ (Ne.symm hxz) hxw hadjzw hbind'
    rw [show ({z, x} : Finset (Fin d → ℤ)) = {x, z} from Finset.pair_comm z x,
      show (latticeDistance d z x : ℝ) = (latticeDistance d x z : ℝ) from by
        rw [IsingModel.latticeDistance_comm], ← hc_def, ← hm_def] at hr
    have htri : (latticeDistance d x z : ℝ) - 1 ≤ (latticeDistance d x w.val : ℝ) := by
      have hzw1 : latticeDistance d z w.val = 1 :=
        (latticeGraph_adj_iff_latticeDistance_eq_one d z w.val).mp hadjzw
      have htri_nat : latticeDistance d x z
          ≤ latticeDistance d x w.val + latticeDistance d w.val z :=
        latticeDistance_triangle d x w.val z
      have hcomm : latticeDistance d w.val z = latticeDistance d z w.val :=
        latticeDistance_comm d w.val z
      have hle : latticeDistance d x z ≤ latticeDistance d x w.val + 1 := by
        rw [hcomm, hzw1] at htri_nat; omega
      have : (latticeDistance d x z : ℝ) ≤ (latticeDistance d x w.val : ℝ) + 1 := by
        exact_mod_cast hle
      linarith
    exact hr.trans (drop_tight _ htri)
  rcases hpred with (rfl | rfl) | (rfl | rfl)
  · have hZv : Z ≠ v := fun h => hnotboth ⟨Or.inl rfl, Or.inr h⟩
    have hXv : X ≠ v := fun h => huv h
    rw [symmDiff_pair_pair_of_ne hXZ hXv (Ne.symm hZv)]
    have hadjxv : (latticeGraph d).Adj x v.val := hadj
    have hzv' : z ≠ v.val := fun h => hZv (by rw [hZ]; exact Subtype.ext h)
    refine le_trans (div_le_div_of_nonneg_right ?_ hc_pos.le) (helper_x v hadjxv hzv')
    rw [Finset.pair_comm v Z]; exact (bridge Z v).trans_eq (by rw [hZ])
  · have hZu : Z ≠ u := fun h => hnotboth ⟨Or.inr rfl, Or.inl h⟩
    have hXu : X ≠ u := fun h => huv h.symm
    rw [Finset.pair_comm u X, symmDiff_pair_pair_of_ne hXZ hXu (Ne.symm hZu)]
    have hadjxu : (latticeGraph d).Adj x u.val := hadj.symm
    have hzu' : z ≠ u.val := fun h => hZu (by rw [hZ]; exact Subtype.ext h)
    refine le_trans (div_le_div_of_nonneg_right ?_ hc_pos.le) (helper_x u hadjxu hzu')
    rw [Finset.pair_comm u Z]; exact (bridge Z u).trans_eq (by rw [hZ])
  · have hXv : X ≠ v := fun h => hnotboth ⟨Or.inr h, Or.inl rfl⟩
    have hZv : Z ≠ v := fun h => huv h
    rw [Finset.pair_comm X Z, symmDiff_pair_pair_of_ne hXZ.symm hZv (Ne.symm hXv)]
    have hadjzv : (latticeGraph d).Adj z v.val := hadj
    have hxv' : x ≠ v.val := fun h => hXv (by rw [hX]; exact Subtype.ext h)
    refine le_trans (div_le_div_of_nonneg_right ?_ hc_pos.le) (helper_z v hadjzv hxv')
    rw [Finset.pair_comm v X]; exact (bridge X v).trans_eq (by rw [hX])
  · have hXu : X ≠ u := fun h => hnotboth ⟨Or.inl h, Or.inr rfl⟩
    have hZu : Z ≠ u := fun h => huv h.symm
    rw [Finset.pair_comm X Z, Finset.pair_comm u Z,
      symmDiff_pair_pair_of_ne hXZ.symm hZu (Ne.symm hXu)]
    have hadjzu : (latticeGraph d).Adj z u.val := hadj.symm
    have hxu' : x ≠ u.val := fun h => hXu (by rw [hX]; exact Subtype.ext h)
    refine le_trans (div_le_div_of_nonneg_right ?_ hc_pos.le) (helper_z u hadjzu hxu')
    rw [Finset.pair_comm u X]; exact (bridge X u).trans_eq (by rw [hX])

end Ambient
end IsingModel
