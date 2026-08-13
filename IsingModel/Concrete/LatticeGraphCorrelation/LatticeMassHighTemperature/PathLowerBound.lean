import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.JLowerBound

/-!
# Lattice mass at high temperature split — Step 114 path lower bound on the two-point function

Part of the split high-temperature lattice-mass layer (Issue #1850).
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## §17.5 Path lower bound on the two-point function (Step 114) -/

/-- From `latticeDistance d 0 r = n + 1`, find a lattice neighbor of `r` that
is one step closer to `0`.

Proof: since the ℓ¹ sum is n + 1 ≥ 1, some coordinate `i₀` has `|r i₀| ≥ 1`.
Move `r i₀` one step toward 0 to get `v = r[i₀ ↦ r i₀ ∓ 1]`. -/
private lemma exists_latticeDistance_succ_adj
    (d : ℕ) (r : Fin d → ℤ) (n : ℕ)
    (hn : IsingModel.latticeDistance d 0 r = n + 1) :
    ∃ v : Fin d → ℤ, (IsingModel.latticeGraph d).Adj v r ∧
      IsingModel.latticeDistance d 0 v = n := by
  have hsum : ∑ i : Fin d, (r i).natAbs = n + 1 := by
    unfold IsingModel.latticeDistance at hn; simpa [Pi.zero_apply] using hn
  have hne : ∑ i : Fin d, (r i).natAbs ≠ 0 := by omega
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hri₀ : r i₀ ≠ 0 := fun h => by simp [h] at hi₀
  -- erase decomposition
  have h_rest : ∑ i ∈ Finset.univ.erase i₀, (r i).natAbs = n + 1 - (r i₀).natAbs := by
    have h : ∑ i ∈ Finset.univ.erase i₀, (r i).natAbs + (r i₀).natAbs = n + 1 :=
      (Finset.sum_erase_add Finset.univ (fun i => (r i).natAbs) (Finset.mem_univ i₀)).trans hsum
    omega
  -- adjacency: ∑ (update i - r i).natAbs = (x - r i₀).natAbs
  have h_adj_sum : ∀ (x : ℤ),
      ∑ i : Fin d, (Function.update r i₀ x i - r i).natAbs = (x - r i₀).natAbs := by
    intro x
    have heq : ∑ i : Fin d, (Function.update r i₀ x i - r i).natAbs
        = (Function.update r i₀ x i₀ - r i₀).natAbs :=
      Finset.sum_eq_single i₀
        (fun j _ hj => by simp [Function.update_of_ne hj])
        (fun h => absurd (Finset.mem_univ i₀) h)
    simp [heq]
  -- distance: ∑ (0 - update i).natAbs = x.natAbs + ∑ erase
  have h_dist_sum : ∀ (x : ℤ),
      ∑ i : Fin d, (0 - Function.update r i₀ x i).natAbs
        = x.natAbs + ∑ i ∈ Finset.univ.erase i₀, (r i).natAbs := by
    intro x
    rw [show ∑ i : Fin d, (0 - Function.update r i₀ x i).natAbs
        = ∑ i ∈ insert i₀ (Finset.univ.erase i₀), (0 - Function.update r i₀ x i).natAbs from by
      rw [Finset.insert_erase (Finset.mem_univ i₀)]]
    rw [Finset.sum_insert (Finset.notMem_erase i₀ Finset.univ)]
    simp only [Function.update_apply, zero_sub, Int.natAbs_neg]
    congr 1
    apply Finset.sum_congr rfl; intro j hj
    simp only [if_neg (Finset.mem_erase.mp hj).1]
  -- sum bound: (r i₀).natAbs ≤ n + 1
  have h_bound : (r i₀).natAbs ≤ n + 1 :=
    (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ i₀)).trans_eq hsum
  rcases lt_or_gt_of_ne hri₀ with h_neg | h_pos
  · -- r i₀ < 0: step v i₀ = r i₀ + 1
    refine ⟨Function.update r i₀ (r i₀ + 1), ?_, ?_⟩
    · rw [IsingModel.latticeGraph_adj_iff_latticeDistance_eq_one]
      unfold IsingModel.latticeDistance; rw [h_adj_sum]; norm_num
    · have : IsingModel.latticeDistance d 0 (Function.update r i₀ (r i₀ + 1))
          = (r i₀ + 1).natAbs + ∑ i ∈ Finset.univ.erase i₀, (r i).natAbs := by
        unfold IsingModel.latticeDistance; simpa [Pi.zero_apply] using h_dist_sum (r i₀ + 1)
      rw [this, h_rest]; omega
  · -- r i₀ > 0: step v i₀ = r i₀ - 1
    refine ⟨Function.update r i₀ (r i₀ - 1), ?_, ?_⟩
    · rw [IsingModel.latticeGraph_adj_iff_latticeDistance_eq_one]
      unfold IsingModel.latticeDistance; rw [h_adj_sum]; norm_num
    · have : IsingModel.latticeDistance d 0 (Function.update r i₀ (r i₀ - 1))
          = (r i₀ - 1).natAbs + ∑ i ∈ Finset.univ.erase i₀, (r i).natAbs := by
        unfold IsingModel.latticeDistance; simpa [Pi.zero_apply] using h_dist_sum (r i₀ - 1)
      rw [this, h_rest]; omega


/-- **Path lower bound on the two-point function** (GJ §17.1 pp. 304–306):
for any `r ≠ 0` in ℤ^d, ferromagnetic `J ≥ 0`, `β > 0`, `h = 0`:

`tanh(β J)^(latticeDistance d 0 r) ≤ twoPointFunction d ⟨J, 0, β⟩ r`.

Proof: strong induction on `n = latticeDistance d 0 r`.
- Base (`n = 0`): contradicts `r ≠ 0`.
- Step `n + 1`: `exists_latticeDistance_succ_adj` gives `v` with `Adj v r` and `dist 0 v = n`.
  If `n = 0`, then `v = 0` so `Adj 0 r`, and `twoPointFunction_ge_tanh_betaJ_of_adj` applies.
  If `n ≥ 1`, then `v ≠ 0`; apply IH to get `tanh^n ≤ twoPointFunction v`.
  By translation invariance, `correlationInfinite ... {v, r} = twoPointFunction (r−v)`,
  and since `Adj 0 (r−v)`, Step 113 gives `tanh ≤ twoPointFunction (r−v)`.
  GKS-II: `twoPointFunction v * correlationInfinite ... {v, r} ≤ twoPointFunction r`
  (via `{0,v} ∆ {v,r} = {0,r}`), so `tanh^{n+1} ≤ twoPointFunction r`.

Reference: Glimm–Jaffe §17.1 pp. 304–306 (2nd ed.); §4.2 (GKS-II subgraph monotonicity). -/
theorem twoPointFunction_ge_tanh_betaJ_pow_dist
    {d : ℕ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {r : Fin d → ℤ} (hr : r ≠ 0) :
    Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 r ≤
    twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) r := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hβ.le hJ)) (Real.cosh_pos _).le
  -- Helper: adjacent pair gives tanh lower bound on correlationInfinite
  have h_adj_ge : ∀ (u w : Fin d → ℤ), (IsingModel.latticeGraph d).Adj u w →
      Real.tanh (β * J) ≤ correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {u, w} := by
    intro u w huw
    -- Translate by -u: correlationInfinite {u, w} = correlationInfinite {0, w - u}
    have htrans : correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {u, w}
        = twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) (w - u) := by
      rw [twoPointFunction_apply]
      rw [← correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset d (-u)
            (⟨J, 0, β⟩ : IsingParams ℝ) hf]
      congr 1
      unfold vaddFinset
      rw [Finset.image_insert, Finset.image_singleton]
      simp only [vadd_eq_add, neg_add_cancel]
      congr 1; ext i; ring_nf
    -- latticeDistance d 0 (w - u) = latticeDistance d u w = 1
    have h_adj_0 : (IsingModel.latticeGraph d).Adj 0 (w - u) := by
      rw [IsingModel.latticeGraph_adj_iff_latticeDistance_eq_one]
      have huw' : IsingModel.latticeDistance d u w = 1 :=
        (IsingModel.latticeGraph_adj_iff_latticeDistance_eq_one d u w).mp huw
      unfold IsingModel.latticeDistance at huw' ⊢
      simp only [Pi.zero_apply, Pi.sub_apply, zero_sub, Int.natAbs_neg] at huw' ⊢
      calc ∑ i : Fin d, (w i - u i).natAbs
          = ∑ i : Fin d, (u i - w i).natAbs :=
            Finset.sum_congr rfl fun i _ => by
              rw [show (w i - u i : ℤ) = -(u i - w i) from by ring]
              exact Int.natAbs_neg _
        _ = 1 := huw'
    rw [htrans]
    exact twoPointFunction_ge_tanh_betaJ_of_adj hJ hβ h_adj_0
  -- Strong induction on n = latticeDistance d 0 r
  suffices h : ∀ (n : ℕ) (s : Fin d → ℤ),
      IsingModel.latticeDistance d 0 s = n → s ≠ 0 →
      Real.tanh (β * J) ^ n ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) s from
    h _ r rfl hr
  intro n
  induction n with
  | zero =>
    intro s h0 hs0
    exact absurd ((IsingModel.latticeDistance_eq_zero_iff d 0 s).mp h0).symm hs0
  | succ n ih =>
    intro s hn hs0
    obtain ⟨v, hv_adj, hv_dist⟩ := exists_latticeDistance_succ_adj d s n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · -- n = 0: v = 0, Adj 0 s, use Step 113 directly
      have hv0 : v = 0 := ((IsingModel.latticeDistance_eq_zero_iff d 0 v).mp hv_dist).symm
      subst hv0
      simpa using twoPointFunction_ge_tanh_betaJ_of_adj hJ hβ hv_adj
    · -- n ≥ 1: v ≠ 0, use IH + GKS-II
      have hv_ne : v ≠ 0 := by
        intro heq; simp [heq, IsingModel.latticeDistance] at hv_dist; omega
      -- IH
      have ih_v : Real.tanh (β * J) ^ n ≤
          twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) v := ih v hv_dist hv_ne
      -- tanh ≤ correlationInfinite {v, s}
      have h_corr_vs : Real.tanh (β * J) ≤ correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {v, s} :=
        h_adj_ge v s hv_adj
      -- nonnegativity
      have hv_nn : 0 ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) v :=
        (pow_nonneg htanh_nn n).trans ih_v
      have hcorr_nn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {v, s} :=
        htanh_nn.trans h_corr_vs
      -- Symmetric difference {0, v} ∆ {v, s} = {0, s}
      have h0v : (0 : Fin d → ℤ) ≠ v := Ne.symm hv_ne
      have hvs : v ≠ s := hv_adj.ne
      have h0s : (0 : Fin d → ℤ) ≠ s := Ne.symm hs0
      have hsdiff : ({(0 : Fin d → ℤ), v} : Finset _) ∆ {v, s} = {0, s} := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (⟨rfl | rfl, h2⟩ | ⟨rfl | rfl, h2⟩)
          · exact Or.inl rfl
          · exact absurd (Or.inl rfl) h2
          · exact absurd (Or.inr rfl) h2
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact Or.inl ⟨Or.inl rfl, fun h => h.elim (h0v ·) (h0s ·)⟩
          · exact Or.inr ⟨Or.inr rfl, fun h => h.elim hs0 (fun hv => hvs hv.symm)⟩
      -- GKS-II: twoPointFunction v * correlationInfinite {v, s} ≤ twoPointFunction s
      have hgks : twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) v *
          correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {v, s}
          ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) s :=
        calc twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) v *
              correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {v, s}
            = correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {0, v} *
              correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {v, s} := by
                  rw [twoPointFunction_apply]
          _ ≤ correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) ({(0 : Fin d → ℤ), v} ∆ {v, s}) :=
                  correlationInfinite_latticeGraph_cubicExhaustion_gks_second d _ hf {0, v} {v, s}
          _ = twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) s := by
                  rw [hsdiff, twoPointFunction_apply]
      calc Real.tanh (β * J) ^ (n + 1)
          = Real.tanh (β * J) ^ n * Real.tanh (β * J) := pow_succ _ _
        _ ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) v *
              correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {v, s} :=
              mul_le_mul ih_v h_corr_vs htanh_nn hv_nn
        _ ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) s := hgks


end Ambient
end IsingModel
