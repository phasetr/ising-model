import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromSimonLieb

/-!
# GJ §17.5/§18 Theorem 17.5.1 — directional abscissa upper bound for the true mass

The all-directions generalization of the on-axis abscissa upper bound
(`latticeMass_le_ofReal_liminf_onAxisRate`, #4389): for **any** nonzero lattice direction `v`,

`latticeMass(σ) ≤ ofReal(liminf_k τ_v(k))`, `τ_v(k) = −log⟨φ₀ φ_{(k+1)v}⟩_∞/((k+1)·d(0,v))`,

the per-distance decay rate along the ray `ℕ·v`.  Since the true mass `m(σ)` is the infimum over
directions of the directional inverse correlation length, this per-direction family of upper bounds
is the **upper half of the abscissa characterization** of the true mass (the matching lower bound /
sharpness is the Ornstein–Zernike / §18 random-walk content; see #4386).  The on-axis bound #4389 is
the special case `v = e₁`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5 Theorem 17.5.1, §18, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Set Filter Topology

/-- **Lattice distance scales along a ray**: `latticeDistance d 0 (n • v) = n · latticeDistance d 0
v` (`latticeDistance` is `ℓ¹`, additive under the `ℕ`-scaling of the coordinate vector). -/
theorem latticeDistance_zero_nsmul {d : ℕ} (n : ℕ) (v : Fin d → ℤ) :
    latticeDistance d 0 (n • v) = n * latticeDistance d 0 v := by
  unfold latticeDistance
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Int.natAbs_mul]

/-- **Directional abscissa upper bound for the true mass** (GJ §17.5/§18, toward #4386): for
`1 ≤ d`, `0 < J`, `0 < β`, and any nonzero direction `v ≠ 0`,
`latticeMass(σ) ≤ ofReal(liminf_k τ_v(k))` where `τ_v(k) = −log⟨φ₀φ_{(k+1)v}⟩_∞/((k+1)·d(0,v))`.
Each admissible decay rate `α` is `≤ liminf τ_v` (apply `HasExponentialDecay` at the ray pair
`(0,(k+1)v)` of distance `(k+1)·d(0,v)`; the prefactor washes out), so `sSup (= latticeMass) ≤
ofReal(liminf τ_v)`.  Generalizes the on-axis bound #4389 to all directions. -/
theorem latticeMass_le_ofReal_liminf_directionalRate {d : ℕ} {J β : ℝ}
    (hJ : 0 < J) (hβ : 0 < β) {v : Fin d → ℤ} (hv : v ≠ 0) :
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ ENNReal.ofReal (Filter.liminf
          (fun k : ℕ => (-Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
              (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), (k + 1) • v}))
            / (((k : ℝ) + 1) * (latticeDistance d 0 v : ℝ))) atTop) := by
  classical
  have hβJ : 0 < β * J := mul_pos hβ hJ
  -- `D = d(0,v) ≥ 1`.
  have hD1 : 1 ≤ latticeDistance d 0 v :=
    Nat.one_le_iff_ne_zero.mpr (fun h => hv ((latticeDistance_eq_zero_iff d 0 v).mp h).symm)
  have hDR : (1 : ℝ) ≤ (latticeDistance d 0 v : ℝ) := by exact_mod_cast hD1
  set D : ℝ := (latticeDistance d 0 v : ℝ) with hDdef
  set e : ℕ → Fin d → ℤ := fun k => (k + 1) • v with he
  set g : ℕ → ℝ := fun k => Ambient.correlationInfinite (IsingModel.latticeGraph d)
    (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), e k} with hg
  set τ : ℕ → ℝ := fun k => (-Real.log (g k)) / (((k : ℝ) + 1) * D) with hτ
  have hkD1 : ∀ k : ℕ, (0 : ℝ) < ((k : ℝ) + 1) * D := by
    intro k; have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    exact mul_pos this (lt_of_lt_of_le one_pos hDR)
  have hne : ∀ k : ℕ, (0 : Fin d → ℤ) ≠ e k := by
    intro k h
    rw [he] at h
    have : ((k + 1 : ℕ) • v) = 0 := h.symm
    rw [smul_eq_zero] at this
    rcases this with h0 | h0
    · omega
    · exact hv h0
  have hdist : ∀ k : ℕ, latticeDistance d 0 (e k) = (k + 1) * latticeDistance d 0 v := by
    intro k; rw [he, latticeDistance_zero_nsmul]
  have hg_pos : ∀ k : ℕ, 0 < g k := by
    intro k; rw [hg]; exact correlationInfinite_pos_of_betaJ_pos_pair hβ hβJ (hne k)
  refine sSup_le ?_
  rintro b ⟨α, hα_decay, rfl⟩
  obtain ⟨C, hC, hbound⟩ := hα_decay
  -- per-`k` lower bound on `τ_v`.
  have hτ_ge : ∀ k : ℕ, (α : ℝ) + (-Real.log C) / (((k : ℝ) + 1) * D) ≤ τ k := by
    intro k
    have hb := hbound 0 (e k) (hne k)
    rw [truncated2Infinite_h_zero (IsingModel.latticeGraph d) (cubicExhaustion d) J β 0 (e k),
      abs_of_pos (hg_pos k), hdist k] at hb
    push_cast at hb
    have hCpos : 0 < C := by
      rcases lt_or_eq_of_le hC with h | h
      · exact h
      · exfalso; rw [← h, zero_mul] at hb; exact absurd hb (not_le.mpr (hg_pos k))
    have hlog : -Real.log C + α * (((k : ℝ) + 1) * D) ≤ -Real.log (g k) := by
      have hle := Real.log_le_log (hg_pos k) hb
      rw [Real.log_mul (ne_of_gt hCpos) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hle
      nlinarith [hle]
    rw [hτ, le_div_iff₀ (hkD1 k)]
    have hexp : ((α : ℝ) + (-Real.log C) / (((k : ℝ) + 1) * D)) * (((k : ℝ) + 1) * D)
        = α * (((k : ℝ) + 1) * D) + (-Real.log C) := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt (hkD1 k))]
    rw [hexp]; linarith [hlog]
  -- fence `→ α`.
  have hgtop : Tendsto (fun k : ℕ => ((k : ℝ) + 1) * D) atTop atTop :=
    Filter.Tendsto.atTop_mul_const (lt_of_lt_of_le one_pos hDR)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hdiv0 : Tendsto (fun k : ℕ => (-Real.log C) / (((k : ℝ) + 1) * D)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hgtop
  have htend : Tendsto (fun k : ℕ => (α : ℝ) + (-Real.log C) / (((k : ℝ) + 1) * D)) atTop
      (nhds (α : ℝ)) := by simpa using (tendsto_const_nhds (x := (α : ℝ))).add hdiv0
  have hlb_liminf : Filter.liminf
      (fun k : ℕ => (α : ℝ) + (-Real.log C) / (((k : ℝ) + 1) * D)) atTop = (α : ℝ) :=
    htend.liminf_eq
  -- `τ_v ≤ −log tanh` (cobounded): the tanh path lower bound `g k ≥ tanh^{(k+1)D}`.
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβJ) (Real.cosh_pos _)
  have hg_eq : ∀ k : ℕ, g k = twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) (e k) := by
    intro k
    simp only [hg]
    rw [correlationInfinite_latticeGraph_pair_eq_twoPointFunction d
      (⟨J, 0, β⟩ : IsingParams ℝ) hf 0 (e k), sub_zero]
  have hτ_above : ∀ k : ℕ, τ k ≤ -Real.log (Real.tanh (β * J)) := by
    intro k
    have hgge : Real.tanh (β * J) ^ ((k + 1) * latticeDistance d 0 v) ≤ g k := by
      rw [hg_eq k]
      have hge := twoPointFunction_ge_tanh_betaJ_pow_dist hJ.le hβ (Ne.symm (hne k))
      rwa [hdist k] at hge
    have hlog : -Real.log (g k) ≤ ((k : ℝ) + 1) * D * (-Real.log (Real.tanh (β * J))) := by
      have h1 := Real.log_le_log (pow_pos htanh_pos _) hgge
      rw [Real.log_pow] at h1
      push_cast at h1
      nlinarith [h1]
    rw [hτ, div_le_iff₀ (hkD1 k)]
    nlinarith [hlog]
  have hτ_bdd_above : IsBoundedUnder (· ≤ ·) atTop τ :=
    ⟨-Real.log (Real.tanh (β * J)), Filter.eventually_map.mpr (Eventually.of_forall hτ_above)⟩
  have hα_le : (α : ℝ) ≤ Filter.liminf τ atTop := by
    rw [← hlb_liminf]
    exact Filter.liminf_le_liminf (Eventually.of_forall hτ_ge) htend.isBoundedUnder_ge
      hτ_bdd_above.isCoboundedUnder_ge
  calc ((α : NNReal) : ENNReal) = ENNReal.ofReal (α : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hα_le

end Ambient
end IsingModel
