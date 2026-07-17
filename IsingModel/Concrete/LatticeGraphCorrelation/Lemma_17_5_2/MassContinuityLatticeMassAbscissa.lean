import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.UpperBound
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.PathLowerBound
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import Mathlib.Analysis.SpecificLimits.Basic
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromSimonLieb

/-!
# GJ §17.5/§18 Theorem 17.5.1 — on-axis abscissa upper bound for the true mass

Toward true-mass `latticeMass` continuity (#4386): the **on-axis abscissa** upper bound

`latticeMass(σ) ≤ ofReal(liminf_k τ(k))`,  `τ(k) = −log⟨φ₀ φ_{(k+1)e₁}⟩_∞ / (k+1)`,

which **tightens** the unconditional `latticeMass ≤ ofReal(−log tanh(βJ))` bound (each `τ(k) ≤
−log tanh(βJ)`, so `liminf τ ≤ −log tanh`).  Every admissible decay rate `α` (in the `sSup`
defining `latticeMass`) satisfies, at the on-axis pair `(0, (k+1)e₁)` of distance `k+1`,
`⟨φ₀φ_{(k+1)e₁}⟩ ≤ C e^{−α(k+1)}`, hence `τ(k) ≥ α + (−log C)/(k+1) → α`, so `liminf τ ≥ α`; taking
the `sSup` over `α` gives the bound.  This is the upper half of the abscissa characterization the
semicontinuity analysis of the true mass rests on.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5 Theorem 17.5.1, §18, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Set Filter Topology

/-- **On-axis distance**: `latticeDistance d 0 (Pi.single ⟨0,hd⟩ (k:ℤ)) = k` for `0 ≤ k`. -/
theorem latticeDistance_zero_single {d : ℕ} (hd : 0 < d) (k : ℤ) :
    latticeDistance d 0 (Pi.single (⟨0, hd⟩ : Fin d) k) = k.natAbs := by
  unfold latticeDistance
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **On-axis abscissa upper bound for the true mass** (GJ §17.5/§18, toward #4386): for `1 ≤ d`,
`0 < J`, `0 < β`, `latticeMass(σ) ≤ ofReal(liminf_k τ(k))` where
`τ(k) = −log⟨φ₀φ_{(k+1)e₁}⟩_∞/(k+1)`
is the on-axis per-distance decay rate.  Each admissible decay rate `α` is `≤ liminf τ` (apply
`HasExponentialDecay` at the on-axis pair of distance `k+1`; the prefactor `C` washes out as
`k → ∞`), so the `sSup` (`= latticeMass`) is `≤ ofReal(liminf τ)`. -/
theorem latticeMass_le_ofReal_liminf_onAxisRate {d : ℕ} (hd : 1 ≤ d) {J β : ℝ}
    (hJ : 0 < J) (hβ : 0 < β) :
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ ENNReal.ofReal (Filter.liminf
          (fun k : ℕ => (-Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
              (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {(0 : Fin d → ℤ), Pi.single (⟨0, hd⟩ : Fin d) ((k : ℤ) + 1)}))
            / ((k : ℝ) + 1)) atTop) := by
  classical
  have hd0 : 0 < d := hd
  have hβJ : 0 < β * J := mul_pos hβ hJ
  set e : ℕ → Fin d → ℤ := fun k => Pi.single (⟨0, hd0⟩ : Fin d) ((k : ℤ) + 1) with he
  set g : ℕ → ℝ := fun k => Ambient.correlationInfinite (IsingModel.latticeGraph d)
    (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), e k} with hg
  set τ : ℕ → ℝ := fun k => (-Real.log (g k)) / ((k : ℝ) + 1) with hτ
  -- distinctness and distance of the on-axis pair.
  have hne : ∀ k : ℕ, (0 : Fin d → ℤ) ≠ e k := by
    intro k h
    have hc := congrFun h (⟨0, hd0⟩ : Fin d)
    simp only [he, Pi.zero_apply, Pi.single_eq_same] at hc
    omega
  have hdist : ∀ k : ℕ, latticeDistance d 0 (e k) = k + 1 := by
    intro k
    rw [he, latticeDistance_zero_single hd0 ((k : ℤ) + 1)]
    omega
  have hg_pos : ∀ k : ℕ, 0 < g k := by
    intro k
    rw [hg]
    exact correlationInfinite_pos_of_betaJ_pos_pair hβ hβJ (hne k)
  -- the on-axis sequence rate `τ` is the lower-fence target.
  refine sSup_le ?_
  rintro b ⟨α, hα_decay, rfl⟩
  -- `α ≤ liminf τ` from the decay bound at the on-axis pairs.
  obtain ⟨C, hC, hbound⟩ := hα_decay
  -- per-`k` lower bound on `τ`.
  have hτ_ge : ∀ k : ℕ, (α : ℝ) + (-Real.log C) / ((k : ℝ) + 1) ≤ τ k := by
    intro k
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    -- decay bound at the on-axis pair, with `|trunc| = g k`.
    have hb := hbound 0 (e k) (hne k)
    rw [truncated2Infinite_h_zero (IsingModel.latticeGraph d) (cubicExhaustion d) J β 0 (e k),
      abs_of_pos (hg_pos k), hdist k] at hb
    push_cast at hb
    -- `g k ≤ C · exp(-α (k+1))`, `C > 0`.
    have hCpos : 0 < C := by
      rcases lt_or_eq_of_le hC with h | h
      · exact h
      · exfalso
        rw [← h, zero_mul] at hb
        exact absurd hb (not_le.mpr (hg_pos k))
    -- take `-log`: `-log(g k) ≥ -log C + α (k+1)`.
    have hlog : -Real.log C + α * ((k : ℝ) + 1) ≤ -Real.log (g k) := by
      have hle := Real.log_le_log (hg_pos k) hb
      rw [Real.log_mul (ne_of_gt hCpos) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hle
      nlinarith [hle]
    rw [hτ, le_div_iff₀ hk1]
    have hexp : ((α : ℝ) + (-Real.log C) / ((k : ℝ) + 1)) * ((k : ℝ) + 1)
        = α * ((k : ℝ) + 1) + (-Real.log C) := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hk1)]
    rw [hexp]
    linarith [hlog]
  -- `liminf` of the lower fence equals `α`.
  have hgtop : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hdiv0 : Tendsto (fun k : ℕ => (-Real.log C) / ((k : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hgtop
  have htend : Tendsto (fun k : ℕ => (α : ℝ) + (-Real.log C) / ((k : ℝ) + 1)) atTop
      (nhds (α : ℝ)) := by simpa using (tendsto_const_nhds (x := (α : ℝ))).add hdiv0
  have hlb_liminf : Filter.liminf (fun k : ℕ => (α : ℝ) + (-Real.log C) / ((k : ℝ) + 1)) atTop
      = (α : ℝ) := htend.liminf_eq
  -- `τ` is bounded above by `−log tanh(βJ)` (so `liminf τ` is cobounded): the on-axis correlation
  -- has the tanh path lower bound `g k ≥ tanh(βJ)^{k+1}`.
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
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hgge : Real.tanh (β * J) ^ (k + 1) ≤ g k := by
      rw [hg_eq k]
      have hge := twoPointFunction_ge_tanh_betaJ_pow_dist hJ.le hβ (Ne.symm (hne k))
      rwa [hdist k] at hge
    have hlog : -Real.log (g k) ≤ ((k : ℝ) + 1) * (-Real.log (Real.tanh (β * J))) := by
      have h1 := Real.log_le_log (pow_pos htanh_pos (k + 1)) hgge
      rw [Real.log_pow] at h1
      push_cast at h1
      nlinarith [h1]
    rw [hτ, div_le_iff₀ hk1]
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
