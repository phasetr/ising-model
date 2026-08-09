import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.FiniteRegionPseudoMassDistLipschitz
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.PathLowerBound
import IsingModel.ClusterExpansion.TwoPointConvergenceWindow

/-!
# Unconditional lower bound on the ℤ^d two-point function by the distance profile

Supplies outright, rather than as an assumption, a per-pair lower bound on the infinite-volume
ℤ^d correlation by the distance profile: on the high-temperature convergence window, and at
the direct-path rate `-Real.log (Real.tanh (β * J))`, the profile `pseudoMassG` evaluated at
the lattice distance between a pair of sites is at most the infinite-volume correlation of
that pair along `Ambient.cubicExhaustion d`.

The steps taken here are arithmetic; the combinatorial input is imported. Whenever the product
of rate and radius is at least `1`, the profile is at most `Real.exp` of the negative of that
product, its denominator being at least `2` there. On `ConvergenceRegion.window d J` the
activity `Real.tanh (β * J)` is strictly below `Real.exp (-1)`, since the window confines
`β * J` strictly below `Real.artanh` of the activity radius `ConvergenceRegion.R d` and that
radius is itself at most `Real.exp (-1)`; hence the rate is at least `1`, and for a pair of
distinct sites the product of rate and lattice distance is at least `1` as well. The profile
is therefore at most `Real.tanh (β * J)` raised to the lattice distance, which the upstream
GKS direct-path bound in turn bounds above by the two-point function.

The conclusion is recorded first anchored at the origin, for a nonzero site, and then for an
arbitrary pair of distinct sites. The general form follows from the anchored one by translating
the pair `{x, z}` to `{0, z - x}`: that translation leaves the infinite-volume correlation along
the cubic exhaustion unchanged, and it leaves the lattice distance unchanged. The anchored
bound and the general-pair bound each assume positivity of the coupling, positivity of the
inverse temperature, distinctness of the sites involved and membership of the inverse
temperature in the window; the arithmetic step assumes only that the product of rate and radius
is at least `1`, and the window observations assume positivity of the coupling and membership
in the window, saying nothing about the sites. No instance argument is taken anywhere in this
module.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **`pseudoMassG α r t ≤ exp(−t r)` when `1 ≤ t·r`.**
`pseudoMassG α r t = 2 e^{−tr}/(1+(tr)^α)`; from `(tr)^α ≥ 1` the denominator is `≥ 2`. -/
theorem pseudoMassG_le_exp_neg_of_one_le {α : ℕ} {r t : ℝ} (h : 1 ≤ t * r) :
    pseudoMassG α r t ≤ Real.exp (-(t * r)) := by
  unfold pseudoMassG
  have hpow : (1 : ℝ) ≤ (t * r) ^ α := one_le_pow₀ h
  have hden : (0 : ℝ) < 1 + (t * r) ^ α := by positivity
  have hexp : 0 < Real.exp (-(t * r)) := Real.exp_pos _
  rw [div_le_iff₀ hden]
  nlinarith [hexp, hpow]

/-- **On the convergence window the activity is below `e⁻¹`**: for `0 < J` and
`β ∈ ConvergenceRegion.window d J`, `tanh(βJ) < e⁻¹`. -/
theorem tanh_betaJ_lt_exp_neg_one_of_window {d : ℕ} {J β : ℝ} (hJ : 0 < J)
    (hβ : β ∈ ConvergenceRegion.window d J) :
    Real.tanh (β * J) < Real.exp (-1) := by
  obtain ⟨hβ0, hβlt⟩ := hβ
  have hRpos : 0 < ConvergenceRegion.R d := twoPointHTActivityRadius_pos (2 * d)
  have hRlt1 : ConvergenceRegion.R d < 1 := ConvergenceRegion.R_lt_one d
  have hβJ : β * J < Real.artanh (ConvergenceRegion.R d) := by
    rw [lt_div_iff₀ hJ] at hβlt; linarith [hβlt]
  have htanh_lt : Real.tanh (β * J) < ConvergenceRegion.R d := by
    have hlt : Real.artanh (Real.tanh (β * J)) < Real.artanh (ConvergenceRegion.R d) := by
      rw [Real.artanh_tanh]; exact hβJ
    have h1 : Real.tanh (β * J) ∈ Set.Ioo (-1 : ℝ) 1 :=
      ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
    have h2 : ConvergenceRegion.R d ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hRlt1⟩
    exact (Real.artanh_lt_artanh_iff h1 h2).mp hlt
  -- `R d ≤ 1/(64·((2d)²+1)·e) ≤ 1/e = exp(-1)`.
  have hRle : ConvergenceRegion.R d ≤ Real.exp (-1) := by
    have hmin : ConvergenceRegion.R d ≤
        1 / (64 * ((((2 * d : ℕ) : ℝ) ^ 2 + 1) * Real.exp 1)) := by
      unfold ConvergenceRegion.R twoPointHTActivityRadius
      exact min_le_left _ _
    have he1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    have hfac : (1 : ℝ) ≤ 64 * (((2 * d : ℕ) : ℝ) ^ 2 + 1) := by
      have : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ) ^ 2 := sq_nonneg _
      nlinarith
    have hle2 : 1 / (64 * ((((2 * d : ℕ) : ℝ) ^ 2 + 1) * Real.exp 1)) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, ← one_div]
      apply one_div_le_one_div_of_le he1
      nlinarith [he1, hfac, mul_le_mul_of_nonneg_right hfac he1.le]
    exact le_trans hmin hle2
  linarith

/-- **On the window the direct-path rate `−log tanh(βJ)` is `≥ 1`.** -/
theorem one_le_neg_log_tanh_betaJ_of_window {d : ℕ} {J β : ℝ} (hJ : 0 < J)
    (hβ : β ∈ ConvergenceRegion.window d J) :
    (1 : ℝ) ≤ -Real.log (Real.tanh (β * J)) := by
  have hβ0 : 0 < β := hβ.1
  have hβJpos : 0 < β * J := mul_pos hβ0 hJ
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβJpos) (Real.cosh_pos _)
  have htanh_lt : Real.tanh (β * J) < Real.exp (-1) :=
    tanh_betaJ_lt_exp_neg_one_of_window hJ hβ
  have hlog : Real.log (Real.tanh (β * J)) < -1 := by
    have := Real.log_lt_log htanh_pos htanh_lt
    rwa [Real.log_exp] at this
  linarith

/-- **GJ §17.5 unconditional faithful profile lower bound (anchored, cubic, on the window).**
For `z ≠ 0` and `β ∈ ConvergenceRegion.window d J`, the distance-radius profile at the
direct-path rate `−log tanh(βJ)` lower-bounds the anchored two-point function:
`pseudoMassG α (dist 0 z) (−log tanh(βJ)) ≤ ⟨φ₀ φ_z⟩^∞`.

The bound is unconditional at this rate: it is the correlation lower bound
that the rate-agnostic Lipschitz route of `UnconditionalFiniteRegionLipschitz.lean` re-parametrizes
to.  The `hprofile` binder of the conditional modules
(`pseudoMassFromParamsAtPairDist_pow_succ_lipschitz_on_window_of_profile_lower` and its
finite-region consumer) is a *different* statement, taken at the walk rate `−log (βJ·2d)`: for
`1 ≤ d` on the window `tanh(βJ) < βJ ≤ βJ·2d`, so the direct-path rate is the larger of the two,
and `pseudoMassG` is antitone in the rate (`pseudoMassG_antitoneOn`).  The bound proved here is
therefore strictly weaker than that binder and does not discharge it.

Proof: on the window `tanh(βJ) < e⁻¹`, so the rate `q := −log tanh(βJ)` satisfies `1 ≤ q`, hence
`q·dist ≥ 1` and `pseudoMassG α (dist) q ≤ e^{−q·dist} = tanh(βJ)^{dist}`
(`pseudoMassG_le_exp_neg_of_one_le`); the GKS direct-path bound
`twoPointFunction_ge_tanh_betaJ_pow_dist` gives `tanh(βJ)^{dist} ≤ ⟨φ₀ φ_z⟩`.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 / Lemma 17.5.2, pp.~311--312; GKS direct path. -/
theorem pseudoMassG_dist_tanh_rate_le_correlationInfinite_cubic_zero
    {d α : ℕ} {J β : ℝ} (hJ_pos : 0 < J) (hβ : 0 < β)
    {z : Fin d → ℤ} (hz : z ≠ 0)
    (hβwin : β ∈ ConvergenceRegion.window d J) :
    pseudoMassG α (IsingModel.latticeDistance d 0 z : ℝ) (-Real.log (Real.tanh (β * J)))
      ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), z} := by
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hJ_pos)) (Real.cosh_pos _)
  have hr1 : (1 : ℝ) ≤ -Real.log (Real.tanh (β * J)) :=
    one_le_neg_log_tanh_betaJ_of_window hJ_pos hβwin
  have hdist_pos : 1 ≤ IsingModel.latticeDistance d 0 z := by
    rw [Nat.one_le_iff_ne_zero]
    intro h
    exact hz ((IsingModel.latticeDistance_eq_zero_iff d 0 z).mp h).symm
  have hdist_real : (1 : ℝ) ≤ (IsingModel.latticeDistance d 0 z : ℝ) := by
    exact_mod_cast hdist_pos
  have h1 : (1 : ℝ) ≤
      -Real.log (Real.tanh (β * J)) * (IsingModel.latticeDistance d 0 z : ℝ) := by
    nlinarith [hr1, hdist_real]
  have halg := pseudoMassG_le_exp_neg_of_one_le (α := α) h1
  have hexp_eq :
      Real.exp (-(-Real.log (Real.tanh (β * J)) *
          (IsingModel.latticeDistance d 0 z : ℝ)))
        = Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z := by
    rw [show -(-Real.log (Real.tanh (β * J)) * (IsingModel.latticeDistance d 0 z : ℝ))
        = (IsingModel.latticeDistance d 0 z : ℝ) * Real.log (Real.tanh (β * J)) by ring]
    rw [Real.exp_nat_mul, Real.exp_log htanh_pos]
  rw [hexp_eq] at halg
  have hdp : Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z
      ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z :=
    twoPointFunction_ge_tanh_betaJ_pow_dist hJ_pos.le hβ hz
  rw [twoPointFunction_apply] at hdp
  exact le_trans halg hdp

/-- **GJ §17.5 unconditional faithful profile lower bound (general pair, cubic, on the window).**
For any distinct pair `x ≠ z` and `β ∈ ConvergenceRegion.window d J`,
`pseudoMassG α (dist x z) (−log tanh(βJ)) ≤ ⟨φ_x φ_z⟩^∞`.  Reduces to the anchored form by
translation invariance (`correlationInfinite_latticeGraph_pair_eq_twoPointFunction`,
`latticeDistance_translate_eq`).  This supplies, for every pair on the window, the per-pair
correlation lower bound at the direct-path rate `−log tanh(βJ)`, which is exactly the local
tanh-rate hypothesis discharged inside
`pseudoMassFromParamsAtPairDist_pow_succ_lipschitz_on_window`.  The walk-rate `hprofile` of the
conditional modules is the strictly stronger statement described on the anchored bound above, and is
*not* discharged here.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 / Lemma 17.5.2, pp.~311--312. -/
theorem pseudoMassG_dist_tanh_rate_le_correlationInfinite_cubic
    {d α : ℕ} {J β : ℝ} (hJ_pos : 0 < J) (hβ : 0 < β)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hβwin : β ∈ ConvergenceRegion.window d J) :
    pseudoMassG α (IsingModel.latticeDistance d x z : ℝ) (-Real.log (Real.tanh (β * J)))
      ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} := by
  have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ_pos.le, le_refl 0, hβ⟩
  have hzx : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
  rw [correlationInfinite_latticeGraph_pair_eq_twoPointFunction d
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z,
    twoPointFunction_apply, latticeDistance_translate_eq d x z]
  exact pseudoMassG_dist_tanh_rate_le_correlationInfinite_cubic_zero hJ_pos hβ hzx hβwin


end Ambient
end IsingModel
