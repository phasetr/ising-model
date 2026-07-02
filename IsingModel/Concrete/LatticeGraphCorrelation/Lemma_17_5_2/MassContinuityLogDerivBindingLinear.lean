import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDerivInfiniteSharp

/-!
# GJ §17.5 Theorem 17.5.1 — Brick 1: linear log-Lipschitz per-pair estimate (binding pairs, `d ≥ 3`)

The reduction file `MassContinuityLatticeMassLogLipReduction.lean` shows that GJ Theorem 17.5.1
(continuity of the true mass `m(β)`, p.312) follows from the literal p.312 estimate
`|∂_β log⟨φ_0 φ_x⟩^∞| ≤ K·d(0,x)` (the `β`-log-derivative bounded *linearly* in the separation),
uniformly over all ray points.  This file establishes that per-pair estimate on the range the
existing (axiom-free) infrastructure can reach: **binding pairs** in dimension `d ≥ 3`.

The sharp infinite-volume derivative bound `|∂_β ⟨φ_x φ_z⟩^∞| ≤ S·⟨φ_x φ_z⟩^∞`
(`abs_deriv_correlationInfinite_le_sharp`, `MassContinuityDerivInfiniteSharp.lean`) is fed through
`HasDerivAt.log` (using `⟨φ_x φ_z⟩^∞ > 0`) to turn the *ratio* bound into a *log-derivative* bound
`|∂_β log⟨φ_x φ_z⟩^∞| ≤ S`; then the choice `α = d − 1` (the unique exponent making `S` linear in
`r = d(x,z)`; the constraints `1 ≤ α`, `d < 2α`, `α < d` read `d ≥ 3`) linearizes `S ≤ K·r`.

The general (non-binding) case is the Ornstein–Zernike sharp-lower-bound gap (§18.6–18.7 walk-sum
content), deferred.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real Filter

/-- **Linearization of the sharp p.312 growth/decay product at the critical exponent `α = d − 1`.**
For `d ≥ 3`, `0 ≤ m`, `1 ≤ r`, the growth factor `1 + (m·r)^{d-1}` against the decay factor
`(1 + r)^{-(2(d-1) − d)}` is bounded by `(1 + m^{d-1})·r`, exhibiting the linear-in-`r` behaviour
that makes the sharp coefficient `S` linear in the separation.  The crux is
`r^{d-1} ≤ r·(1 + r)^{d-2}`, i.e. `r^{d-1}·(1 + r)^{-(d-2)} ≤ r`. -/
private lemma sharp_growth_decay_le_linear {d : ℕ} (hd : 3 ≤ d) {m r : ℝ}
    (hm : 0 ≤ m) (hr : 1 ≤ r) :
    (1 + (m * r) ^ (d - 1)) * (1 + r) ^ (-(2 * ((d - 1 : ℕ) : ℝ) - (d : ℝ)))
      ≤ (1 + m ^ (d - 1)) * r := by
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
  have hr_pos : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have h1r_pos : (0 : ℝ) < 1 + r := by linarith
  have hr_le : r ≤ 1 + r := by linarith
  set p : ℝ := (d : ℝ) - 2 with hp_def
  have hp0 : (0 : ℝ) ≤ p := by
    have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    rw [hp_def]; linarith
  have hexp_eq : -(2 * ((d - 1 : ℕ) : ℝ) - (d : ℝ)) = -p := by
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    rw [hcast, hp_def]; ring
  rw [hexp_eq]
  have hrpow_pos : (0 : ℝ) < (1 + r) ^ (-p) := Real.rpow_pos_of_pos h1r_pos _
  have hdecay1 : (1 + r) ^ (-p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  -- the crux: `r^{d-1} ≤ r · (1 + r)^p`, hence `r^{d-1}·(1 + r)^{-p} ≤ r`.
  have hcastk : ((d - 1 : ℕ) : ℝ) = 1 + p := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one, hp_def]; ring
  have hrk : r ^ (d - 1) ≤ r * (1 + r) ^ p := by
    have h1 : r ^ (d - 1) = r ^ ((d - 1 : ℕ) : ℝ) := (Real.rpow_natCast r (d - 1)).symm
    rw [h1, hcastk, Real.rpow_add hr_pos, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr0 hr_le hp0) hr0
  have hmain : r ^ (d - 1) * (1 + r) ^ (-p) ≤ r := by
    calc r ^ (d - 1) * (1 + r) ^ (-p)
        ≤ (r * (1 + r) ^ p) * (1 + r) ^ (-p) :=
          mul_le_mul_of_nonneg_right hrk hrpow_pos.le
      _ = r * ((1 + r) ^ p * (1 + r) ^ (-p)) := by ring
      _ = r * (1 + r) ^ (p + -p) := by rw [← Real.rpow_add h1r_pos]
      _ = r := by rw [add_neg_cancel, Real.rpow_zero, mul_one]
  calc (1 + (m * r) ^ (d - 1)) * (1 + r) ^ (-p)
      = (1 + r) ^ (-p) + (m * r) ^ (d - 1) * (1 + r) ^ (-p) := by ring
    _ = (1 + r) ^ (-p) + m ^ (d - 1) * (r ^ (d - 1) * (1 + r) ^ (-p)) := by
        rw [mul_pow]; ring
    _ ≤ r + m ^ (d - 1) * r :=
        add_le_add (le_trans hdecay1 hr)
          (mul_le_mul_of_nonneg_left hmain (pow_nonneg hm _))
    _ = (1 + m ^ (d - 1)) * r := by ring

/-- **Brick 1 — linear log-Lipschitz per-pair estimate for binding pairs, `d ≥ 3`** (GJ p.312).
For a non-adjacent binding pair `x ≠ z` (`m⁻(x,z) = globalPseudoMassDist > 0`) at `β ∈ window` with
`d ≥ 3`, the `β`-log-derivative of the infinite-volume two-point function is bounded *linearly* in
the separation: `∃ K ≥ 0, |∂_β log⟨φ_x φ_z⟩^∞| ≤ K·d(x,z)`, where `K` is an explicit function of
`J`, `m⁻(β)`, the convergence constant `C(β)` and `d` (single-`β` version).

Proof: from the sharp ratio bound `|∂_β ⟨φ_x φ_z⟩^∞| ≤ S·⟨φ_x φ_z⟩^∞`
(`abs_deriv_correlationInfinite_le_sharp`, `α = d − 1`) and `⟨φ_x φ_z⟩^∞ > 0`, the log-derivative is
`∂_β ⟨φ_x φ_z⟩^∞ / ⟨φ_x φ_z⟩^∞` (`HasDerivAt.log`), so `|∂_β log⟨φ_x φ_z⟩^∞| ≤ S`; then
`sharp_growth_decay_le_linear` gives `S ≤ K·d(x,z)`. -/
theorem abs_deriv_log_correlationInfinite_le_dist_of_binding {d : ℕ} (hd : 3 ≤ d)
    (hα : 1 ≤ d - 1) {J β : ℝ} (hJ : 0 < J) (hβ_win : β ∈ ConvergenceRegion.window d J)
    {x z : Fin d → ℤ} (hxz : x ≠ z) (hxz_nonadj : ¬ (latticeGraph d).Adj x z)
    (hm_pos : 0 < globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
    (hbind : pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧
      |deriv (fun β' => Real.log (correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})) β|
        ≤ K * (latticeDistance d x z : ℝ) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hβ_pos : 0 < β := (ConvergenceRegion.window_subset_highTemp d J hJ hd1 hβ_win).1
  -- positivity of the two-point function at `β` (needed to pass from the ratio to the log bound).
  have hc_pos : 0 < correlationInfinite (latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} :=
    (correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (cubicExhaustion d) hβ_pos (mul_pos hβ_pos hJ) x z hxz).1
  -- the sharp p.312 ratio bound `|∂_β c| ≤ S · c`, with `α = d − 1`.
  obtain ⟨C, hC, hsharp⟩ := abs_deriv_correlationInfinite_le_sharp hα hd1
    (by omega : d < 2 * (d - 1)) (by omega : d - 1 < d) hJ hβ_win hxz hxz_nonadj hm_pos hbind
  -- `HasDerivAt` of the correlation profile at `β` (same limit used inside the sharp lemma).
  obtain ⟨g', hderiv_lim⟩ :=
    ConvergenceRegion.derivativeLimit_on_window d J (cubicExhaustion d) hJ hxz
  have hHasDeriv : HasDerivAt (fun β' => correlationInfinite (latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) (g' β) β :=
    correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
      hd1 (cubicExhaustion d) x z hxz J hJ g' isOpen_Ioo
      (ConvergenceRegion.window_subset_highTemp d J hJ hd1) hderiv_lim β hβ_win
  -- log-derivative: `∂_β log c = ∂_β c / c`.
  have hlog : HasDerivAt (fun β' => Real.log (correlationInfinite (latticeGraph d)
      (cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}))
      (g' β / correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) β :=
    hHasDeriv.log hc_pos.ne'
  -- abbreviate the pseudo-mass and the separation.
  set m := globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) with hm_def
  set r := (latticeDistance d x z : ℝ) with hr_def
  have hr_nat : 1 ≤ latticeDistance d x z :=
    Nat.pos_of_ne_zero (fun h => hxz ((latticeDistance_eq_zero_iff d x z).mp h))
  have hr1 : (1 : ℝ) ≤ r := by rw [hr_def]; exact_mod_cast hr_nat
  have hm0 : (0 : ℝ) ≤ m := hm_pos.le
  have hexpnn : (0 : ℝ) ≤ Real.exp m := (Real.exp_pos m).le
  refine ⟨J * (2 * Real.exp m * C * (1 + m ^ (d - 1)))
      + J * (4 * (d : ℝ) * (1 + (2 : ℝ) ^ (d - 1)) * Real.exp m), ?_, ?_⟩
  · -- nonnegativity of `K`.
    refine add_nonneg (mul_nonneg hJ.le ?_) (mul_nonneg hJ.le ?_)
    · have hmk : (0 : ℝ) ≤ m ^ (d - 1) := pow_nonneg hm0 _
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hexpnn) hC.le) (by linarith)
    · have htk : (0 : ℝ) ≤ (2 : ℝ) ^ (d - 1) := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (by positivity : (0 : ℝ) ≤ (d : ℝ))) (by linarith)) hexpnn
  · -- the main bound `|∂_β log c| ≤ K · r`.
    rw [hlog.deriv, abs_div, abs_of_pos hc_pos, div_le_iff₀ hc_pos, ← hHasDeriv.deriv]
    refine le_trans hsharp (mul_le_mul_of_nonneg_right ?_ hc_pos.le)
    -- reduce to `S ≤ K · r`.
    have hlin := sharp_growth_decay_le_linear hd hm0 hr1
    set A1 := (m * r) ^ (d - 1) with hA1_def
    set W := (1 + r) ^ (-(2 * ((d - 1 : ℕ) : ℝ) - (d : ℝ))) with hW_def
    set B1 := m ^ (d - 1) with hB1_def
    set T1 := (2 : ℝ) ^ (d - 1) with hT1_def
    have hT0 : (0 : ℝ) ≤ T1 := by rw [hT1_def]; positivity
    have hcoefA : (0 : ℝ) ≤ J * 2 * Real.exp m * C :=
      mul_nonneg (mul_nonneg (mul_nonneg hJ.le (by norm_num)) hexpnn) hC.le
    have hAle : (J * 2 * Real.exp m * C) * ((1 + A1) * W)
        ≤ (J * 2 * Real.exp m * C) * ((1 + B1) * r) :=
      mul_le_mul_of_nonneg_left hlin hcoefA
    have hcoefB : (0 : ℝ) ≤ J * (4 * (d : ℝ) * (1 + T1) * Real.exp m) :=
      mul_nonneg hJ.le (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (by positivity : (0 : ℝ) ≤ (d : ℝ))) (by linarith)) hexpnn)
    have hB : J * ((4 * (d : ℝ)) * ((1 + T1) * Real.exp m))
        ≤ (J * (4 * (d : ℝ) * (1 + T1) * Real.exp m)) * r := by
      rw [show J * ((4 * (d : ℝ)) * ((1 + T1) * Real.exp m))
          = J * (4 * (d : ℝ) * (1 + T1) * Real.exp m) from by ring]
      exact le_mul_of_one_le_right hcoefB hr1
    calc J * (2 * (1 + A1) * Real.exp m * (C * W))
            + J * ((4 * (d : ℝ)) * ((1 + T1) * Real.exp m))
        = (J * 2 * Real.exp m * C) * ((1 + A1) * W)
            + J * ((4 * (d : ℝ)) * ((1 + T1) * Real.exp m)) := by ring
      _ ≤ (J * 2 * Real.exp m * C) * ((1 + B1) * r)
            + (J * (4 * (d : ℝ) * (1 + T1) * Real.exp m)) * r := add_le_add hAle hB
      _ = (J * (2 * Real.exp m * C * (1 + B1))
            + J * (4 * (d : ℝ) * (1 + T1) * Real.exp m)) * r := by ring

end Ambient
end IsingModel
