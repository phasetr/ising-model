import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityLatticeMassAbscissa
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointCorrelationInfinite
import IsingModel.Inequalities.SimonLieb
import IsingModel.TranslationInvariance.Truncated
import Mathlib.Analysis.Subadditive

/-!
# GJ §17.5 Theorem 17.5.1 — on-axis inverse correlation length as a Fekete limit

Toward true-mass `latticeMass` continuity (#4386): the **on-axis inverse correlation length**
exists as a genuine limit (not merely a `liminf`).  Writing
`u(n) = −log⟨φ₀ φ_{n e₁}⟩_∞` for the on-axis log-correlation sequence, the second Griffiths
inequality (GKS-II, `correlationInfinite_latticeGraph_cubicExhaustion_gks_second`) gives
**supermultiplicativity** of the two-point function,

`⟨φ₀ φ_{m e₁}⟩ · ⟨φ_{m e₁} φ_{(m+n) e₁}⟩ ≤ ⟨φ₀ φ_{(m+n) e₁}⟩`,

and translation invariance (`correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset`) turns
`⟨φ_{m e₁} φ_{(m+n) e₁}⟩` into `⟨φ₀ φ_{n e₁}⟩`.  Taking `−log` makes `u` **subadditive**
(`u(m+n) ≤ u(m) + u(n)`); `u` is bounded below by `0` (correlations lie in `[0,1]`), so
Fekete's lemma (`Subadditive.tendsto_lim`) yields

`u(n)/n → onAxisInverseCorrelationLength := infₙ u(n)/n`.

This **upgrades** the on-axis abscissa upper bound `latticeMass ≤ ofReal(liminf_k τ(k))` (#4389)
to a true limit: `latticeMass ≤ ofReal(onAxisInverseCorrelationLength)`, where the bound is now a
genuine `lim`/`inf`.  It is the GJ §17.5 / FV statement that the (on-axis) inverse correlation
length is **well-defined** — a recognized result worth recording on its own — and the structural
scaffold the eventual matching lower bound (the Ornstein–Zernike / §18 sharp-rate content; #4386)
must hook into.  The matching lower bound and hence full continuity are *not* delivered here.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5 Theorem 17.5.1, §18, pp.~311--312.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3 (correlation length).
-/

namespace IsingModel
namespace Ambient

open Set Filter Topology

variable {d : ℕ}

/-- **On-axis lattice point** `n · e₁ = Pi.single ⟨0,hd⟩ (n : ℤ)` (the `n`-th site along the first
coordinate axis). -/
noncomputable def onAxisPoint (hd : 0 < d) (n : ℕ) : Fin d → ℤ :=
  Pi.single (⟨0, hd⟩ : Fin d) (n : ℤ)

/-- **On-axis log-correlation sequence** `u(n) = −log⟨φ₀ φ_{n e₁}⟩_∞`, the quantity whose
`n`-normalised limit is the on-axis inverse correlation length. -/
noncomputable def onAxisLogCorr (hd : 0 < d) (J β : ℝ) (n : ℕ) : ℝ :=
  -Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
    {(0 : Fin d → ℤ), onAxisPoint hd n})

/-- **First-coordinate value of the on-axis point**: `onAxisPoint hd n ⟨0,hd⟩ = (n : ℤ)`. -/
theorem onAxisPoint_eval (hd : 0 < d) (n : ℕ) :
    onAxisPoint hd n (⟨0, hd⟩ : Fin d) = (n : ℤ) :=
  Pi.single_eq_same _ _

/-- **The on-axis origin is the lattice origin**: `onAxisPoint hd 0 = 0`. -/
theorem onAxisPoint_zero (hd : 0 < d) : onAxisPoint hd 0 = 0 := by
  unfold onAxisPoint
  simp

/-- **Additivity of on-axis points**: `onAxisPoint hd m + onAxisPoint hd n = onAxisPoint hd (m+n)`
(`Pi.single` is additive in its value, `(m:ℤ)+(n:ℤ) = ((m+n:ℕ):ℤ)`). -/
theorem onAxisPoint_add (hd : 0 < d) (m n : ℕ) :
    onAxisPoint hd m + onAxisPoint hd n = onAxisPoint hd (m + n) := by
  unfold onAxisPoint
  rw [show ((m + n : ℕ) : ℤ) = (m : ℤ) + (n : ℤ) by push_cast; ring, Pi.single_add]

/-- **Distinctness of on-axis points**: distinct indices give distinct points (evaluate at the first
coordinate, where the value is the index cast to `ℤ`). -/
theorem onAxisPoint_ne (hd : 0 < d) {a b : ℕ} (hab : a ≠ b) :
    onAxisPoint hd a ≠ onAxisPoint hd b := by
  intro h
  apply hab
  have hc := congrFun h (⟨0, hd⟩ : Fin d)
  rw [onAxisPoint_eval, onAxisPoint_eval] at hc
  exact_mod_cast hc

/-- **Nonnegativity of the on-axis log-correlation**: `0 ≤ u(n)` since the ferromagnetic correlation
lies in `[0,1]`, so its `log` is `≤ 0`. -/
theorem onAxisLogCorr_nonneg (hd : 0 < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) (n : ℕ) :
    0 ≤ onAxisLogCorr hd J β n := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  unfold onAxisLogCorr
  have hnn := correlationInfinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf
    {(0 : Fin d → ℤ), onAxisPoint hd n}
  have hle := correlationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
    {(0 : Fin d → ℤ), onAxisPoint hd n}
  have hlog := Real.log_nonpos hnn hle
  linarith

/-- **Subadditivity of the on-axis log-correlation** (GKS-II supermultiplicativity + translation
invariance): `u(m+n) ≤ u(m) + u(n)`.  For `m,n ≥ 1`, GKS-II gives
`⟨φ₀φ_{me₁}⟩·⟨φ_{me₁}φ_{(m+n)e₁}⟩ ≤ ⟨φ₀φ_{(m+n)e₁}⟩` (`{me₁,0} ∆ {me₁,(m+n)e₁} = {(m+n)e₁,0}`),
translation turns the middle factor into `⟨φ₀φ_{ne₁}⟩`, and `−log` of the positive
supermultiplicative inequality is subadditivity; the `m=0`/`n=0` cases reduce to `0 ≤ u(0)`. -/
theorem onAxisLogCorr_subadditive (hd : 0 < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    Subadditive (onAxisLogCorr hd J β) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have hβJ : 0 < β * J := mul_pos hβ hJ
  intro m n
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simpa using onAxisLogCorr_nonneg hd hJ hβ 0
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 := onAxisLogCorr_nonneg hd hJ hβ 0
    have : onAxisLogCorr hd J β m
        ≤ onAxisLogCorr hd J β m + onAxisLogCorr hd J β 0 := by linarith
    simpa using this
  -- `m, n ≥ 1`: distinctness of the three on-axis points.
  have h0m : (0 : Fin d → ℤ) ≠ onAxisPoint hd m := by
    rw [← onAxisPoint_zero hd]; exact onAxisPoint_ne hd (by omega)
  have h0n : (0 : Fin d → ℤ) ≠ onAxisPoint hd n := by
    rw [← onAxisPoint_zero hd]; exact onAxisPoint_ne hd (by omega)
  have h0mn : (0 : Fin d → ℤ) ≠ onAxisPoint hd (m + n) := by
    rw [← onAxisPoint_zero hd]; exact onAxisPoint_ne hd (by omega)
  have hmmn : onAxisPoint hd m ≠ onAxisPoint hd (m + n) := onAxisPoint_ne hd (by omega)
  -- GKS-II on `A = {me₁, 0}`, `B = {me₁, (m+n)e₁}`; `A ∆ B = {(m+n)e₁, 0}`.
  have hgks := correlationInfinite_latticeGraph_cubicExhaustion_gks_second d
    (⟨J, 0, β⟩ : IsingParams ℝ) hf {onAxisPoint hd m, (0 : Fin d → ℤ)}
    {onAxisPoint hd m, onAxisPoint hd (m + n)}
  rw [symmDiff_pair_pair_of_ne h0m.symm hmmn h0mn.symm] at hgks
  -- translation: `⟨φ_{me₁}φ_{(m+n)e₁}⟩ = ⟨φ₀φ_{ne₁}⟩`.
  have htrans : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {onAxisPoint hd m, onAxisPoint hd (m + n)}
      = Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), onAxisPoint hd n} := by
    have h := correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset d (onAxisPoint hd m)
      (⟨J, 0, β⟩ : IsingParams ℝ) hf {(0 : Fin d → ℤ), onAxisPoint hd n}
    rw [vaddFinset_pair,
      show onAxisPoint hd m +ᵥ (0 : Fin d → ℤ) = onAxisPoint hd m by rw [vadd_eq_add, add_zero],
      show onAxisPoint hd m +ᵥ onAxisPoint hd n = onAxisPoint hd (m + n) by
        rw [vadd_eq_add]; exact onAxisPoint_add hd m n] at h
    exact h
  rw [Finset.pair_comm (onAxisPoint hd m) (0 : Fin d → ℤ), htrans,
    Finset.pair_comm (onAxisPoint hd (m + n)) (0 : Fin d → ℤ)] at hgks
  -- positivity of the three pair correlations.
  have hpm : 0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), onAxisPoint hd m} :=
    correlationInfinite_pos_of_betaJ_pos_pair hβ hβJ h0m
  have hpn : 0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), onAxisPoint hd n} :=
    correlationInfinite_pos_of_betaJ_pos_pair hβ hβJ h0n
  -- `−log` of the supermultiplicative inequality is subadditivity.
  have hlog := Real.log_le_log (mul_pos hpm hpn) hgks
  rw [Real.log_mul (ne_of_gt hpm) (ne_of_gt hpn)] at hlog
  unfold onAxisLogCorr
  linarith

/-- **Lower-boundedness of the normalised on-axis log-correlation**: `range (n ↦ u(n)/n)` is bounded
below by `0` (each term is `≥ 0` for `n ≥ 1`, and `u(0)/0 = 0`). -/
theorem onAxisLogCorr_div_bddBelow (hd : 0 < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    BddBelow (Set.range fun n : ℕ => onAxisLogCorr hd J β n / n) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; norm_num
  · exact div_nonneg (onAxisLogCorr_nonneg hd hJ hβ n) (Nat.cast_nonneg n)

/-- **On-axis inverse correlation length** (GJ §17.5 / FV §3.7.3): the Fekete limit
`infₙ (−log⟨φ₀ φ_{n e₁}⟩_∞)/n` of the subadditive on-axis log-correlation sequence.  This is the
(well-defined) inverse correlation length along the first coordinate axis. -/
noncomputable def onAxisInverseCorrelationLength (hd : 0 < d) {J β : ℝ}
    (hJ : 0 < J) (hβ : 0 < β) : ℝ :=
  (onAxisLogCorr_subadditive hd hJ hβ).lim

/-- **Existence of the on-axis inverse correlation length as a limit** (Fekete's lemma): the
normalised on-axis log-correlation `u(n)/n` converges to `onAxisInverseCorrelationLength`.  This
upgrades the on-axis decay rate from a `liminf` (#4389) to a genuine `lim`. -/
theorem onAxisLogCorr_div_tendsto (hd : 0 < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    Filter.Tendsto (fun n : ℕ => onAxisLogCorr hd J β n / n) Filter.atTop
      (nhds (onAxisInverseCorrelationLength hd hJ hβ)) :=
  (onAxisLogCorr_subadditive hd hJ hβ).tendsto_lim (onAxisLogCorr_div_bddBelow hd hJ hβ)

/-- **The on-axis inverse correlation length is bounded by `−log tanh(βJ)`** (consistency with the
unconditional mass upper bound): each `u(k)/k ≤ −log tanh(βJ)` via the tanh path lower bound
`⟨φ₀φ_{k e₁}⟩ ≥ tanh(βJ)^k`, so the limit satisfies the same bound.  Hence
`onAxisInverseCorrelationLength ≤ −log tanh(βJ)`, the (sharper, true-limit) refinement of
`latticeMass ≤ ofReal(−log tanh(βJ))`. -/
theorem onAxisInverseCorrelationLength_le_neg_log_tanh (hd : 0 < d) {J β : ℝ}
    (hJ : 0 < J) (hβ : 0 < β) :
    onAxisInverseCorrelationLength hd hJ hβ ≤ -Real.log (Real.tanh (β * J)) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hJ)) (Real.cosh_pos _)
  refine le_of_tendsto (onAxisLogCorr_div_tendsto hd hJ hβ) ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have h0k : (0 : Fin d → ℤ) ≠ onAxisPoint hd k := by
    rw [← onAxisPoint_zero hd]; exact onAxisPoint_ne hd (by omega)
  -- `⟨φ₀φ_{k e₁}⟩ = twoPointFunction (k e₁) ≥ tanh(βJ)^k`.
  have hg_eq : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), onAxisPoint hd k}
      = twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) (onAxisPoint hd k) := by
    rw [correlationInfinite_latticeGraph_pair_eq_twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ)
      hf 0 (onAxisPoint hd k), sub_zero]
  have hdist : latticeDistance d 0 (onAxisPoint hd k) = k := by
    rw [onAxisPoint, latticeDistance_zero_single hd (k : ℤ)]; simp
  have hgge : Real.tanh (β * J) ^ k
      ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), onAxisPoint hd k} := by
    rw [hg_eq]
    have hge := twoPointFunction_ge_tanh_betaJ_pow_dist hJ.le hβ (Ne.symm h0k)
    rwa [hdist] at hge
  have hcorr_pos : 0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), onAxisPoint hd k} :=
    correlationInfinite_pos_of_betaJ_pos_pair hβ (mul_pos hβ hJ) h0k
  have hlog : -Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), onAxisPoint hd k})
      ≤ (k : ℝ) * (-Real.log (Real.tanh (β * J))) := by
    have h1 := Real.log_le_log (pow_pos htanh_pos k) hgge
    rw [Real.log_pow] at h1
    nlinarith [h1]
  rw [onAxisLogCorr, div_le_iff₀ hkpos]
  nlinarith [hlog]

/-- **On-axis abscissa upper bound for the true mass, as a true limit** (GJ §17.5 Thm 17.5.1, toward
#4386): `latticeMass(σ) ≤ ofReal(onAxisInverseCorrelationLength)`.  Combines the on-axis abscissa
bound #4389 (`latticeMass ≤ ofReal(liminf_k τ(k))`) with the Fekete limit `τ(k) → onAxis…Length`
(so the `liminf` equals the limit).  This is the sharpened, well-defined-correlation-length form of
the on-axis upper bound; the matching lower bound (sharpness / continuity) is the Ornstein–Zernike /
§18 content (#4386). -/
theorem latticeMass_le_ofReal_onAxisInverseCorrelationLength (hd : 0 < d) {J β : ℝ}
    (hJ : 0 < J) (hβ : 0 < β) :
    latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ ENNReal.ofReal (onAxisInverseCorrelationLength hd hJ hβ) := by
  -- the #4389 rate sequence `τ(k) = u(k+1)/(k+1)` is the `(·+1)`-shift of `n ↦ u(n)/n`, so it
  -- tends to the Fekete limit; hence its `liminf` equals the limit.
  have hτ_tendsto : Filter.Tendsto (fun k : ℕ =>
      (-Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), Pi.single (⟨0, hd⟩ : Fin d) ((k : ℤ) + 1)}))
        / ((k : ℝ) + 1)) Filter.atTop
      (nhds (onAxisInverseCorrelationLength hd hJ hβ)) := by
    have h := (onAxisLogCorr_div_tendsto hd hJ hβ).comp (tendsto_add_atTop_nat 1)
    refine h.congr (fun k => ?_)
    simp only [Function.comp_apply, onAxisLogCorr, onAxisPoint, Nat.cast_add, Nat.cast_one]
  have hliminf := hτ_tendsto.liminf_eq
  calc latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ ENNReal.ofReal (Filter.liminf (fun k : ℕ =>
          (-Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), Pi.single (⟨0, hd⟩ : Fin d) ((k : ℤ) + 1)}))
            / ((k : ℝ) + 1)) Filter.atTop) :=
        latticeMass_le_ofReal_liminf_onAxisRate hd hJ hβ
    _ = ENNReal.ofReal (onAxisInverseCorrelationLength hd hJ hβ) := by rw [hliminf]

end Ambient
end IsingModel
