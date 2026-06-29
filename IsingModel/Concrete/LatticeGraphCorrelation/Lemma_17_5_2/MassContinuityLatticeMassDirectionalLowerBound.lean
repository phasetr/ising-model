import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDirectionalCorrelationLength
import IsingModel.Concrete.LatticeGraphCorrelation.SharpLatticeMassLowerBound
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationVadd

/-!
# GJ §17.5 eq. (17.5.1) — the true mass equals the directional inverse-correlation-length infimum

The directional abscissa **UPPER** characterization
`latticeMass ≤ ⨅_{v≠0} ofReal(directionalInverseCorrelationLength v)`
(`latticeMass_le_iInf_ofReal_directionalInverseCorrelationLength`) was already established as a true
Fekete limit.  Here we prove the matching **LOWER** bound, hence the equality

`latticeMass = ⨅_{v≠0} ofReal(directionalInverseCorrelationLength v)`     (GJ eq. (17.5.1))

— the true mass is *exactly* the infimum over lattice directions of the directional inverse
correlation length.

The lower bound is **elementary** (no Ornstein–Zernike machinery): for the direction `v = x` itself
at step `n = 1`, the Fekete limit (an infimum over `n ≥ 1`) is `≤` its first term, so

`directionalInverseCorrelationLength(x) · d(0,x) = (Subadditive.lim a_x) ≤ a_x(1) = −log⟨φ₀ φ_x⟩`,

i.e. `⟨φ₀ φ_x⟩ ≤ exp(−directionalInverseCorrelationLength(x) · d(0,x))`.  Bounding
`directionalInverseCorrelationLength(x)` below by the direction-infimum `m∞` and reducing a general
pair `{i,j}` to the origin pair `{0, j−i}` by translation invariance gives **uniform** exponential
decay (single prefactor `C = 1`, all pairs) at rate `m∞`, so `ofReal m∞ ≤ latticeMass`.

## Scope

This pins the true mass to the directional infimum as a structural identity.  It does **not** supply
the Ornstein–Zernike *exact rate* in closed form (`directionalInverseCorrelationLength` is an
abstract Fekete limit, only pinned to `[−log(2d·tanh βJ), −log tanh βJ]`), nor a correlation *lower*
bound / OZ prefactor.  It does, with the upper-semicontinuity of the envelope
(`iInf_directionalInverseCorrelationLength_upperSemicontinuousOn_window`), give the **upper-
semicontinuity of `latticeMass`** — the usc half of GJ Theorem 17.5.1 continuity (#4386); the lower-
semicontinuous half remains open.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5 eq. (17.5.1) / Theorem 17.5.1, pp.~311--312.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel
namespace Ambient

open Set

variable {d : ℕ}

/-- **Nonnegativity of the directional inverse correlation length**: `0 ≤
directionalInverseCorrelationLength v`.  The Fekete limit is an infimum of the nonnegative
normalised log-correlations `a_v(n)/n ≥ 0`, and the per-step distance `d(0,v)` is positive. -/
theorem directionalInverseCorrelationLength_nonneg {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    {v : Fin d → ℤ} (hv : v ≠ 0) :
    0 ≤ directionalInverseCorrelationLength hJ hβ hv := by
  unfold directionalInverseCorrelationLength
  apply div_nonneg _ (Nat.cast_nonneg _)
  rw [Subadditive.lim]
  apply Real.sInf_nonneg
  rintro x ⟨n, _, rfl⟩
  exact div_nonneg (directionalLogCorr_nonneg hJ hβ v n) (Nat.cast_nonneg _)

/-- **Origin-pair decay at the directional rate** (the elementary crux): for `v ≠ 0`,
`⟨φ₀ φ_v⟩_∞ ≤ exp(−directionalInverseCorrelationLength(v) · d(0,v))`.  The Fekete limit (an infimum
over `n ≥ 1`) is `≤` its `n = 1` term `a_v(1) = −log⟨φ₀ φ_v⟩`, and the length times `d(0,v)` equals
that limit. -/
theorem correlationInfinite_origin_le_exp_neg_directionalInverseCorrelationLength {J β : ℝ}
    (hJ : 0 < J) (hβ : 0 < β) {v : Fin d → ℤ} (hv : v ≠ 0) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), v}
      ≤ Real.exp (-directionalInverseCorrelationLength hJ hβ hv * (latticeDistance d 0 v : ℝ)) := by
  have hd0 : (0 : ℝ) < (latticeDistance d 0 v : ℝ) := by
    have hne : latticeDistance d 0 v ≠ 0 := fun h =>
      hv (((latticeDistance_eq_zero_iff d 0 v).mp h).symm)
    exact_mod_cast Nat.pos_of_ne_zero hne
  have hcorr_pos : 0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), v} :=
    correlationInfinite_pos_of_betaJ_pos_pair hβ (mul_pos hβ hJ) (Ne.symm hv)
  -- `directional · d(0,v) = Subadditive.lim ≤ a_v(1) = −log⟨φ₀ φ_v⟩`.
  have hlim_le : (directionalLogCorr_subadditive hJ hβ hv).lim ≤ directionalLogCorr J β v 1 := by
    have h := (directionalLogCorr_subadditive hJ hβ hv).lim_le_div
      (directionalLogCorr_div_bddBelow hJ hβ v) (n := 1) one_ne_zero
    simpa using h
  have hmul : directionalInverseCorrelationLength hJ hβ hv * (latticeDistance d 0 v : ℝ)
      = (directionalLogCorr_subadditive hJ hβ hv).lim := by
    unfold directionalInverseCorrelationLength
    exact div_mul_cancel₀ _ hd0.ne'
  have ha1 : directionalLogCorr J β v 1
      = -Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), v}) := by
    unfold directionalLogCorr
    rw [one_nsmul]
  have hkey : directionalInverseCorrelationLength hJ hβ hv * (latticeDistance d 0 v : ℝ)
      ≤ -Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), v}) := by
    rw [hmul, ← ha1]; exact hlim_le
  -- exponentiate: `⟨φ₀φ_v⟩ = exp(log⟨φ₀φ_v⟩) ≤ exp(−directional·d)`.
  rw [neg_mul]
  calc Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), v}
      = Real.exp (Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), v})) :=
        (Real.exp_log hcorr_pos).symm
    _ ≤ Real.exp (-(directionalInverseCorrelationLength hJ hβ hv
          * (latticeDistance d 0 v : ℝ))) := by
        apply Real.exp_le_exp.mpr
        linarith [hkey]

/-- **Translation invariance of the lattice distance**: `d(i,j) = d(0, j − i)`
(`∑ |iₖ − jₖ| = ∑ |0 − (j−i)ₖ|`, since `|iₖ − jₖ| = |(j−i)ₖ|`). -/
theorem latticeDistance_eq_latticeDistance_zero_sub (d : ℕ) (i j : Fin d → ℤ) :
    latticeDistance d i j = latticeDistance d 0 (j - i) := by
  unfold latticeDistance
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Pi.zero_apply, Pi.sub_apply, zero_sub, Int.natAbs_neg]
  omega

/-- **The directional inverse-correlation-length infimum over all nonzero directions** `m∞ :=
⨅_{v≠0} directionalInverseCorrelationLength v`. -/
noncomputable def directionalInverseCorrelationLengthInf {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (d : ℕ) : ℝ :=
  ⨅ v : {v : Fin d → ℤ // v ≠ 0}, directionalInverseCorrelationLength hJ hβ v.2

/-- **A nonzero lattice vector exists** for `d ≥ 1`: `Pi.single ⟨0,hd⟩ 1 ≠ 0`. -/
instance nonempty_ne_zero_subtype {d : ℕ} [hd : NeZero d] :
    Nonempty {v : Fin d → ℤ // v ≠ 0} :=
  ⟨⟨Pi.single (⟨0, Nat.pos_of_ne_zero hd.1⟩ : Fin d) (1 : ℤ), by
    intro h
    have := congrFun h (⟨0, Nat.pos_of_ne_zero hd.1⟩ : Fin d)
    rw [Pi.single_eq_same, Pi.zero_apply] at this
    exact one_ne_zero this⟩⟩

/-- **Boundedness below of the directional inverse correlation lengths** (by `0`). -/
theorem directionalInverseCorrelationLength_bddBelow {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) (d : ℕ) :
    BddBelow (Set.range fun v : {v : Fin d → ℤ // v ≠ 0} =>
      directionalInverseCorrelationLength hJ hβ v.2) := by
  refine ⟨0, ?_⟩
  rintro x ⟨v, rfl⟩
  exact directionalInverseCorrelationLength_nonneg hJ hβ v.2

/-- **Nonnegativity of the directional infimum** `0 ≤ m∞` (`d ≥ 1`). -/
theorem directionalInverseCorrelationLengthInf_nonneg {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    {d : ℕ} (hd : 1 ≤ d) : 0 ≤ directionalInverseCorrelationLengthInf hJ hβ d := by
  haveI : NeZero d := ⟨Nat.one_le_iff_ne_zero.mp hd⟩
  exact le_ciInf fun v => directionalInverseCorrelationLength_nonneg hJ hβ v.2

/-- **Uniform exponential decay at the directional-infimum rate**: `HasExponentialDecay` holds at
rate `m∞` with prefactor `C = 1`.  For each pair `i ≠ j`, translation reduces `⟨φ_i φ_j⟩` to the
origin pair `⟨φ₀ φ_{j−i}⟩ ≤ exp(−directional(j−i)·d(0,j−i)) ≤ exp(−m∞·d(i,j))`. -/
theorem hasExponentialDecay_directionalInverseCorrelationLengthInf {J β : ℝ} (hJ : 0 < J)
    (hβ : 0 < β) (d : ℕ) :
    HasExponentialDecay d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      (directionalInverseCorrelationLengthInf hJ hβ d) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  refine ⟨1, zero_le_one, fun i j hij => ?_⟩
  have hvne : (j - i) ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
  -- reduce the truncated 2-point function to the origin correlation.
  rw [truncated2Infinite_h_zero (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β i j]
  rw [abs_of_nonneg (correlationInfinite_nonneg_of_hβJ (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) (mul_pos hβ hJ).le {i, j})]
  -- `⟨φ_i φ_j⟩ = ⟨φ₀ φ_{j−i}⟩`.
  have htrans : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      = Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), j - i} := by
    have h := correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset d i
      (⟨J, 0, β⟩ : IsingParams ℝ) hf {(0 : Fin d → ℤ), j - i}
    rw [vaddFinset_pair,
      show i +ᵥ (0 : Fin d → ℤ) = i by rw [vadd_eq_add, add_zero],
      show i +ᵥ (j - i) = j by rw [vadd_eq_add]; ring] at h
    exact h
  rw [htrans, one_mul, latticeDistance_eq_latticeDistance_zero_sub d i j]
  -- bound by the directional rate at `v = j − i`, then by `m∞`.
  have hbound := correlationInfinite_origin_le_exp_neg_directionalInverseCorrelationLength
    hJ hβ hvne
  refine hbound.trans ?_
  apply Real.exp_le_exp.mpr
  have hge : directionalInverseCorrelationLengthInf hJ hβ d
      ≤ directionalInverseCorrelationLength hJ hβ hvne := by
    have := ciInf_le (directionalInverseCorrelationLength_bddBelow hJ hβ d)
      (⟨j - i, hvne⟩ : {v : Fin d → ℤ // v ≠ 0})
    simpa using this
  have hdist_nonneg : (0 : ℝ) ≤ (latticeDistance d 0 (j - i) : ℝ) := Nat.cast_nonneg _
  nlinarith [hge, hdist_nonneg]

/-- **Directional-infimum LOWER bound for the true mass**: `ofReal(m∞) ≤ latticeMass`, where `m∞ =
⨅_{v≠0} directionalInverseCorrelationLength v` (`d ≥ 1`).  Immediate from uniform exponential decay
at rate `m∞`. -/
theorem ofReal_directionalInverseCorrelationLengthInf_le_latticeMass {J β : ℝ} (hJ : 0 < J)
    (hβ : 0 < β) {d : ℕ} (hd : 1 ≤ d) :
    ENNReal.ofReal (directionalInverseCorrelationLengthInf hJ hβ d)
      ≤ latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_of_HasExponentialDecay (directionalInverseCorrelationLengthInf_nonneg hJ hβ hd)
    (hasExponentialDecay_directionalInverseCorrelationLengthInf hJ hβ d)

/-- **GJ eq. (17.5.1): the true mass equals the directional inverse-correlation-length infimum**
(`d ≥ 1`):

`latticeMass = ⨅_{v≠0} ofReal(directionalInverseCorrelationLength v)`.

Combines the directional abscissa UPPER characterization
(`latticeMass_le_iInf_ofReal_directionalInverseCorrelationLength`) with the elementary LOWER bound
`ofReal m∞ ≤ latticeMass`, using `ENNReal.ofReal_iInf` to commute `ofReal` through the infimum.  The
true mass is exactly the slowest directional inverse correlation length — the GJ eq. (17.5.1) mass
characterization. -/
theorem latticeMass_eq_iInf_ofReal_directionalInverseCorrelationLength {J β : ℝ} (hJ : 0 < J)
    (hβ : 0 < β) {d : ℕ} (hd : 1 ≤ d) :
    latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      = ⨅ v : {v : Fin d → ℤ // v ≠ 0},
          ENNReal.ofReal (directionalInverseCorrelationLength hJ hβ v.2) := by
  haveI : NeZero d := ⟨Nat.one_le_iff_ne_zero.mp hd⟩
  refine le_antisymm (latticeMass_le_iInf_ofReal_directionalInverseCorrelationLength hJ hβ) ?_
  rw [← ENNReal.ofReal_iInf]
  exact ofReal_directionalInverseCorrelationLengthInf_le_latticeMass hJ hβ hd

end Ambient
end IsingModel
