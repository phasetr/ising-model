import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityLatticeMassDirectionalAbscissa

/-!
# GJ §17.5 eq. (17.5.1) — directional inverse correlation length exists as a Fekete limit

The all-directions generalization of the on-axis Fekete limit
(`onAxisInverseCorrelationLength`, #4391): for **any** nonzero lattice direction `v ≠ 0`, the
directional log-correlation sequence `a_v(n) = −log⟨φ₀ φ_{n·v}⟩_∞` is subadditive (GKS-II
supermultiplicativity along the ray `ℕ·v` + translation invariance), bounded below by `0`, so by
Fekete's lemma `a_v(n)/n → infₙ a_v(n)/n`; dividing by the per-step lattice distance `d(0,v)` gives
the **directional inverse correlation length**

`directionalInverseCorrelationLength v := (infₙ a_v(n)/n) / d(0,v)`,

a genuine limit (not merely a `liminf`).  This upgrades the directional abscissa upper bound #4390
from a `liminf` to a `lim`, and assembling over all directions gives the sharp
`latticeMass(σ) ≤ ⨅_{v≠0} ofReal(directionalInverseCorrelationLength v)` — the full directional
abscissa **upper** characterization of the true mass, as true limits.  The on-axis case #4391 is
`v = e₁`.  This establishes existence/well-definedness of the GJ eq. (17.5.1) limit in every lattice
direction.  The matching **lower** bound `latticeMass ≥ ⨅_{v≠0} ofReal(directional v)` — hence the
equality `latticeMass = ⨅_{v≠0} ofReal(directional v)` (GJ eq. (17.5.1) mass characterization) — is
now proved *elementarily* in `MassContinuityLatticeMassDirectionalLowerBound.lean` (the Fekete
infimum is `≤` its `n=1` term, giving uniform decay); it does **not**
need the Ornstein–Zernike machinery.  What genuinely remains open (#4386) is the OZ *exact closed-
form rate*, a correlation *lower* bound / prefactor, and the lower-semicontinuous half of the
continuity Theorem 17.5.1 (the usc half follows from the envelope upper-semicontinuity).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5 eq. (17.5.1) (mass as a limit) and Theorem 17.5.1
  (continuity), §18, pp.~311--312.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3 (correlation length).
-/

namespace IsingModel
namespace Ambient

open Set Filter Topology

variable {d : ℕ}

/-- **Directional log-correlation sequence** `a_v(n) = −log⟨φ₀ φ_{n·v}⟩_∞` along the ray `ℕ·v`. -/
noncomputable def directionalLogCorr (J β : ℝ) (v : Fin d → ℤ) (n : ℕ) : ℝ :=
  -Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), n • v})

/-- **Ray points are nonzero**: for `v ≠ 0` and `n ≥ 1`, `n · v ≠ 0` (its lattice distance to the
origin is `n · d(0,v) ≥ 1`). -/
theorem nsmul_ne_zero_of_dir {v : Fin d → ℤ} (hv : v ≠ 0) {n : ℕ} (hn : 0 < n) :
    (0 : Fin d → ℤ) ≠ n • v := by
  have hD1 : 1 ≤ latticeDistance d 0 v :=
    Nat.one_le_iff_ne_zero.mpr (fun h => hv ((latticeDistance_eq_zero_iff d 0 v).mp h).symm)
  intro h
  have hdist : latticeDistance d 0 (n • v) = 0 := by rw [← h]; simp
  rw [latticeDistance_zero_nsmul] at hdist
  have : 0 < n * latticeDistance d 0 v := Nat.mul_pos hn (by omega)
  omega

/-- **Nonnegativity of the directional log-correlation**: `0 ≤ a_v(n)` (ferromagnetic correlations
lie in `[0,1]`, so their `log` is `≤ 0`). -/
theorem directionalLogCorr_nonneg {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) (v : Fin d → ℤ) (n : ℕ) :
    0 ≤ directionalLogCorr J β v n := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  unfold directionalLogCorr
  have hnn := correlationInfinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf {(0 : Fin d → ℤ), n • v}
  have hle := correlationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), n • v}
  have hlog := Real.log_nonpos hnn hle
  linarith

/-- **Subadditivity of the directional log-correlation** (GKS-II supermultiplicativity along `ℕ·v` +
translation invariance): `a_v(m+n) ≤ a_v(m) + a_v(n)`.  For `m,n ≥ 1`, GKS-II gives
`⟨φ₀φ_{mv}⟩·⟨φ_{mv}φ_{(m+n)v}⟩ ≤ ⟨φ₀φ_{(m+n)v}⟩` (`{mv,0} ∆ {mv,(m+n)v} = {(m+n)v,0}`), translation
turns the middle factor into `⟨φ₀φ_{nv}⟩`, and `−log` of the positive supermultiplicative inequality
is subadditivity; the `m=0`/`n=0` cases reduce to `0 ≤ a_v(0)`. -/
theorem directionalLogCorr_subadditive {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {v : Fin d → ℤ}
    (hv : v ≠ 0) : Subadditive (directionalLogCorr J β v) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have hβJ : 0 < β * J := mul_pos hβ hJ
  intro m n
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simpa using directionalLogCorr_nonneg hJ hβ v 0
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 := directionalLogCorr_nonneg hJ hβ v 0
    have : directionalLogCorr J β v m
        ≤ directionalLogCorr J β v m + directionalLogCorr J β v 0 := by linarith
    simpa using this
  -- `m, n ≥ 1`: distinctness of the three ray points.
  have h0m : (0 : Fin d → ℤ) ≠ m • v := nsmul_ne_zero_of_dir hv hm
  have h0n : (0 : Fin d → ℤ) ≠ n • v := nsmul_ne_zero_of_dir hv hn
  have h0mn : (0 : Fin d → ℤ) ≠ (m + n) • v := nsmul_ne_zero_of_dir hv (by omega)
  have hmmn : m • v ≠ (m + n) • v := by
    intro h
    rw [add_nsmul] at h
    have hz : n • v = 0 := by
      have h2 : m • v + n • v = m • v + 0 := by rw [add_zero]; exact h.symm
      exact add_left_cancel h2
    exact h0n hz.symm
  -- GKS-II on `A = {mv, 0}`, `B = {mv, (m+n)v}`; `A ∆ B = {(m+n)v, 0}`.
  have hgks := correlationInfinite_latticeGraph_cubicExhaustion_gks_second d
    (⟨J, 0, β⟩ : IsingParams ℝ) hf {m • v, (0 : Fin d → ℤ)} {m • v, (m + n) • v}
  rw [symmDiff_pair_pair_of_ne h0m.symm hmmn h0mn.symm] at hgks
  -- translation: `⟨φ_{mv}φ_{(m+n)v}⟩ = ⟨φ₀φ_{nv}⟩`.
  have htrans : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {m • v, (m + n) • v}
      = Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), n • v} := by
    have h := correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset d (m • v)
      (⟨J, 0, β⟩ : IsingParams ℝ) hf {(0 : Fin d → ℤ), n • v}
    rw [vaddFinset_pair,
      show m • v +ᵥ (0 : Fin d → ℤ) = m • v by rw [vadd_eq_add, add_zero],
      show m • v +ᵥ n • v = (m + n) • v by rw [vadd_eq_add, ← add_nsmul]] at h
    exact h
  rw [Finset.pair_comm (m • v) (0 : Fin d → ℤ), htrans,
    Finset.pair_comm ((m + n) • v) (0 : Fin d → ℤ)] at hgks
  -- positivity of the three pair correlations.
  have hpm : 0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), m • v} :=
    correlationInfinite_pos_of_betaJ_pos_pair hβ hβJ h0m
  have hpn : 0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), n • v} :=
    correlationInfinite_pos_of_betaJ_pos_pair hβ hβJ h0n
  -- `−log` of the supermultiplicative inequality is subadditivity.
  have hlog := Real.log_le_log (mul_pos hpm hpn) hgks
  rw [Real.log_mul (ne_of_gt hpm) (ne_of_gt hpn)] at hlog
  unfold directionalLogCorr
  linarith

/-- **Lower-boundedness of the normalised directional log-correlation**: `range (n ↦ a_v(n)/n)` is
bounded below by `0`. -/
theorem directionalLogCorr_div_bddBelow {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) (v : Fin d → ℤ) :
    BddBelow (Set.range fun n : ℕ => directionalLogCorr J β v n / n) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; norm_num
  · exact div_nonneg (directionalLogCorr_nonneg hJ hβ v n) (Nat.cast_nonneg n)

/-- **Directional inverse correlation length** (GJ §17.5 eq. (17.5.1) / FV §3.7.3): the Fekete limit
`infₙ a_v(n)/n` of the subadditive directional log-correlation, divided by the per-step lattice
distance `d(0,v)`.  This is the (well-defined) inverse correlation length along direction `v`. -/
noncomputable def directionalInverseCorrelationLength {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    {v : Fin d → ℤ} (hv : v ≠ 0) : ℝ :=
  (directionalLogCorr_subadditive hJ hβ hv).lim / (latticeDistance d 0 v : ℝ)

/-- **Existence of the directional inverse correlation length as a limit** (Fekete): the normalised
directional log-correlation `a_v(n)/n` converges to `(directionalInverseCorrelationLength v) ·
d(0,v)` (i.e. to the Fekete limit `infₙ a_v(n)/n`). -/
theorem directionalLogCorr_div_tendsto {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {v : Fin d → ℤ}
    (hv : v ≠ 0) :
    Filter.Tendsto (fun n : ℕ => directionalLogCorr J β v n / n) Filter.atTop
      (nhds (directionalLogCorr_subadditive hJ hβ hv).lim) :=
  (directionalLogCorr_subadditive hJ hβ hv).tendsto_lim
    (directionalLogCorr_div_bddBelow hJ hβ v)

/-- **Directional abscissa upper bound for the true mass, as a true limit** (GJ §17.5 eq. (17.5.1)
limit existence, toward Thm 17.5.1 / #4386): `latticeMass(σ) ≤ ofReal(directionalInverseCorrelation…
Length v)`.  Combines the directional abscissa bound #4390 (`latticeMass ≤ ofReal(liminf_k τ_v(k))`)
with the Fekete limit: `τ_v(k) = a_v(k+1)/((k+1)·d(0,v))` is the `(·+1)`-shift of `a_v(n)/n` divided
by `d(0,v)`, so its `liminf` equals `(infₙ a_v(n)/n)/d(0,v)`, i.e.
`directionalInverseCorrelationLength`. -/
theorem latticeMass_le_ofReal_directionalInverseCorrelationLength {J β : ℝ} (hJ : 0 < J)
    (hβ : 0 < β) {v : Fin d → ℤ} (hv : v ≠ 0) :
    latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ ENNReal.ofReal (directionalInverseCorrelationLength hJ hβ hv) := by
  have hτ_tendsto : Filter.Tendsto (fun k : ℕ =>
      (-Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), (k + 1) • v}))
        / (((k : ℝ) + 1) * (latticeDistance d 0 v : ℝ))) Filter.atTop
      (nhds (directionalInverseCorrelationLength hJ hβ hv)) := by
    have h := ((directionalLogCorr_div_tendsto hJ hβ hv).comp (tendsto_add_atTop_nat 1)).div_const
      (latticeDistance d 0 v : ℝ)
    refine h.congr (fun k => ?_)
    simp only [Function.comp_apply, directionalLogCorr, Nat.cast_add, Nat.cast_one, div_div]
  have hliminf := hτ_tendsto.liminf_eq
  calc latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ ENNReal.ofReal (Filter.liminf (fun k : ℕ =>
          (-Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), (k + 1) • v}))
            / (((k : ℝ) + 1) * (latticeDistance d 0 v : ℝ))) Filter.atTop) :=
        latticeMass_le_ofReal_liminf_directionalRate hJ hβ hv
    _ = ENNReal.ofReal (directionalInverseCorrelationLength hJ hβ hv) := by rw [hliminf]

/-- **Directional abscissa upper characterization of the true mass** (GJ §17.5 eq. (17.5.1), toward
Thm 17.5.1 / #4386): `latticeMass(σ) ≤ ⨅_{v≠0} ofReal(directionalInverseCorrelationLength v)`.  The
true mass is bounded by the infimum over all lattice directions of the directional inverse
correlation length — the full directional abscissa **upper** half, as true limits.  Direct from the
per-direction bound (`le_iInf`); the matching lower bound / sharpness is the Ornstein–Zernike / §18
content (#4386). -/
theorem latticeMass_le_iInf_ofReal_directionalInverseCorrelationLength {J β : ℝ} (hJ : 0 < J)
    (hβ : 0 < β) :
    latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ ⨅ v : {v : Fin d → ℤ // v ≠ 0},
          ENNReal.ofReal (directionalInverseCorrelationLength hJ hβ v.2) :=
  le_iInf fun v => latticeMass_le_ofReal_directionalInverseCorrelationLength hJ hβ v.2

end Ambient
end IsingModel
