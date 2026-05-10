import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature
import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Inequalities.HighTemp
import IsingModel.LatticeExpSum
import IsingModel.PseudoMass

/-!
# Lattice-mass pseudo-mass transfer bridges at ℤ^d

This module contains the concrete §17.1 / §17.5 bridge layer split from the
legacy `Inequalities` module: Step 127 product summability bounds, critical
inverse temperature wrappers, high-temperature decay transfer to arbitrary
exhaustions, pseudo-mass comparison bridges, and below-critical cluster /
summability consequences.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Step 127: Lebowitz–exponential product bound (GJ §17.5 PR N+2) -/

/-- Uniform upper bound on each factor under exponential decay.

Under `HasExponentialDecay` with constant `C` and rate `α`, each
`truncated2Infinite(i, z)` is bounded uniformly for ALL `z` (including `i = z`)
by `(C + 1) * exp(-α/2 * d(i, z))`.

At `i = z`: uses `truncated2Infinite_le_one` (≤ 1 ≤ C+1).
At `i ≠ z`: uses the decay bound `C * exp(-α*d) ≤ (C+1) * exp(-α/2 * d)` for
`d ≥ 0` (since `-α*d ≤ -α/2*d` and `C ≤ C+1`). -/
private lemma truncated2Infinite_le_hDecay_uniform
    {d : ℕ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hbound : ∀ i j : Fin d → ℤ, i ≠ j →
        |Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j|
        ≤ C * Real.exp (-α * (latticeDistance d i j : ℝ)))
    (i z : Fin d → ℤ) :
    Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) i z
    ≤ (C + 1) * Real.exp (-(α / 2) * (latticeDistance d i z : ℝ)) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hnn : 0 ≤ Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) i z :=
    Ambient.truncated2Infinite_nonneg (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) hf i z
  rcases eq_or_ne i z with rfl | hiz
  · -- Diagonal: truncated2(i,i) ≤ 1 ≤ (C+1)·1 = (C+1)·exp(-α/2·0)
    have hle1 := Ambient.truncated2Infinite_le_one (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf i i
    simp only [latticeDistance_self, Nat.cast_zero, mul_zero, Real.exp_zero]
    linarith
  · -- Off-diagonal: C·exp(-α·d) ≤ (C+1)·exp(-α/2·d)
    have habs := hbound i z hiz
    rw [abs_of_nonneg hnn] at habs
    have hdist_nn : (0 : ℝ) ≤ latticeDistance d i z := Nat.cast_nonneg _
    calc Ambient.truncated2Infinite _ _ _ i z
        ≤ C * Real.exp (-α * (latticeDistance d i z : ℝ)) := habs
      _ ≤ (C + 1) * Real.exp (-(α / 2) * (latticeDistance d i z : ℝ)) := by
            apply mul_le_mul (le_add_of_nonneg_right one_pos.le)
              (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_nonneg _) (by linarith)

/-- **Summability of the truncated-2 product sum** under exponential decay (Step 127).

Under `HasExponentialDecay d (cubicExhaustion d) (⟨J, 0, β⟩) α`, the sum
`∑_z truncated2Inf(x,z) · truncated2Inf(y,z)` is summable over `ℤ^d`.

Proof: both factors are nonneg (GKS-II) and uniformly bounded by `(C+1)·exp(-α/2·d)`;
the product is bounded by `(C+1)²·exp(-α/2·d(x,z))·exp(-α/2·d(y,z))`; this is
summable by `summable_exp_neg_dist` with rate `α/2`.

**Reference**: GJ §17.5 (applying Lemma 17.5.2 exponential decay). -/
theorem summable_truncated2Infinite_prod_of_hasExponentialDecay
    {d : ℕ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {α : ℝ} (hα : 0 < α)
    (hdecay : HasExponentialDecay d (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) α)
    (x y : Fin d → ℤ) :
    Summable (fun z : Fin d → ℤ =>
        Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z *
        Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) y z) := by
  obtain ⟨C, hC, hbound⟩ := hdecay
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hα2 : 0 < α / 2 := half_pos hα
  refine Summable.of_nonneg_of_le
    (fun z => mul_nonneg (Ambient.truncated2Infinite_nonneg (latticeGraph d)
                            (Ambient.cubicExhaustion d) _ hf x z)
                         (Ambient.truncated2Infinite_nonneg (latticeGraph d)
                            (Ambient.cubicExhaustion d) _ hf y z))
    (fun z => ?_)
    ((summable_exp_neg_dist hα2 d x).mul_left ((C + 1) ^ 2))
  have hx := truncated2Infinite_le_hDecay_uniform hJ hβ hα hC hbound x z
  have hy := truncated2Infinite_le_hDecay_uniform hJ hβ hα hC hbound y z
  have hnn_y := Ambient.truncated2Infinite_nonneg (latticeGraph d)
                  (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf y z
  calc Ambient.truncated2Infinite _ _ _ x z * Ambient.truncated2Infinite _ _ _ y z
      ≤ (C + 1) * Real.exp (-(α / 2) * (latticeDistance d x z : ℝ)) *
        ((C + 1) * Real.exp (-(α / 2) * (latticeDistance d y z : ℝ))) :=
          mul_le_mul hx hy hnn_y (mul_nonneg (by linarith) (Real.exp_nonneg _))
    _ = (C + 1) ^ 2 *
        (Real.exp (-(α / 2) * (latticeDistance d x z : ℝ)) *
         Real.exp (-(α / 2) * (latticeDistance d y z : ℝ))) := by ring
    _ ≤ (C + 1) ^ 2 * Real.exp (-(α / 2) * (latticeDistance d x z : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact mul_le_of_le_one_right (Real.exp_nonneg _)
                (Real.exp_le_one_iff.mpr (by
                  nlinarith [hα2.le, show (0:ℝ) ≤ latticeDistance d y z from Nat.cast_nonneg _]))

/-- **Upper bound on the truncated-2 product tsum** (Step 127).

Under `HasExponentialDecay d (cubicExhaustion d) (⟨J, 0, β⟩) α` with witness constant `C`,
the infinite sum satisfies:
```
∑_z truncated2Inf(x,z) · truncated2Inf(y,z) ≤
  (C+1)² · 2 · C(α/2, d) · exp(-α/4 · d(x,y))
```
where `C(α/2, d) = ∑_z exp(-α/2 · d(0,z))`.

The uniform factor `C+1` absorbs both the off-diagonal decay `C·exp(-α·d)` and the
diagonal bound `≤ 1` (GKS-II), avoiding case analysis. The rate `α/4` comes from
applying `lattice_exp_sum_conv_le` with rate `α/2`.

**Reference**: GJ §17.5, Lemma 17.5.2. -/
theorem tsum_truncated2Infinite_prod_le
    {d : ℕ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hbound : ∀ i j : Fin d → ℤ, i ≠ j →
        |Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j|
        ≤ C * Real.exp (-α * (latticeDistance d i j : ℝ)))
    (x y : Fin d → ℤ) :
    ∑' z : Fin d → ℤ,
        Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z *
        Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) y z
    ≤ (C + 1) ^ 2 * (2 * ∑' z : Fin d → ℤ,
          Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ))) *
        Real.exp (-(α / 2) * (latticeDistance d x y : ℝ) / 2) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hα2 : 0 < α / 2 := half_pos hα
  -- Uniform pointwise bound using C+1
  have hle_prod : ∀ z : Fin d → ℤ,
      Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z *
      Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) y z
      ≤ (C + 1) ^ 2 * (Real.exp (-(α / 2) * (latticeDistance d x z : ℝ)) *
                        Real.exp (-(α / 2) * (latticeDistance d y z : ℝ))) := by
    intro z
    have hx := truncated2Infinite_le_hDecay_uniform hJ hβ hα hC hbound x z
    have hy := truncated2Infinite_le_hDecay_uniform hJ hβ hα hC hbound y z
    have hnn_y := Ambient.truncated2Infinite_nonneg (latticeGraph d)
                    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf y z
    calc Ambient.truncated2Infinite _ _ _ x z * Ambient.truncated2Infinite _ _ _ y z
        ≤ (C + 1) * Real.exp (-(α / 2) * _) * ((C + 1) * Real.exp (-(α / 2) * _)) :=
            mul_le_mul hx hy hnn_y (mul_nonneg (by linarith) (Real.exp_nonneg _))
      _ = (C + 1) ^ 2 * (Real.exp (-(α / 2) * _) * Real.exp (-(α / 2) * _)) := by ring
  -- Summability of the comparison
  have hsumm_conv : Summable (fun z : Fin d → ℤ =>
      Real.exp (-(α / 2) * (latticeDistance d x z : ℝ)) *
      Real.exp (-(α / 2) * (latticeDistance d y z : ℝ))) :=
    Summable.of_nonneg_of_le
      (fun z => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      (fun z => mul_le_of_le_one_right (Real.exp_nonneg _)
                  (Real.exp_le_one_iff.mpr (by
                    nlinarith [hα2.le,
                      show (0:ℝ) ≤ latticeDistance d y z from Nat.cast_nonneg _])))
      (summable_exp_neg_dist hα2 d x)
  have hprod_summable : Summable (fun z : Fin d → ℤ =>
      Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z *
      Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) y z) :=
    Summable.of_nonneg_of_le
      (fun z => mul_nonneg (Ambient.truncated2Infinite_nonneg (latticeGraph d)
                              (Ambient.cubicExhaustion d) _ hf x z)
                           (Ambient.truncated2Infinite_nonneg (latticeGraph d)
                              (Ambient.cubicExhaustion d) _ hf y z))
      hle_prod (hsumm_conv.mul_left _)
  -- Main calc
  calc ∑' z, Ambient.truncated2Infinite _ _ _ x z * Ambient.truncated2Infinite _ _ _ y z
      ≤ ∑' z, (C + 1) ^ 2 * (Real.exp (-(α / 2) * _) * Real.exp (-(α / 2) * _)) :=
          hprod_summable.tsum_le_tsum hle_prod (hsumm_conv.mul_left _)
    _ = (C + 1) ^ 2 * ∑' z, Real.exp (-(α / 2) * _) * Real.exp (-(α / 2) * _) :=
          tsum_mul_left
    _ ≤ (C + 1) ^ 2 * (2 * ∑' z : Fin d → ℤ,
            Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ))) *
          Real.exp (-(α / 2) * (latticeDistance d x y : ℝ) / 2) := by
          have hconv := lattice_exp_sum_conv_le hα2 d x y
          calc (C + 1) ^ 2 * ∑' z : Fin d → ℤ,
                  Real.exp (-(α / 2) * (latticeDistance d x z : ℝ)) *
                  Real.exp (-(α / 2) * (latticeDistance d y z : ℝ))
              ≤ (C + 1) ^ 2 * (2 * (∑' z : Fin d → ℤ,
                    Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ))) *
                  Real.exp (-(α / 2) * (latticeDistance d x y : ℝ) / 2)) :=
                  mul_le_mul_of_nonneg_left hconv (sq_nonneg _)
            _ = (C + 1) ^ 2 * (2 * ∑' z : Fin d → ℤ,
                    Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ))) *
                Real.exp (-(α / 2) * (latticeDistance d x y : ℝ) / 2) := by ring

/-! ## §17.1 Critical inverse temperature -/

/-- **Critical inverse temperature** for the d-dimensional Ising model on ℤ^d
with coupling `J` (no ferromagneticity required in the definition): the supremum (in `ENNReal`)
of all inverse temperatures `β ≥ 0` for which the lattice mass
`latticeMass d (cubicExhaustion d) ⟨J, 0, β⟩` is strictly positive.

For β strictly below this threshold (and J > 0 ferromagnetic) the model is in the
high-temperature phase with exponential decay. For β strictly above the threshold the mass
equals 0 (see `latticeMass_eq_zero_of_criticalInverseTemp_lt`); for fixed J > 0 and
sufficiently large β, a genuine two-phase region appears in d ≥ 2 (Peierls, §5.4).

**GJ §17.1 analogy**: Glimm–Jaffe define the critical coupling `σ_c` as the infimum of
σ (mass² parameter) for which the φ⁴ theory has a unique phase with exponential decay.
Our `criticalInverseTemp d J` is the lattice Ising analog: because higher β = lower
temperature = stronger interaction, the critical point is a supremum in β rather than an
infimum in σ. -/
noncomputable def criticalInverseTemp (d : ℕ) (J : ℝ) : ENNReal :=
  sSup (ENNReal.ofReal ''
    { β : ℝ | 0 ≤ β ∧ 0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) })

/-- The defining set for `criticalInverseTemp` is non-empty: at `β = 0` the lattice mass
equals `⊤ > 0` (see `latticeMass_top_of_beta_zero`), so `0 ∈ {β | 0 ≤ β ∧ mass > 0}`. -/
theorem criticalInverseTemp_set_nonempty (d : ℕ) (J : ℝ) :
    (ENNReal.ofReal ''
      { β : ℝ | 0 ≤ β ∧
        0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) }).Nonempty :=
  ⟨ENNReal.ofReal 0, 0,
    ⟨le_refl 0, by simp [latticeMass_top_of_beta_zero]⟩, rfl⟩

/-- The critical inverse temperature is nonneg; trivially in `ENNReal`. -/
theorem criticalInverseTemp_nonneg (d : ℕ) (J : ℝ) : 0 ≤ criticalInverseTemp d J :=
  zero_le _

/-- **High-temperature lower bound on `criticalInverseTemp`** (GJ §17.1):
for `d ≥ 1` and `J > 0`, the critical inverse temperature satisfies
`β_c ≥ ENNReal.ofReal (1 / (2 * J * 2d)) > 0`.

Proof: the midpoint `β₀ := 1 / (2 * J * 2d)` satisfies `β₀ * J > 0` and
`β₀ * J * 2d = 1/2 < 1`, so `latticeMass_pos_of_high_temp` gives `mass > 0` at `β₀`.
Hence `β₀` lies in the defining set and `criticalInverseTemp ≥ ENNReal.ofReal β₀ > 0`. -/
theorem criticalInverseTemp_ge_ofReal_high_temp
    {d : ℕ} (hd : 1 ≤ d) {J : ℝ} (hJ : 0 < J) :
    ENNReal.ofReal (1 / (2 * J * ↑(2 * d))) ≤ criticalInverseTemp d J := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by exact_mod_cast Nat.mul_pos two_pos (by omega)
  have hβ_pos : (0 : ℝ) < 1 / (2 * J * ↑(2 * d)) := by positivity
  have hβJ : 0 < 1 / (2 * J * ↑(2 * d)) * J := mul_pos hβ_pos hJ
  have hβJd : 1 / (2 * J * ↑(2 * d)) * J * ↑(2 * d) < 1 := by
    have h2Jd_pos : (0 : ℝ) < 2 * J * ↑(2 * d) := by positivity
    rw [show (1 : ℝ) / (2 * J * ↑(2 * d)) * J * ↑(2 * d) =
        J * ↑(2 * d) / (2 * J * ↑(2 * d)) from by ring,
      div_lt_one h2Jd_pos]
    linarith [mul_pos hJ h2d_pos]
  have hmass : 0 < latticeMass d (cubicExhaustion d)
      (⟨J, 0, 1 / (2 * J * ↑(2 * d))⟩ : IsingParams ℝ) :=
    latticeMass_pos_of_high_temp hβJ hβJd
  have hmem : (1 / (2 * J * ↑(2 * d)) : ℝ) ∈
      { β : ℝ | 0 ≤ β ∧ 0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) } :=
    ⟨le_of_lt hβ_pos, hmass⟩
  calc ENNReal.ofReal (1 / (2 * J * ↑(2 * d)))
      ≤ sSup (ENNReal.ofReal '' { β : ℝ | 0 ≤ β ∧
          0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) }) :=
        le_sSup ⟨1 / (2 * J * ↑(2 * d)), hmem, rfl⟩
    _ = criticalInverseTemp d J := rfl

/-- The critical inverse temperature is strictly positive for `d ≥ 1` and `J > 0`:
the high-temperature bound `β_c ≥ 1/(2J·2d) > 0` guarantees positivity. -/
theorem criticalInverseTemp_pos {d : ℕ} (hd : 1 ≤ d) {J : ℝ} (hJ : 0 < J) :
    0 < criticalInverseTemp d J :=
  (ENNReal.ofReal_pos.mpr (by positivity)).trans_le
    (criticalInverseTemp_ge_ofReal_high_temp hd hJ)

/-- **Critical inverse temperature is antitone in the coupling J** (GJ §17.1 Cor 17.1.2 analog):
for `0 ≤ J₁ ≤ J₂`, the critical inverse temperature satisfies `β_c(J₂) ≤ β_c(J₁)`.

Physics: stronger coupling (larger J) → smaller lattice mass at fixed β (longer correlation
length) → phase transition occurs at higher temperature (= smaller β_c, since β_c = 1/T_c
and larger T_c means smaller β_c). Proof: `latticeMass_antitone_J` gives
`latticeMass(J₁, β) ≥ latticeMass(J₂, β)` for β > 0, so the high-temperature set for J₁
contains the high-temperature set for J₂, hence sSup J₁ ≥ sSup J₂.

**GJ §17.1 monotonicity analog**: Cor 17.1.2 states that the mass m(σ) is monotone
increasing in σ (larger σ = weaker coupling = larger mass). Here J plays the role of
-σ, so increasing J decreases the mass at fixed β, lowering β_c. -/
theorem criticalInverseTemp_antitone_J
    {d : ℕ} {J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) :
    criticalInverseTemp d J₂ ≤ criticalInverseTemp d J₁ := by
  unfold criticalInverseTemp
  apply sSup_le_sSup
  rintro x ⟨β, ⟨hβ_nn, hmass_pos⟩, rfl⟩
  refine ⟨β, ⟨hβ_nn, ?_⟩, rfl⟩
  rcases eq_or_lt_of_le hβ_nn with rfl | hβ_pos
  · simp [latticeMass_top_of_beta_zero]
  · exact lt_of_lt_of_le hmass_pos
      (latticeMass_antitone_J (cubicExhaustion d) hJ₁ hJ₁₂ hβ_pos)

/-! ## §17.1 Critical inverse temperature — characterization -/

/-- **Lower bound on `criticalInverseTemp` from positive mass** (GJ §17.1):
if `latticeMass d (cubicExhaustion d) ⟨J, 0, β⟩ > 0` for some `β ≥ 0`, then
`ENNReal.ofReal β ≤ criticalInverseTemp d J`.

Proof: `β` is in the defining set of `criticalInverseTemp`, so `ENNReal.ofReal β` is
in the image set, and `le_sSup` gives the bound. -/
theorem criticalInverseTemp_ge_ofReal_of_latticeMass_pos
    {d : ℕ} {J β : ℝ} (hβ : 0 ≤ β)
    (h : 0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    ENNReal.ofReal β ≤ criticalInverseTemp d J :=
  le_sSup ⟨β, ⟨hβ, h⟩, rfl⟩

/-- **Mass vanishes above the critical inverse temperature** (GJ §17.1):
if `criticalInverseTemp d J < ENNReal.ofReal β` (and `β ≥ 0`), then
`latticeMass d (cubicExhaustion d) ⟨J, 0, β⟩ = 0`.

This is the characterization: for β strictly above the critical threshold, the
high-temperature exponential-decay regime ends and mass vanishes (within the ENNReal lattice).
Proof: contrapositive of `criticalInverseTemp_ge_ofReal_of_latticeMass_pos`. -/
theorem latticeMass_eq_zero_of_criticalInverseTemp_lt
    {d : ℕ} {J β : ℝ} (hβ : 0 ≤ β)
    (h : criticalInverseTemp d J < ENNReal.ofReal β) :
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) = 0 := by
  by_contra hm
  exact absurd h (not_lt.mpr
    (criticalInverseTemp_ge_ofReal_of_latticeMass_pos hβ (lt_of_le_of_ne (zero_le _) (Ne.symm hm))))

/-- **Positive mass below the critical inverse temperature** (GJ §17.1):
for ferromagnetic `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J`,
the lattice mass is strictly positive.

Together with `latticeMass_eq_zero_of_criticalInverseTemp_lt` and
`criticalInverseTemp_ge_ofReal_of_latticeMass_pos`, this gives a near-complete picture:
`ENNReal.ofReal β < β_c → mass > 0 → ENNReal.ofReal β ≤ β_c`
(where `β_c = criticalInverseTemp d J`).
The boundary case `ENNReal.ofReal β = criticalInverseTemp d J` remains undetermined.

**GJ §17.1 context**: for σ < σ_c (= β < β_c in the Ising analog), the theory has
exponential decay of correlations; this is the defining property of the critical coupling.

Proof: by contradiction — if mass(J, β) = 0, then for all β' ≥ β (and β > 0), the
antitonicity `latticeMass_antitone_beta` gives mass(J, β') ≤ mass(J, β) = 0. Hence the
defining set ⊆ `[0, β)`, so `criticalInverseTemp ≤ ENNReal.ofReal β`, contradicting
`ENNReal.ofReal β < criticalInverseTemp`. The β = 0 case is vacuous since mass(J, 0) = ⊤. -/
theorem latticeMass_pos_of_lt_criticalInverseTemp
    {d : ℕ} {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J) :
    0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  by_contra hm
  rw [not_lt] at hm
  have hm_zero : latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) = 0 :=
    le_antisymm hm (latticeMass_nonneg _ _ _)
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · simp [latticeMass_top_of_beta_zero] at hm_zero
  · have h_bound : criticalInverseTemp d J ≤ ENNReal.ofReal β := by
      unfold criticalInverseTemp
      apply sSup_le
      intro b hb
      rw [Set.mem_image] at hb
      obtain ⟨γ, ⟨hγ_nn, hmass_γ⟩, hγ_eq⟩ := hb
      rw [← hγ_eq]
      apply ENNReal.ofReal_le_ofReal
      by_cases h_le : γ ≤ β
      · exact h_le
      · rw [not_le] at h_le
        have hmono := latticeMass_antitone_beta (cubicExhaustion d) hJ hβ_pos h_le.le
        rw [hm_zero] at hmono
        exact absurd hmass_γ (not_lt.mpr hmono)
    exact absurd h (not_lt.mpr h_bound)

/-! ## §17.1 Cluster property below criticalInverseTemp (Step 146) -/

/-- **Extract positive decay rate from positive lattice mass** (GJ §17.1):
if `latticeMass d Λ p > 0`, there exists `α : NNReal` with `0 < (α : ℝ)` and
`HasExponentialDecay d Λ p (α : ℝ)`.

Proof: by `lt_sSup_iff`, a positive supremum of the image set contains some
element `(α : ENNReal) > 0`; coercing via `ENNReal.coe_pos` and
`NNReal.coe_pos` yields a positive real decay rate.

**GJ §17.1 context**: the positivity of the lattice mass (= inverse correlation
length) directly produces an exponential decay witness, connecting the abstract
`latticeMass` definition to the `HasExponentialDecay` predicate. -/
theorem HasExponentialDecay_of_latticeMass_pos
    {d : ℕ} {Λ : Ambient.Exhaustion (Fin d → ℤ)} {p : IsingParams ℝ}
    (h : 0 < latticeMass d Λ p) :
    ∃ α : NNReal, 0 < (α : ℝ) ∧ HasExponentialDecay d Λ p (α : ℝ) := by
  unfold latticeMass at h
  rw [lt_sSup_iff] at h
  obtain ⟨y, hy_mem, hy_pos⟩ := h
  rw [Set.mem_image] at hy_mem
  obtain ⟨α, hα_decay, hα_eq⟩ := hy_mem
  rw [← hα_eq] at hy_pos
  exact ⟨α, NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hy_pos), hα_decay⟩

/-- **Transfer `HasExponentialDecay` across exhaustions**:
for ferromagnetic `p`, if `HasExponentialDecay d Λ p α` holds for some
exhaustion `Λ`, then it holds for any other exhaustion `Λ'`.

Proof: the truncated 2-point function is exhaustion-independent for ferromagnetic
parameters (`truncated2Infinite_indep_exhaustion`), so the bound transfers directly
from `Λ` to `Λ'` with the same constant `C` and rate `α`. -/
theorem HasExponentialDecay_transfer_exhaustion
    {d : ℕ} (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {p : IsingParams ℝ} {α : ℝ}
    (hf : Ferromagnetic p)
    (h : HasExponentialDecay d Λ p α) :
    HasExponentialDecay d Λ' p α := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun i j hij => ?_⟩
  rw [truncated2Infinite_indep_exhaustion (IsingModel.latticeGraph d) Λ' Λ p hf i j]
  exact hbound i j hij

/-- **Uniform high-temperature exponential decay across exhaustions**:
the Simon--Lieb high-temperature decay rate from `cubicExhaustion` transfers to any
exhaustion `Λ` under ferromagnetic `h = 0` parameters.

This is the reusable uniform-in-exhaustion form needed by the Step 117l
pseudo-mass/lattice-mass bridge: the witness constant and rate are independent of
the target exhaustion because `truncated2Infinite` is exhaustion-independent under
ferromagnetic parameters.

References: Glimm--Jaffe §5.1 pp. 74--75 and §17.5 Lemma 17.5.2, pp. 311--312;
Friedli--Velenik Prop. 9.31 p. 428. -/
theorem HasExponentialDecay_transfer_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (-Real.log (β * J * ↑(2 * d))) :=
  HasExponentialDecay_transfer_exhaustion (cubicExhaustion d) Λ
    (p := (⟨J, 0, β⟩ : IsingParams ℝ))
    ⟨hJ, le_refl 0, hβ⟩
    (hasExponentialDecay_of_high_temp (mul_nonneg hβ.le hJ) hlt)

/-- **Arbitrary-exhaustion high-temperature lattice-mass lower bound**:
for any exhaustion `Λ`, the Simon--Lieb high-temperature rate
`-log(βJ·2d)` belongs below `latticeMass d Λ ⟨J,0,β⟩`.

This is the exhaustion-uniform version of `latticeMass_ge_neg_log_of_high_temp`;
it combines `HasExponentialDecay_transfer_high_temp` with the `sSup` definition
of `latticeMass`.

References: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_neg_log_of_high_temp_exhaustion
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) :
    ENNReal.ofReal (-Real.log (β * J * ↑(2 * d))) ≤
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have hβJD_nn : 0 ≤ β * J * ↑(2 * d) :=
    mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg _)
  have hα_nn : 0 ≤ -Real.log (β * J * ↑(2 * d)) :=
    neg_nonneg.mpr (Real.log_nonpos hβJD_nn hlt.le)
  exact latticeMass_ge_of_HasExponentialDecay hα_nn
    (HasExponentialDecay_transfer_high_temp Λ hJ hβ hlt)

/-- **Arbitrary-exhaustion positive lattice mass in the high-temperature regime**:
if `0 < βJ` and `βJ·2d < 1` with `d ≥ 1`, then every exhaustion has positive
`latticeMass`.

The proof uses the transferred high-temperature decay rate
`-log(βJ·2d)`, which is strictly positive when `0 < βJ·2d < 1`.

Reference: Glimm--Jaffe §17.5 pp. 304--306. -/
theorem latticeMass_pos_of_high_temp_exhaustion
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ : 0 < β * J)
    (hlt : β * J * ↑(2 * d) < 1) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have hβJD_pos : 0 < β * J * ↑(2 * d) :=
    mul_pos hβJ (Nat.cast_pos.mpr (by omega))
  have hα_pos : 0 < -Real.log (β * J * ↑(2 * d)) :=
    neg_pos.mpr (Real.log_neg hβJD_pos hlt)
  exact latticeMass_pos_of_HasExponentialDecay hα_pos
    (HasExponentialDecay_transfer_high_temp Λ hJ hβ hlt)

/-- **Pseudo-mass/high-temperature comparison from a profile lower bound**:
if the infinite-volume pair correlation is in the active pseudo-mass range
`Ioo 0 2` and dominates the pseudo-mass profile
`pseudoMassG α r (-log(βJ·2d))`, then the concrete pair pseudo-mass is no
larger than the transferred Simon--Lieb high-temperature rate.

The proof unfolds `pseudoMassFromParamsAtPair`, rewrites `pseudoMassExt` to
`pseudoMass` on `Ioo 0 2`, and applies the implicit characterization
`pseudoMass(c) ≤ t ↔ pseudoMassG α r t ≤ c`. The high-temperature hypotheses
give `0 ≤ -log(βJ·2d)`.

References: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312; Glimm--Jaffe
§5.1 pp. 74--75. -/
theorem pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d)) := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  unfold pseudoMassFromParamsAtPair
  rw [pseudoMassExt_of_mem hα hr hcorr]
  exact (pseudoMass_le_iff_pseudoMassG_le hα hr hcorr hrate_nonneg).mpr hprofile

/-- **Pseudo-mass validates decay when it is below the high-temperature rate**:
if the concrete pair pseudo-mass is bounded above by the transferred
Simon--Lieb high-temperature rate `-log(βJ·2d)`, then that pseudo-mass itself
is a validating `HasExponentialDecay` rate.

This is the monotonicity step needed after
`HasExponentialDecay_transfer_high_temp`: smaller decay rates give weaker
exponential bounds, so they remain valid.

References: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312; Glimm--Jaffe §5.1
pp. 74--75; Friedli--Velenik Prop. 9.31 p. 428. -/
theorem HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle : pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_mono d Λ (⟨J, 0, β⟩ : IsingParams ℝ) hle
    (HasExponentialDecay_transfer_high_temp Λ hJ hβ hlt)

/-- **Profile lower bound validates the concrete pair pseudo-mass as a decay rate**:
the profile criterion
`pseudoMassG α r (-log(βJ·2d)) ≤ correlationInfinite {x,z}` supplies the
missing comparison with the transferred high-temperature rate, so the concrete
pseudo-mass is itself a valid exponential-decay rate.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr hprofile)

/-- **Pseudo-mass lower bound from comparison with the high-temperature rate**:
under the comparison `pseudoMassFromParamsAtPair ≤ -log(βJ·2d)`, the concrete
pseudo-mass is bounded above by `latticeMass`.

This composes the transferred Simon--Lieb high-temperature decay rate, rate
monotonicity of `HasExponentialDecay`, and the `sSup` definition of
`latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_pseudoMassFromParamsAtPair_of_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle : pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_of_HasExponentialDecay
    (pseudoMassFromParamsAtPair_nonneg hα hr d Λ _ x z)
    (HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle)

/-- **Lattice-mass lower bound from a profile lower bound**:
if the correlation dominates `pseudoMassG` at the transferred
high-temperature rate, then the concrete pair pseudo-mass is bounded above by
`latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_pseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr hprofile)

/-- **Positive lattice mass from positive pseudo-mass below the high-temperature rate**:
if the concrete pair pseudo-mass is positive and no larger than the transferred
Simon--Lieb high-temperature rate, then `latticeMass` is positive.

This is the positivity companion to
`latticeMass_ge_pseudoMassFromParamsAtPair_of_le_high_temp_rate`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_pseudoMassFromParamsAtPair_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hpos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle : pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_HasExponentialDecay hpos
    (HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle)

/-- **Positive lattice mass from a profile lower bound**:
the active-range correlation hypothesis makes the concrete pair pseudo-mass
positive, and the profile lower bound supplies the comparison with the
transferred high-temperature rate.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_pseudoMassFromParamsAtPair_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_pseudoMassFromParamsAtPair_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z hcorr)
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr hprofile)

/-- **Reference-exhaustion pseudo-mass comparison transfers to a target exhaustion**:
if the concrete pair pseudo-mass computed with a reference exhaustion `Λ₀` is
bounded above by the transferred Simon--Lieb high-temperature rate
`-log(βJ·2d)`, then the pseudo-mass computed with the target exhaustion `Λ`
is a validating `HasExponentialDecay` rate.

The proof uses exhaustion-independence of `pseudoMassFromParamsAtPair` under
ferromagnetic parameters, then applies
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle₀ : pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ⟩
  have hpm : pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z =
      pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    pseudoMassFromParamsAtPair_indep_exhaustion hα hr d Λ Λ₀
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have hle : pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d)) := by
    simpa [hpm] using hle₀
  exact HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt hle

/-- **Reference-exhaustion profile bound validates the target pseudo-mass**:
if a reference exhaustion supplies the profile lower bound at the
high-temperature rate, the resulting reference comparison transfers to the
target pseudo-mass by exhaustion-independence.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr₀ : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile₀ : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ Λ₀ hJ hβ hlt
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ₀ hJ hβ hlt hcorr₀ hprofile₀)

/-- **Reference-exhaustion comparison gives a target-exhaustion lattice-mass lower bound**:
under the comparison of the reference pseudo-mass with the high-temperature
rate, the target-exhaustion pseudo-mass is bounded by the target
`latticeMass`.

This is the `latticeMass` consequence of
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle₀ : pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_of_HasExponentialDecay
    (pseudoMassFromParamsAtPair_nonneg hα hr d Λ _ x z)
    (HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
      hα hr Λ Λ₀ hJ hβ hlt hle₀)

/-- **Reference-exhaustion profile bound gives a target lattice-mass lower bound**:
the profile lower bound on the reference exhaustion supplies the reference
comparison with `-log(βJ·2d)`, and hence bounds the target pseudo-mass by the
target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr₀ : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile₀ : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ Λ₀ hJ hβ hlt
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ₀ hJ hβ hlt hcorr₀ hprofile₀)

/-- **Reference-exhaustion comparison gives positive target lattice mass**:
if the target pseudo-mass is positive and the reference pseudo-mass is no
larger than the high-temperature rate, then the target `latticeMass` is
positive.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_pseudoMassFromParamsAtPair_exhaustion_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hpos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle₀ : pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_HasExponentialDecay hpos
    (HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
      hα hr Λ Λ₀ hJ hβ hlt hle₀)

/-- **Reference-exhaustion profile bound gives positive target lattice mass**:
if the target pseudo-mass is positive and the reference exhaustion supplies
the profile lower bound at the high-temperature rate, then the target
`latticeMass` is positive.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_pseudoMassFromParamsAtPair_exhaustion_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hpos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hcorr₀ : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile₀ : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_pseudoMassFromParamsAtPair_exhaustion_le_high_temp_rate
    hα hr Λ Λ₀ hJ hβ hlt hpos
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ₀ hJ hβ hlt hcorr₀ hprofile₀)

/-- **Cubic-reference pseudo-mass comparison transfers to any exhaustion**:
the specialization of
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate`
where the reference exhaustion is `cubicExhaustion d`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_pseudoMassFromParamsAtPair_of_cubic_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle_cubic : pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hle_cubic

/-- **Cubic-reference profile bound validates the target pseudo-mass**:
the specialization of
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr`
with `cubicExhaustion d` as the reference exhaustion.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
          ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hcorr_cubic hprofile_cubic

/-- **Cubic-reference comparison gives an arbitrary-exhaustion lattice-mass lower bound**:
if the pseudo-mass comparison with `-log(βJ·2d)` is verified on
`cubicExhaustion d`, then the target-exhaustion pseudo-mass is bounded above
by the target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_pseudoMassFromParamsAtPair_of_cubic_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle_cubic : pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hle_cubic

/-- **Cubic-reference profile bound gives an arbitrary-exhaustion lattice-mass lower bound**:
if the cubic exhaustion supplies the profile lower bound at the
high-temperature rate, then the target-exhaustion pseudo-mass is bounded above
by the target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
          ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hcorr_cubic hprofile_cubic

/-- **Cubic-reference comparison gives positive lattice mass for any exhaustion**:
if the target pseudo-mass is positive and the cubic-reference pseudo-mass is no
larger than the high-temperature rate, then the target `latticeMass` is
positive.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_pseudoMassFromParamsAtPair_cubic_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hpos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle_cubic : pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_pseudoMassFromParamsAtPair_exhaustion_le_high_temp_rate
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hpos hle_cubic

/-- **Cubic-reference profile bound gives positive lattice mass for any exhaustion**:
if the target pseudo-mass is positive and the cubic exhaustion supplies the
profile lower bound at the high-temperature rate, then the target
`latticeMass` is positive.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_pseudoMassFromParamsAtPair_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hpos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
          ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_pseudoMassFromParamsAtPair_exhaustion_pseudoMassG_le_corr
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hpos hcorr_cubic hprofile_cubic

/-- **Reference pseudo-mass itself is a target validating rate**:
if the pseudo-mass/high-temperature-rate comparison is verified on a reference
exhaustion `Λ₀`, then that reference pseudo-mass value is also a validating
`HasExponentialDecay` rate for the target exhaustion `Λ`.

This is the direct reference-rate form of
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate`;
it only needs the numerical comparison of the reference pseudo-mass with the
transferred high-temperature rate.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle₀ : pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_mono d Λ (⟨J, 0, β⟩ : IsingParams ℝ) hle₀
    (HasExponentialDecay_transfer_high_temp Λ hJ hβ hlt)

/-- **Reference pseudo-mass is a target validating rate from a profile bound**:
if the reference-exhaustion correlation dominates `pseudoMassG` at the
transferred high-temperature rate, then that reference pseudo-mass value is a
valid decay rate for the target exhaustion.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr₀ : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile₀ : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ Λ₀ hJ hβ hlt
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ₀ hJ hβ hlt hcorr₀ hprofile₀)

/-- **Reference pseudo-mass lower bound on target lattice mass**:
under the reference-exhaustion high-temperature comparison, the reference
pseudo-mass value itself is bounded above by the target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle₀ : pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ₀
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_of_HasExponentialDecay
    (pseudoMassFromParamsAtPair_nonneg hα hr d Λ₀ _ x z)
    (HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
      hα hr Λ Λ₀ hJ hβ hlt hle₀)

/-- **Reference pseudo-mass lower bound on target lattice mass from a profile bound**:
if the reference-exhaustion correlation dominates `pseudoMassG` at the
transferred high-temperature rate, then the reference pseudo-mass value is
bounded above by the target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_reference_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr₀ : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile₀ : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ₀
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ Λ₀ hJ hβ hlt
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ₀ hJ hβ hlt hcorr₀ hprofile₀)

/-- **Positive target lattice mass from a positive reference pseudo-mass**:
if the reference pseudo-mass is positive and no larger than the high-temperature
rate, then the target `latticeMass` is positive.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_reference_pseudoMassFromParamsAtPair_exhaustion_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hpos₀ : 0 < pseudoMassFromParamsAtPair hα hr d Λ₀
      (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle₀ : pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_HasExponentialDecay hpos₀
    (HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
      hα hr Λ Λ₀ hJ hβ hlt hle₀)

/-- **Positive target lattice mass from a reference profile lower bound**:
the reference active-range hypothesis makes the reference pseudo-mass positive,
and the profile lower bound supplies the high-temperature comparison.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_reference_pseudoMassFromParamsAtPair_exhaustion_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr₀ : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile₀ : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_reference_pseudoMassFromParamsAtPair_exhaustion_le_high_temp_rate
    hα hr Λ Λ₀ hJ hβ hlt
    (pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d Λ₀
      (⟨J, 0, β⟩ : IsingParams ℝ) x z hcorr₀)
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ₀ hJ hβ hlt hcorr₀ hprofile₀)

/-- **Cubic pseudo-mass itself is a target validating rate**:
if the pseudo-mass/high-temperature-rate comparison is verified on
`cubicExhaustion d`, then that cubic pseudo-mass value is a validating
`HasExponentialDecay` rate for any target exhaustion `Λ`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_cubic_pseudoMassFromParamsAtPair_of_cubic_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle_cubic : pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hle_cubic

/-- **Cubic pseudo-mass is a target validating rate from a profile bound**:
the specialization of
`HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr`
with `cubicExhaustion d` as the reference exhaustion.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_cubic_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
          ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hcorr_cubic hprofile_cubic

/-- **Cubic pseudo-mass lower bound on arbitrary-exhaustion lattice mass**:
under the cubic-reference comparison with `-log(βJ·2d)`, the cubic pseudo-mass
value itself is bounded above by the target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_cubic_pseudoMassFromParamsAtPair_of_cubic_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle_cubic : pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hle_cubic

/-- **Cubic pseudo-mass lower bound on target lattice mass from a profile bound**:
if the cubic exhaustion supplies the profile lower bound at the
high-temperature rate, then the cubic pseudo-mass value itself is bounded
above by the target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_cubic_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
          ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_reference_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hcorr_cubic hprofile_cubic

/-- **Positive target lattice mass from a positive cubic pseudo-mass**:
if the cubic-reference pseudo-mass is positive and no larger than the
high-temperature rate, then the target `latticeMass` is positive.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_cubic_pseudoMassFromParamsAtPair_cubic_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hpos_cubic : 0 < pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle_cubic : pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_reference_pseudoMassFromParamsAtPair_exhaustion_le_high_temp_rate
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hpos_cubic hle_cubic

/-- **Positive target lattice mass from a cubic profile lower bound**:
the cubic active-range hypothesis makes the cubic pseudo-mass positive, and
the cubic profile lower bound supplies the high-temperature comparison.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_cubic_pseudoMassFromParamsAtPair_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
          ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_reference_pseudoMassFromParamsAtPair_exhaustion_pseudoMassG_le_corr
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hcorr_cubic hprofile_cubic

/-- **Tanh-power profile bound implies the cubic pair-correlation profile bound**:
the existing path lower bound
`tanh(βJ) ^ latticeDistance d 0 z ≤ twoPointFunction d ⟨J,0,β⟩ z`
turns the numerical condition
`pseudoMassG α r (-log(βJ·2d)) ≤ tanh(βJ) ^ latticeDistance d 0 z`
into the cubic-exhaustion correlation lower bound required by the
profile-comparison bridge.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassG_le_cubic_correlation_of_le_tanh_pow_dist
    {α d : ℕ} {r β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} := by
  have hpow_le_corr :
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z} := by
    change Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z ≤
      twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z
    exact twoPointFunction_ge_tanh_betaJ_pow_dist hJ hβ hz
  exact hprofile_tanh.trans hpow_le_corr

/-- **Cubic pair correlation is positive from a tanh-power profile bound**:
under the high-temperature hypothesis, the Lean real-log rate `-log(βJ·2d)` is
nonnegative, so `pseudoMassG` is positive at that rate.  Combining this
positivity with the tanh-power reduction gives positivity of the anchored cubic
pair correlation.

This supplies the lower half of the active-range input used by the
profile-comparison bridge toward GJ §17.5 Lemma 17.5.2.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_pos_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  exact lt_of_lt_of_le (pseudoMassG_pos α hrate_nonneg hr)
    (pseudoMassG_le_cubic_correlation_of_le_tanh_pow_dist
      (α := α) (d := d) (r := r) (β := β) (J := J)
      hJ hβ (z := z) hz hprofile_tanh)

set_option maxHeartbeats 2000000 in
-- The totalized proof splits on active-interval membership and reuses the
-- implicit pseudo-mass comparison, which is heavier than the surrounding wrappers.
/-- **Two-point pseudo-mass extension comparison from a tanh-power profile bound**:
the tanh-power lower-bound reduction supplies the profile comparison whenever
the anchored two-point function is in the active interval.  Outside the active
interval, `pseudoMassExt` is zero, so the high-temperature comparison is
automatic from nonnegativity of the Lean real-log rate.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassExt_twoPointFunction_le_high_temp_rate_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMassExt hα hr (twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z)
      ≤ -Real.log (β * J * ↑(2 * d)) := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  have hprofile_two :
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z :=
    hprofile_tanh.trans (twoPointFunction_ge_tanh_betaJ_pow_dist hJ hβ hz)
  by_cases hcorr : twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z ∈ Set.Ioo (0 : ℝ) 2
  · rw [pseudoMassExt_of_mem hα hr hcorr]
    exact (pseudoMass_le_iff_pseudoMassG_le hα hr hcorr hrate_nonneg).mpr hprofile_two
  · rw [pseudoMassExt_of_not_mem hα hr hcorr]
    exact hrate_nonneg

/-- **Two-point active range from a tanh-power profile bound**: the same
tanh-power lower-bound reduction used for the totalized comparison also proves
that the anchored two-point function lies in the pseudo-mass active interval
`(0,2)`.  The lower endpoint comes from positivity of `pseudoMassG` at the
Lean total real-log rate; the upper endpoint uses the universal bound
`twoPointFunction ≤ 1`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z ∈ Set.Ioo (0 : ℝ) 2 := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  have hprofile_two :
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z :=
    hprofile_tanh.trans (twoPointFunction_ge_tanh_betaJ_pow_dist hJ hβ hz)
  constructor
  · exact lt_of_lt_of_le (pseudoMassG_pos α hrate_nonneg hr) hprofile_two
  · exact lt_of_le_of_lt
      (twoPointFunction_le_one d (⟨J, 0, β⟩ : IsingParams ℝ) z) one_lt_two

/-- **Ordinary two-point pseudo-mass comparison from a tanh-power profile bound**:
once the tanh-power profile bound places the anchored two-point function in
`(0,2)`, the implicit pseudo-mass comparison gives the non-totalized
`pseudoMass` bound by the high-temperature rate.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMass_twoPointFunction_le_high_temp_rate_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMass hα hr
        (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
          (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh)
      ≤ -Real.log (β * J * ↑(2 * d)) := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  have hcorr :
      twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z ∈ Set.Ioo (0 : ℝ) 2 :=
    twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh
  have hprofile_two :
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z :=
    hprofile_tanh.trans (twoPointFunction_ge_tanh_betaJ_pow_dist hJ hβ hz)
  exact (pseudoMass_le_iff_pseudoMassG_le hα hr hcorr hrate_nonneg).mpr hprofile_two

/-- **The totalized two-point pseudo-mass equals the ordinary pseudo-mass under
the tanh-power profile bound**: the profile condition supplies the active-range
membership needed to remove the totalization.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassExt_twoPointFunction_eq_pseudoMass_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMassExt hα hr (twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z) =
      pseudoMass hα hr
        (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
          (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh) := by
  rw [pseudoMassExt_of_mem hα hr
    (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh)]

/-- **Ordinary two-point pseudo-mass positivity from a tanh-power profile
bound**: the active-range theorem supplies the `Ioo 0 2` argument required by
`pseudoMass_pos`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMass_twoPointFunction_pos_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    0 < pseudoMass hα hr
      (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
        (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh) :=
  pseudoMass_pos hα hr
    (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh)

/-- **Totalized two-point pseudo-mass positivity from a tanh-power profile
bound**: under the profile condition, the anchored two-point function is active,
so `pseudoMassExt` is strictly positive.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassExt_twoPointFunction_pos_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    0 < pseudoMassExt hα hr (twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z) :=
  pseudoMassExt_pos_of_mem hα hr
    (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh)

/-- **Totalized two-point pseudo-mass non-vanishing from a tanh-power profile
bound**: a direct non-zero corollary of positivity.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassExt_twoPointFunction_ne_zero_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMassExt hα hr (twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z) ≠ 0 :=
  ne_of_gt
    (pseudoMassExt_twoPointFunction_pos_of_pseudoMassG_le_tanh_pow_dist
      hα hr hJ hβ hlt hz hprofile_tanh)

/-- **Cubic pair active range from a tanh-power profile bound**:
the tanh-power reduction supplies a positive lower bound on the anchored cubic
pair correlation, and the universal correlation bound gives the upper endpoint
`< 2`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 := by
  constructor
  · exact correlationInfinite_cubic_pair_pos_of_pseudoMassG_le_tanh_pow_dist
      hr hJ hβ hlt hz hprofile_tanh
  · exact lt_of_le_of_lt
      (Ambient.correlationInfinite_le_one (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({(0 : Fin d → ℤ), z} : Finset (Fin d → ℤ)))
      one_lt_two

/-- **Cubic pair correlation is nonzero from a tanh-power profile bound**:
positivity of the anchored cubic pair correlation rules out zero.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_ne_zero_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} ≠ 0 :=
  ne_of_gt
    (correlationInfinite_cubic_pair_pos_of_pseudoMassG_le_tanh_pow_dist
      hr hJ hβ hlt hz hprofile_tanh)

/-- **Cubic pair correlation is in `(0,1]` from a tanh-power profile bound**:
the tanh-power hypothesis gives positivity, while boundedness of correlations
gives the endpoint `≤ 1`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_mem_Ioc_zero_one_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact correlationInfinite_cubic_pair_pos_of_pseudoMassG_le_tanh_pow_dist
      hr hJ hβ hlt hz hprofile_tanh
  · exact Ambient.correlationInfinite_le_one (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ({(0 : Fin d → ℤ), z} : Finset (Fin d → ℤ))

/-- **Cubic pair correlation is strictly below two from a tanh-power profile
bound**: this is the upper endpoint of the active interval package.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_lt_two_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} < 2 :=
  (correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
    (α := α) hr hJ hβ hlt hz hprofile_tanh).2

/-- **Cluster property holds below the critical inverse temperature** (GJ §17.1):
for `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J`, the
cluster property holds for any exhaustion `Λ`:
```
clusterProperty (latticeGraph d) Λ ⟨J, 0, β⟩.
```

**Physics**: the hypothesis `β < β_c` is the **high-temperature** regime
(equivalently, above the critical temperature `T_c = 1/β_c`). In this regime,
the connected 2-point function decays exponentially: for all `i, j`,
`|⟨σᵢ σⱼ⟩ - ⟨σᵢ⟩⟨σⱼ⟩|` decays to zero as `|i - j| → ∞`. This is the
GJ §17.1 high-temperature clustering consequence for the Ising model analog.

**Proof strategy**:
* `β = 0`: `clusterProperty_latticeGraph_beta_zero` (trivial slice).
* `β > 0`: use `latticeMass_pos_of_lt_criticalInverseTemp` to get `m > 0`,
  extract a positive rate `α` via `HasExponentialDecay_of_latticeMass_pos`,
  transfer the decay from `cubicExhaustion d` to `Λ` via
  `HasExponentialDecay_transfer_exhaustion` (uses `Ferromagnetic`), and
  conclude by `clusterProperty_latticeGraph_of_HasExponentialDecay`. -/
theorem clusterProperty_latticeGraph_of_lt_criticalInverseTemp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J) :
    clusterProperty (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · exact clusterProperty_beta_zero (IsingModel.latticeGraph d) Λ J 0
  · have hm_pos : 0 < latticeMass d (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) :=
      latticeMass_pos_of_lt_criticalInverseTemp hβ_pos.le hJ h
    obtain ⟨α, hα_pos, hα_decay⟩ := HasExponentialDecay_of_latticeMass_pos hm_pos
    have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨hJ, le_refl _, hβ_pos⟩
    have hα_decay' : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (α : ℝ) :=
      HasExponentialDecay_transfer_exhaustion (cubicExhaustion d) Λ hf hα_decay
    exact clusterProperty_latticeGraph_of_HasExponentialDecay d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hα_pos hα_decay'

/-- **Summability of truncated 2-point below critical inverse temperature** (GJ §17.1/§17.5):
for `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J`, the truncated
2-point function is summable:
`Summable (fun j => truncated2Infinite (latticeGraph d) Λ ⟨J, 0, β⟩ i j)`.

This extends `truncated2Infinite_summable_of_high_temp` (βJD < 1 case, PR #903) to the
full below-β_c regime, giving a per-site finite-susceptibility result for all high-temperature
couplings (not just the Simon-Lieb high-temperature range).

**Proof**: β = 0 gives `U_2 = 0` (summable trivially). For β > 0: `latticeMass > 0`
(via `latticeMass_pos_of_lt_criticalInverseTemp`) → extract `α > 0` and
`HasExponentialDecay` (via `HasExponentialDecay_of_latticeMass_pos`) → transfer to `Λ`
(via `HasExponentialDecay_transfer_exhaustion`) → `|U_2(i,j)| ≤ C·exp(-α·d(i,j))` for
`i ≠ j` and `U_2(i,i) = 0` (Z₂ symmetry) → `summable_exp_neg_dist` + nonneg bound
→ `Summable.of_nonneg_of_le`. -/
theorem truncated2Infinite_summable_of_lt_criticalInverseTemp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J)
    (i : Fin d → ℤ) :
    Summable (fun j : Fin d → ℤ =>
      truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i j) := by
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · simp only [truncated2Infinite_beta_zero (IsingModel.latticeGraph d) Λ J 0]
    exact summable_zero
  · have hm_pos : 0 < latticeMass d (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) :=
      latticeMass_pos_of_lt_criticalInverseTemp hβ_pos.le hJ h
    obtain ⟨α, hα_pos, hα_decay⟩ := HasExponentialDecay_of_latticeMass_pos hm_pos
    have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl _, hβ_pos⟩
    obtain ⟨C, hC, hbound⟩ :=
      HasExponentialDecay_transfer_exhaustion (cubicExhaustion d) Λ hf hα_decay
    apply Summable.of_nonneg_of_le
        (fun j => truncated2Infinite_nonneg (IsingModel.latticeGraph d) Λ _ hf i j)
        (fun j => ?_)
        ((summable_exp_neg_dist hα_pos d i).mul_left C)
    by_cases hij : i = j
    · subst hij
      rw [truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β i i]
      simp only [Finset.pair_eq_singleton]
      rw [Ambient.correlationInfinite_h_zero (IsingModel.latticeGraph d) Λ J β {i} (by simp)]
      exact mul_nonneg hC (Real.exp_nonneg _)
    · exact le_trans (le_abs_self _) (hbound i j hij)

end Ambient
end IsingModel
