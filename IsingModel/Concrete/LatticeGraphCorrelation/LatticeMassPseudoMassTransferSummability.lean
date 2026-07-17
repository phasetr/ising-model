import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundationTrivialSliceAndIndep
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
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.PosAndAntitone

/-!
# Lattice-mass: Step 127 summability + criticalInverseTemp foundations

Narrow child module for the §17.5 Step 127 Lebowitz-exponential product
summability bounds and §17.1 / §17.5 criticalInverseTemp foundations:
`summable_truncated2Infinite_prod_of_hasExponentialDecay`,
`tsum_truncated2Infinite_prod_le`, `criticalInverseTemp_set_nonempty`,
`criticalInverseTemp_nonneg`, `criticalInverseTemp_ge_ofReal_high_temp`,
`criticalInverseTemp_pos`, `criticalInverseTemp_antitone_J`,
`criticalInverseTemp_ge_ofReal_of_latticeMass_pos`,
`latticeMass_eq_zero_of_criticalInverseTemp_lt`, and
`latticeMass_pos_of_lt_criticalInverseTemp`. The theorem names are
unchanged from the former `LatticeMassPseudoMassTransfer` declarations.
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

/-! ## Moved: criticalInverseTemp characterization wrappers

The three `criticalInverseTemp_ge_ofReal_of_latticeMass_pos`,
`latticeMass_eq_zero_of_criticalInverseTemp_lt`,
`latticeMass_pos_of_lt_criticalInverseTemp` characterization theorems now
live in `LatticeMassPseudoMassTransferSummabilityCharacterization.lean`. -/



end Ambient

end IsingModel
