import IsingModel.Conditioning.Bounds

/-!
# Free Energy Bounds

This module is part of the split `IsingModel.Conditioning` development.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Free energy upper bound (Corollary 10.3.2, divided by `|ι|`) -/

/-- **Free energy upper bound** (Glimm–Jaffe, Cor. 10.3.2 divided by `|ι|`):
for nonempty `ι`,
`f(G, p) ≤ log 2 + |β|·(|J|·|E| + |h|·|ι|) / |ι|`.

Obtained from `partitionFunction_upper` by taking the logarithm
(`Z ≤ 2^|ι| · exp(|β|·(|J|·|E| + |h|·|ι|))` implies
`log Z ≤ |ι|·log 2 + |β|·(|J|·|E| + |h|·|ι|)`) and dividing by `|ι|`. -/
theorem freeEnergy_upper_bound (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hne : 0 < Fintype.card ι) :
    freeEnergy G p ≤ Real.log 2 +
      |p.β| * (|p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι)
        / Fintype.card ι := by
  set A : ℝ :=
    |p.β| * (|p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι)
  have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hne
  have h_config_pos : (0 : ℝ) < (Fintype.card (Config ι) : ℝ) := by
    rw [card_config_eq_two_pow]; positivity
  have h_exp_pos : (0 : ℝ) < Real.exp A := Real.exp_pos _
  have hlog : Real.log (partitionFunction G p)
      ≤ (Fintype.card ι : ℝ) * Real.log 2 + A := by
    calc Real.log (partitionFunction G p)
        ≤ Real.log ((Fintype.card (Config ι) : ℝ) * Real.exp A) :=
          (Real.log_le_log_iff (partitionFunction_pos G p)
            (mul_pos h_config_pos h_exp_pos)).mpr (partitionFunction_upper G p)
      _ = Real.log (Fintype.card (Config ι) : ℝ) + A := by
          rw [Real.log_mul h_config_pos.ne' h_exp_pos.ne', Real.log_exp]
      _ = (Fintype.card ι : ℝ) * Real.log 2 + A := by
          rw [card_config_eq_two_pow]; push_cast; rw [Real.log_pow]
  unfold freeEnergy
  calc (Fintype.card ι : ℝ)⁻¹ * Real.log (partitionFunction G p)
      ≤ (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * Real.log 2 + A) :=
        mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hcard_pos.le)
    _ = Real.log 2 + A / (Fintype.card ι : ℝ) := by
        field_simp


end IsingModel
