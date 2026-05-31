import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSOverloadedNamespace

/-!
# Substantive HLS positivity helpers bundle

GJ-proposition-unit bundle of positivity / nonneg helpers for the
substantive HLS chain.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Positivity helpers -/

/-- **`0 ≤ β·J`** from `Ferromagnetic`. -/
theorem hls_betaJ_nonneg
    {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    (0 : ℝ) ≤ β * J :=
  mul_nonneg hf.hβ.le hf.hJ

/-- **`0 ≤ β·J·(2d)`** from `Ferromagnetic`. -/
theorem hls_betaJ_two_d_nonneg
    {J β : ℝ} {d : ℕ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    (0 : ℝ) ≤ β * J * ↑(2 * d) :=
  mul_nonneg (hls_betaJ_nonneg hf) (by positivity)

/-- **`0 ≤ susceptibility upper bound`**. -/
theorem hls_susceptibility_bound_nonneg
    {β J : ℝ} {d : ℕ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) := by
  have h_denom_pos : (0 : ℝ) < 1 - β * J * ↑(2 * d) := by linarith
  exact div_nonneg (hls_betaJ_two_d_nonneg hf) h_denom_pos.le

/-- **`0 < d`** from `1 ≤ d`. -/
theorem hls_d_pos_of_hd
    {d : ℕ} (hd : 1 ≤ d) :
    0 < d := hd

/-- **`0 < β·J·(2d)`** from `Ferromagnetic + 0 < β·J + 0 < d`. -/
theorem hls_betaJd_pos_of_betaJ_pos
    {β J : ℝ} {d : ℕ} (hd_pos : 0 < d) (hβJ : 0 < β * J) :
    0 < β * J * (2 * d) := by
  have h2d_pos : (0 : ℝ) < 2 * d := by positivity
  exact mul_pos hβJ h2d_pos

end Ambient
end IsingModel
