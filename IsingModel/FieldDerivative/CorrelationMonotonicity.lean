import IsingModel.FieldDerivative.Basic
import IsingModel.Inequalities.GKS

/-!
# Field monotonicity of correlations

GKS-II consequence for nonnegative field derivatives of finite-volume correlations.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Monotonicity in h (Step 121): GKS-II-based bound -/

omit [DecidableEq ι] in
/-- `totalMagnetization σ = Σ_i spinProduct {i} σ`. -/
private lemma totalMagnetization_eq_sum_spinProduct (σ : Config ι) :
    totalMagnetization σ = ∑ i : ι, spinProduct {i} σ := by
  simp [totalMagnetization, spinProduct]

/-- `spinProduct A σ * totalMagnetization σ = Σ_i spinProduct (symmDiff A {i}) σ`. -/
private lemma spinProduct_mul_totalMagnetization (A : Finset ι) (σ : Config ι) :
    spinProduct A σ * totalMagnetization σ =
    ∑ i : ι, spinProduct (symmDiff A {i}) σ := by
  rw [totalMagnetization_eq_sum_spinProduct, Finset.mul_sum]
  congr 1; ext i
  exact spinProduct_mul A {i} σ

/-- `⟨spinProduct A · M⟩_p = Σ_i ⟨σ^{AΔ{i}}⟩_p`. -/
lemma gibbsExpectation_spinProd_mul_mag
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    gibbsExpectation G p (fun σ => spinProduct A σ * totalMagnetization σ) =
    ∑ i : ι, correlation G p (symmDiff A {i}) := by
  simp_rw [spinProduct_mul_totalMagnetization, correlation, gibbsExpectation,
           Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- `⟨M⟩_p = Σ_i correlation G p {i}`. -/
lemma gibbsExpectation_totalMag_eq_sum
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    gibbsExpectation G p totalMagnetization = ∑ i : ι, correlation G p {i} := by
  simp_rw [correlation, gibbsExpectation, totalMagnetization_eq_sum_spinProduct,
           Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The h-derivative of correlations is nonneg (infinitesimal form of h-monotonicity).

`d/dh ⟨σ^A⟩_h = β · Σ_i (⟨σ^{AΔ{i}}⟩ - ⟨σ^A⟩·⟨σ_i⟩) ≥ 0`

by GKS-II: each term `⟨σ^{AΔ{i}}⟩ - ⟨σ^A⟩·⟨σ_i⟩ ≥ 0` for ferromagnetic `h ≥ 0`.
This is the infinitesimal form underlying the monotonicity of correlations in `h`.

Reference: Glimm–Jaffe §4.2, Proposition 4.2.1, p. 58, applied to the
singleton couplings that carry `h`;
Glimm–Jaffe §17.6 pp. 348–351 (derivative formula). -/
theorem correlation_field_deriv_nonneg
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (A : Finset ι)
    (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ)) :
    0 ≤ β * (gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ)
              (fun σ => spinProduct A σ * totalMagnetization σ) -
            correlation G (⟨J, h, β⟩ : IsingParams ℝ) A *
            gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) totalMagnetization) := by
  apply mul_nonneg hf.hβ.le
  rw [gibbsExpectation_spinProd_mul_mag, gibbsExpectation_totalMag_eq_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro i _
  linarith [gks_second G (⟨J, h, β⟩ : IsingParams ℝ) hf A {i}]

end IsingModel
