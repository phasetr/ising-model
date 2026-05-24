import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivative
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivativeSuscSq
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivativeHighTemp
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Analysis.BoundedVariation

/-!
# Lattice mass high-temp Lipschitz split — pointwise high-temperature beta-derivative absolute bound

Part of the split high-temperature Lipschitz layer (Issue #1850).
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Pointwise high-temperature β-derivative absolute bound** (Step 166 to
Step 167 bridge, GJ §17.5): for each finite stage and `β ∈ [a,b]`, the
β-derivative of the two-point correlation exists and has absolute value bounded
by the uniform high-temperature constant
`J * M^2 + J * 4d`, where `M = bJ·2d / (1 - bJ·2d)`.

This exposes the pointwise derivative estimate that is used internally by the
finite-stage Lipschitz theorem below. It is the concrete Lebowitz/susceptibility
input that downstream HLS pseudo-mass estimates must compare with
`K * c β / (m⁻ β)^(2α)`. -/
theorem inducedLatticeGraph_beta_deriv_abs_le_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (β : ℝ) (hβ : β ∈ Set.Icc a b) :
    let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    ∃ dval : ℝ,
      HasDerivAt
        (fun β' => IsingModel.correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s})
        dval β ∧
      |dval| ≤ J * M ^ 2 + J * (4 * ↑d) := by
  intro G M
  have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
  have hb_pos : 0 < b := ha.trans_le hab
  have hM_nn : 0 ≤ M :=
    div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ) (Nat.cast_nonneg _)) hdenom_b.le
  obtain ⟨dval, hd, hbound⟩ :=
    inducedLatticeGraph_beta_deriv_le_susc_sq_high_temp Λ J β hJ
      (ha.trans_le hβ.1)
      (by have : β ≤ b := hβ.2; nlinarith [mul_le_mul_of_nonneg_right this
            (mul_nonneg hJ (Nat.cast_nonneg (2 * d)))])
      n r s hrs
  have hβ_pos : 0 < β := ha.trans_le hβ.1
  have hmono : MonotoneOn
      (fun β' => IsingModel.correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) (Set.Ici 0) :=
    IsingModel.correlation_monotoneOn_beta G J hJ {r, s}
  have hacc : AccPt β (Filter.principal (Set.Ici 0)) := by
    rw [accPt_principal_iff_nhdsWithin]
    exact (right_nhdsWithin_Ioo_neBot hβ_pos).mono
      (nhdsWithin_mono β (fun x hx => ⟨le_of_lt hx.1, ne_of_lt hx.2⟩))
  have hdnn : 0 ≤ dval :=
    hd.hasDerivWithinAt.nonneg_of_monotoneOn hacc hmono
  have hβJ : 0 ≤ β * J := mul_nonneg hβ_pos.le hJ
  have hlt_β : β * J * ↑(2 * d) < 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hβ.2
                (mul_nonneg hJ (Nat.cast_nonneg (2 * d)))]
  have hsusc_r : susceptibilityInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) r.val ≤ M := by
    calc susceptibilityInfinite _ Λ _ r.val
        ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
          IsingModel.Ambient.susceptibilityInfinite_latticeGraph_le_of_high_temp_gen
            Λ hβJ hlt_β r.val
      _ ≤ M := by
          have hdenom_β : 0 < 1 - β * J * ↑(2 * d) := by linarith
          rw [div_le_div_iff₀ hdenom_β hdenom_b]
          nlinarith [mul_le_mul_of_nonneg_right hβ.2
                      (mul_nonneg hJ (Nat.cast_nonneg (2 * d)))]
  have hsusc_s : susceptibilityInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) s.val ≤ M := by
    calc susceptibilityInfinite _ Λ _ s.val
        ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
          IsingModel.Ambient.susceptibilityInfinite_latticeGraph_le_of_high_temp_gen
            Λ hβJ hlt_β s.val
      _ ≤ M := by
          have hdenom_β : 0 < 1 - β * J * ↑(2 * d) := by linarith
          rw [div_le_div_iff₀ hdenom_β hdenom_b]
          nlinarith [mul_le_mul_of_nonneg_right hβ.2
                      (mul_nonneg hJ (Nat.cast_nonneg (2 * d)))]
  have hsusc_s_nn : 0 ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) s.val :=
    IsingModel.Ambient.susceptibilityInfinite_nonneg _ Λ _ ⟨hJ, le_refl 0, hβ_pos⟩ _
  have hdval_le : dval ≤ J * M ^ 2 + J * (4 * ↑d) :=
    calc dval ≤ J * susceptibilityInfinite _ Λ _ r.val *
                susceptibilityInfinite _ Λ _ s.val + J * (4 * ↑d) := hbound
         _ ≤ J * M ^ 2 + J * (4 * ↑d) := by
              nlinarith [mul_le_mul hsusc_r hsusc_s hsusc_s_nn hM_nn,
                         mul_nonneg hJ (pow_nonneg hM_nn 2)]
  refine ⟨dval, hd, ?_⟩
  rwa [abs_of_nonneg hdnn]


end Ambient
end IsingModel
