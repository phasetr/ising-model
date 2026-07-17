import IsingModel.Inequalities.NonnegCorrelations

/-!
# Concrete spinProduct + edgeSpin algebra wrappers

Narrow child module for seven ℤ^d spinProduct / edgeSpin algebra
wrappers (`sum_config_spinProduct_*`, `spinProduct_mul`, `edgeSpin_sq`,
`one_sub_spinProduct_nonneg`, `abs_spinProduct_*`). Each wrapper is a
thin pass-through to the corresponding `IsingModel.*` lemma.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d sum_config_spinProduct_eq_zero at Λ-induced**:
for nonempty `A`, `Σ_σ σ^A = 0`. -/
theorem sum_config_spinProduct_eq_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    ∑ σ : IsingModel.Config (↑Λ : Type _), IsingModel.spinProduct A σ = 0 :=
  IsingModel.sum_config_spinProduct_eq_zero A hA

/-- **ℤ^d sum_config_spinProduct_empty at Λ-induced**:
`Σ_σ σ^∅ = |Config ↑Λ|`. -/
theorem sum_config_spinProduct_empty_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    ∑ σ : IsingModel.Config (↑Λ : Type _), IsingModel.spinProduct ∅ σ
      = (Fintype.card (IsingModel.Config (↑Λ : Type _)) : ℝ) :=
  IsingModel.sum_config_spinProduct_empty

/-- **ℤ^d spinProduct_mul at Λ-induced**:
`σ^A · σ^C = σ^{A Δ C}`. -/
theorem spinProduct_mul_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A C : Finset (↑Λ : Type _)) (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct A σ * IsingModel.spinProduct C σ
      = IsingModel.spinProduct (symmDiff A C) σ :=
  IsingModel.spinProduct_mul A C σ

/-- **ℤ^d edgeSpin_sq at Λ-induced**: `edgeSpin σ e ^ 2 = 1`. -/
theorem edgeSpin_sq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (σ : IsingModel.Config (↑Λ : Type _)) (e : Sym2 (↑Λ : Type _)) :
    IsingModel.edgeSpin (K := ℝ) σ e ^ 2 = 1 :=
  IsingModel.edgeSpin_sq σ e

/-! ## Moved: spinProduct nonneg / abs wrappers

The three wrappers
`one_sub_spinProduct_nonneg_latticeGraph`,
`abs_spinProduct_eq_one_latticeGraph`,
`abs_spinProduct_le_one_latticeGraph` now live in
`FiniteVolumeBasicsSpinBounds.lean`. -/


end Ambient
end IsingModel
