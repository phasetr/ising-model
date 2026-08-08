import IsingModel.Inequalities.NonnegCorrelations

/-!
# Spin-product algebra on the sites of a finite volume in ℤ^d

Records the configuration-sum and multiplicative identities for spin products over the
sites of a finite `Λ ⊆ ℤ^d`: summing `σ^A` over all configurations gives zero as soon as
`A` is nonempty and gives the number of configurations when `A` is empty; the product of
two spin products is the spin product of the symmetric difference of their index sets; and
a per-edge spin product squares to `1`. Nonemptiness of `A` is the only hypothesis anywhere
here, and no graph, interaction or parameter record enters these statements, which involve
`Λ` only through its site type.
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

end Ambient
end IsingModel
