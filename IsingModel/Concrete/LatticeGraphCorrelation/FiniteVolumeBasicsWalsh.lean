import IsingModel.InfiniteVolume.Boundedness

/-!
# The Walsh system on configurations of a finite volume in ℤ^d

Records the orthogonality, normalization, completeness and inversion identities for the
Walsh functions `σ ↦ σ^S` indexed by subsets `S` of a finite `Λ ⊆ ℤ^d`. Summed over
configurations, distinct index sets give zero and a repeated index set gives the number of
configurations; summed over index sets, `σ^S(σ)·σ^S(τ)` detects equality of the two
configurations; and every real function of a configuration is recovered from its Walsh
coefficients. The number of configurations is itself `2` raised to the number of sites.
Distinctness of the index sets in the orthogonality statement is the only hypothesis
anywhere here, and no graph, interaction or parameter record enters.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d Walsh orthogonality at Λ-induced**. -/
theorem walsh_orthogonality_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (S T : Finset (↑Λ : Type _)) (hST : S ≠ T) :
    ∑ σ : IsingModel.Config (↑Λ : Type _),
      IsingModel.spinProduct S σ * IsingModel.spinProduct T σ = 0 :=
  IsingModel.walsh_orthogonality S T hST

/-- **ℤ^d Walsh completeness at Λ-induced**:
`Σ_S σ^S(σ) σ^S(τ) = card · [σ = τ]`. -/
theorem walsh_completeness_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (σ τ : IsingModel.Config (↑Λ : Type _)) :
    ∑ S : Finset (↑Λ : Type _),
        IsingModel.spinProduct S σ * IsingModel.spinProduct S τ
      = if σ = τ then (Fintype.card (IsingModel.Config (↑Λ : Type _)) : ℝ) else 0 :=
  IsingModel.walsh_completeness σ τ

/-- **ℤ^d Walsh Fourier inversion at Λ-induced**:
`f(σ) = Σ_S ĉ_S σ^S` where `ĉ_S = card⁻¹ Σ_τ σ^S(τ) f(τ)`. -/
theorem walsh_fourier_inversion_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (f : IsingModel.Config (↑Λ : Type _) → ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    f σ = ∑ S : Finset (↑Λ : Type _),
      ((Fintype.card (IsingModel.Config (↑Λ : Type _)) : ℝ)⁻¹
        * ∑ τ : IsingModel.Config (↑Λ : Type _),
            IsingModel.spinProduct S τ * f τ)
      * IsingModel.spinProduct S σ :=
  IsingModel.walsh_fourier_inversion f σ

/-- **ℤ^d Walsh normalization at Λ-induced**. -/
theorem walsh_normalization_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (S : Finset (↑Λ : Type _)) :
    ∑ σ : IsingModel.Config (↑Λ : Type _),
        IsingModel.spinProduct S σ * IsingModel.spinProduct S σ
      = Fintype.card (IsingModel.Config (↑Λ : Type _)) :=
  IsingModel.walsh_normalization S

/-- **ℤ^d `card_config_eq_two_pow` at Λ**:
`|Config ↑Λ| = 2^|Λ|`. -/
theorem card_config_eq_two_pow_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Fintype.card (IsingModel.Config (↑Λ : Type _))
      = 2 ^ Fintype.card (↑Λ : Type _) :=
  IsingModel.card_config_eq_two_pow

end Ambient
end IsingModel
