import IsingModel.Inequalities.NonnegCorrelations

/-!
# ℤ^d hasNonnegCorrelations primitive wrappers

Narrow child module for four ℤ^d
`hasNonnegCorrelations_*_latticeGraph` primitive wrappers extracted
from `MagnetizationGksFkg.lean`:

* `hasNonnegCorrelations_one_latticeGraph`,
* `hasNonnegCorrelations_finset_prod_latticeGraph`,
* `hasNonnegCorrelations_mul_prod_latticeGraph`,
* `hasNonnegCorrelations_mul_latticeGraph`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d hasNonnegCorrelations_one direct** (Λ-induced):
the constant function `1` has HNC. -/
theorem hasNonnegCorrelations_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    IsingModel.HasNonnegCorrelations
      (ι := (↑Λ : Type _)) (fun _ => 1) :=
  IsingModel.hasNonnegCorrelations_one

/-- **ℤ^d hasNonnegCorrelations_finset_prod direct** (Λ-induced):
a product of `(a + b · σ^C)` factors over a Finset has HNC. -/
theorem hasNonnegCorrelations_finset_prod_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {α : Type*}
    (S : Finset α)
    (g : α → IsingModel.Config (↑Λ : Type _) → ℝ)
    (hg : ∀ a ∈ S, ∃ c e : ℝ, ∃ C : Finset (↑Λ : Type _), 0 ≤ c ∧ 0 ≤ e ∧
      ∀ σ, g a σ = c + e * IsingModel.spinProduct C σ) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      ∏ a ∈ S, g a σ := by
  classical
  exact IsingModel.hasNonnegCorrelations_finset_prod S g hg

/-- **ℤ^d hasNonnegCorrelations_mul_prod direct** (Λ-induced):
multiplying an HNC function by a product of `(a + b · σ^C)` factors
preserves HNC. -/
theorem hasNonnegCorrelations_mul_prod_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {α : Type*}
    (S : Finset α) {f : IsingModel.Config (↑Λ : Type _) → ℝ}
    (hf : IsingModel.HasNonnegCorrelations f)
    (g : α → IsingModel.Config (↑Λ : Type _) → ℝ)
    (hg : ∀ a ∈ S, ∃ c e : ℝ, ∃ C : Finset (↑Λ : Type _), 0 ≤ c ∧ 0 ≤ e ∧
      ∀ σ, g a σ = c + e * IsingModel.spinProduct C σ) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      f σ * ∏ a ∈ S, g a σ := by
  classical
  exact IsingModel.hasNonnegCorrelations_mul_prod S hf g hg

/-- **ℤ^d hasNonnegCorrelations_mul direct** (Λ-induced): if `f` has HNC
then so does `f · (a + b · σ^C)` for `a, b ≥ 0`. -/
theorem hasNonnegCorrelations_mul_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {f : IsingModel.Config (↑Λ : Type _) → ℝ}
    (hf : IsingModel.HasNonnegCorrelations f)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (C : Finset (↑Λ : Type _)) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      f σ * (a + b * IsingModel.spinProduct C σ) :=
  IsingModel.hasNonnegCorrelations_mul hf ha hb C

end Ambient
end IsingModel
