import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper

/-!
# Ambient alongExhaustion correlation closed-form / nonnegativity wrappers at h = 0

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
correlation wrappers extracted from
`HighTemperatureBoundsExpansionClosed.lean`:

* `correlationAlongExhaustion_high_temp_h_zero_nonneg`
* `correlationAlongExhaustion_high_temp_expansion_h_zero_closed`

Each wrapper unfolds `correlationAlongExhaustion` and dispatches on
`A ⊆ Λ.volume n`, falling back to the trivial `0` case when the
finset lies outside the exhaustion. The non-trivial case lifts via
`liftFinset` and applies the corresponding `correlationΛ_*` ambient
lemma. Theorem names are unchanged from the former
`HighTemperatureBoundsExpansionClosedForms` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion correlation nonnegativity from FV (3.46)**:
under `0 ≤ β * J`, at every stage `n`,
`0 ≤ correlationAlongExhaustion G Λ ⟨J, 0, β⟩ A n`.
When `A ⊄ Λ.volume n`, equals `0` by definition. When `A ⊆`, lifts via
`liftFinset` and applies `correlationΛ_high_temp_h_zero_nonneg` (Step 294). -/
theorem correlationAlongExhaustion_high_temp_h_zero_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (A : Finset V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A n := by
  unfold correlationAlongExhaustion
  by_cases hAn : A ⊆ Λ.volume n
  · rw [dif_pos hAn]
    exact correlationΛ_high_temp_h_zero_nonneg G (Λ.volume n) J β hβJ
      (liftFinset A hAn)
  · rw [dif_neg hAn]

/-- **Along-exhaustion correlation high-temperature closed form (FV §3.7.3 eq. (3.46))**:
at every stage `n` with `A ⊆ Λ.volume n`, the per-stage correlation
admits the FV (3.46) ratio form. When `A ⊄ Λ.volume n`, the
along-exhaustion correlation is `0` by definition.

For the `A ⊆` case, lifts via `liftFinset` and applies
`correlationΛ_high_temp_expansion_h_zero_closed` (Step 285). -/
theorem correlationAlongExhaustion_high_temp_expansion_h_zero_closed
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (n : ℕ) (hAn : A ⊆ Λ.volume n) :
    correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A n =
      (∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑(Λ.volume n)) => ∀ v : ↑(Λ.volume n),
            Even ((if v ∈ liftFinset A hAn then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) /
      (∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
            ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) := by
  unfold correlationAlongExhaustion
  rw [dif_pos hAn]
  exact correlationΛ_high_temp_expansion_h_zero_closed G (Λ.volume n) J β
    (liftFinset A hAn)

/-- **Along-exhaustion general external-field high-temperature correlation
expansion (GJ §18.3/§18.5)**: at every stage `n` with `A ⊆ Λ.volume n` and
any Ising parameter `p = (J, h, β)`, the per-stage correlation admits the
general-`h` subset ratio form whose inner σ-sums carry the field weight
`exp(β h ∑_i σ_i)`. When `A ⊄ Λ.volume n`, the along-exhaustion correlation
is `0` by definition.

For the `A ⊆` case, lifts via `liftFinset` and applies
`correlationΛ_high_temp_expansion_general_h_subset_form`. General
external-field counterpart of
`correlationAlongExhaustion_high_temp_expansion_h_zero_closed`. -/
theorem correlationAlongExhaustion_high_temp_expansion_general_h_subset_form
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) (n : ℕ) (hAn : A ⊆ Λ.volume n) :
    correlationAlongExhaustion G Λ p A n =
      (∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ↑(Λ.volume n),
            spinProduct (liftFinset A hAn) σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h * ∑ i : ↑(Λ.volume n), Spin.sign ℝ (σ i))) /
      (∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ↑(Λ.volume n),
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h * ∑ i : ↑(Λ.volume n), Spin.sign ℝ (σ i))) := by
  unfold correlationAlongExhaustion
  rw [dif_pos hAn]
  exact correlationΛ_high_temp_expansion_general_h_subset_form G (Λ.volume n) p
    (liftFinset A hAn)

end Ambient

end IsingModel
