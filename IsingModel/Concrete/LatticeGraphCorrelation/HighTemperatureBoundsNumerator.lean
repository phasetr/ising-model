import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete HT FV (3.46) numerator and even-subgraph wrappers

Narrow child module for 4 ℤ^d Λ-level FV (3.46) numerator and
even-subgraph wrappers at `h = 0` extracted from
`HighTemperatureBounds.lean`:

* `sum_high_temp_numerator_h_zero_odd_card_eq_zero_latticeGraph`,
* `correlationΛ_latticeGraph_high_temp_h_zero_nonneg`,
* `one_le_sum_pow_tanh_even_subgraph_latticeGraph`,
* `high_temp_numerator_filter_eq_empty_of_odd_card_latticeGraph`.

Each result is a thin pass-through of the corresponding ambient
`sum_high_temp_numerator_*_Λ` / `correlationΛ_high_temp_*` /
`one_le_sum_pow_tanh_even_subgraph_Λ` /
`high_temp_numerator_filter_eq_empty_of_odd_card_Λ` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ-level FV (3.46) numerator vanishes for odd-cardinality A**
at `h = 0`: `∑_{X : ∂X = A} tanh(β J)^|X| = 0` for any `A` of odd
cardinality. ℤ^d wrapper of `sum_high_temp_numerator_h_zero_odd_card_eq_zero_Λ`. -/
theorem sum_high_temp_numerator_h_zero_odd_card_eq_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (A : Finset ↑Λ) (hA_odd : Odd A.card) :
    ∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑Λ) => ∀ v : ↑Λ,
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card = 0 :=
  sum_high_temp_numerator_h_zero_odd_card_eq_zero_Λ
    (IsingModel.latticeGraph d) Λ J β A hA_odd

/-- **ℤ^d Λ-level correlation nonnegativity from FV (3.46)** at `h = 0`:
under `0 ≤ β * J`, `0 ≤ correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ A`.
ℤ^d wrapper of `correlationΛ_high_temp_h_zero_nonneg`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (A : Finset ↑Λ) :
    0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) A :=
  correlationΛ_high_temp_h_zero_nonneg
    (IsingModel.latticeGraph d) Λ J β hβJ A

/-- **ℤ^d high-temperature even-subgraph sum is `≥ 1`**: under
`0 ≤ β * J`,
`∑_{X ⊆ E_Λ, even-degree} tanh(β J)^|X| ≥ 1` on the ℤ^d induced
subgraph. ℤ^d wrapper of `one_le_sum_pow_tanh_even_subgraph_Λ`. -/
theorem one_le_sum_pow_tanh_even_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (1 : ℝ) ≤ ∑ X ∈
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑Λ) =>
            ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card :=
  one_le_sum_pow_tanh_even_subgraph_Λ
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d FV (3.46) numerator filter is empty for odd-cardinality A**:
the filtered powerset is empty whenever `|A|` is odd.
ℤ^d wrapper of `high_temp_numerator_filter_eq_empty_of_odd_card_Λ`. -/
theorem high_temp_numerator_filter_eq_empty_of_odd_card_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A : Finset ↑Λ) (hA_odd : Odd A.card) :
    (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑Λ) => ∀ v : ↑Λ,
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)) = ∅ :=
  high_temp_numerator_filter_eq_empty_of_odd_card_Λ
    (IsingModel.latticeGraph d) Λ A hA_odd

end Ambient

end IsingModel
