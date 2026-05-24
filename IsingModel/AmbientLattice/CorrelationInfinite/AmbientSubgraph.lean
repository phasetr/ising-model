import IsingModel.AmbientLattice.CorrelationInfinite.ExhaustionIndependence

/-!
# Infinite-volume correlation ambient-subgraph monotonicity

Monotonicity of along-exhaustion and infinite-volume correlations in the ambient subgraph.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Ambient-subgraph monotonicity of infinite-volume correlation

Finite-volume monotonicity in the ambient subgraph
(`correlationΛ_monotone_ambient_subgraph`, PR #58) lifts to the
thermodynamic-limit correlation: for ferromagnetic Ising on an
ambient type `V` and exhaustion `Λ`, `G₁ ≤ G₂` implies
`correlationInfinite G₁ Λ p A ≤ correlationInfinite G₂ Λ p A`. -/

/-- **Ambient-subgraph monotonicity of `correlationAlongExhaustion`**:
if `G₁ ≤ G₂` then the exhaustion sequence is pointwise monotone in
the ambient subgraph. -/
theorem correlationAlongExhaustion_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G₁ Λ p A n
      ≤ correlationAlongExhaustion G₂ Λ p A n := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G₁ Λ p hAn,
        correlationAlongExhaustion_of_subset G₂ Λ p hAn]
    exact correlationΛ_monotone_ambient_subgraph h (Λ.volume n) p hf _
  · rw [correlationAlongExhaustion_of_not_subset G₁ Λ p hAn,
        correlationAlongExhaustion_of_not_subset G₂ Λ p hAn]

/-- **Ambient-subgraph monotonicity of `correlationInfinite`**:
if `G₁ ≤ G₂` then
`correlationInfinite G₁ Λ p A ≤ correlationInfinite G₂ Λ p A`.

Proof: pointwise monotonicity of the exhaustion sequence
(`correlationAlongExhaustion_monotone_ambient_subgraph`) combined
with `le_ciSup` and `ciSup_le`. -/
theorem correlationInfinite_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    correlationInfinite G₁ Λ p A ≤ correlationInfinite G₂ Λ p A := by
  refine ciSup_le ?_
  intro n
  exact (correlationAlongExhaustion_monotone_ambient_subgraph h Λ p hf A n).trans
    (le_ciSup (correlationAlongExhaustion_bddAbove G₂ Λ p A) n)

/-- **Magnetization along-exhaustion ambient-subgraph monotonicity**:
per stage, for `G₁ ≤ G₂` and ferromagnetic `p`. Specialization of
`correlationAlongExhaustion_monotone_ambient_subgraph` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G₁ Λ p i n
      ≤ magnetizationAlongExhaustion G₂ Λ p i n :=
  correlationAlongExhaustion_monotone_ambient_subgraph h Λ p hf {i} n

end Ambient
end IsingModel
