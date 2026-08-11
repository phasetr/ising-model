import IsingModel.AmbientLattice.CorrelationInfinite.AmbientSubgraph

/-!
# Infinite-volume GKS-II prelude

Helpers for lifting GKS-II to infinite-volume correlations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## GKS-II (second Griffiths inequality) at infinite volume

Lift the finite-volume second Griffiths inequality (`gks_second`,
`Inequalities/GKS.lean`) to the thermodynamic limit. For ferromagnetic
Ising and any two finite subsets `A, B`,
`correlationInfinite A * correlationInfinite B ≤ correlationInfinite (A ∆ B)`.

Reference: Glimm-Jaffe, *Quantum Physics* §4.1 Theorem 4.1.3, (4.1.11),
p. 57 (GKS-II), here taken to the infinite-volume limit; in the Ising case
`σ² = 1` gives the symmetric-difference form used above.  Friedli-Velenik
Thm 3.49 for the finite-volume version. -/

/-- Helper: if `A ⊆ Λ` and `B ⊆ Λ` then `A ∆ B ⊆ Λ`. -/
theorem symmDiff_subset_of_subset
    {A B Λ : Finset V} (hA : A ⊆ Λ) (hB : B ⊆ Λ) :
    A ∆ B ⊆ Λ :=
  fun _ hx => (Finset.mem_symmDiff.mp hx).elim (fun h => hA h.1) (fun h => hB h.1)

/-- `correlationAlongExhaustion` is always `≥ 0` for a ferromagnetic
Ising model: either the value is `0` (when `A ⊄ Λ.volume n`) or it is
`correlationΛ ≥ 0` by GKS-I (`correlationΛ_nonneg`). -/
theorem correlationAlongExhaustion_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ p A n := by
  by_cases hA : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ p hA]
    exact correlationΛ_nonneg G (Λ.volume n) p hf _
  · rw [correlationAlongExhaustion_of_not_subset G Λ p hA]

end Ambient
end IsingModel
