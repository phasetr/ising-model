import IsingModel.AmbientLattice.Monotonicity.Factoring

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Volume-direction monotonicity main theorem

Combining `correlationΛ_extendGraph_eq` (correlation equality via config
factoring) with `extendGraphFromΛ₁_le_induce` + `correlation_monotone_subgraph`
(subgraph monotonicity on `↑Λ₂`), we obtain the main volume-direction
monotonicity theorem. -/

/-- **Volume-direction monotonicity** (main theorem of the ambient
framework): for ferromagnetic `p`, `A ⊆ Λ₁ ⊆ Λ₂ : Finset V`,
`⟨σ^A⟩_{G, Λ₁} ≤ ⟨σ^A⟩_{G, Λ₂}`. -/
theorem correlationΛ_monotone_volume
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset V} (hA : A ⊆ Λ₁) :
    correlationΛ G Λ₁ p (liftFinset A hA)
      ≤ correlationΛ G Λ₂ p (liftFinset A (hA.trans h12)) := by
  classical
  haveI : Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet :=
    Fintype.ofFinite _
  unfold correlationΛ
  rw [← correlationΛ_extendGraph_eq G h12 p hA]
  exact correlation_monotone_subgraph
    (extendGraphFromΛ₁_le_induce G Λ₁ Λ₂) p hf _



end Ambient
end IsingModel
