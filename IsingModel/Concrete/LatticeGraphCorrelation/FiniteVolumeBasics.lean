import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Vanishing coupling collapses a finite volume in ℤ^d to the edgeless graph

Records that the induced-subgraph construction on a finite `Λ ⊆ ℤ^d` is monotone in the
ambient graph, and that at zero coupling the finite-volume partition function and the
finite-volume correlations of the nearest-neighbor lattice graph agree with those of the
edgeless graph on the sites of `Λ`, whose correlations have the closed form
`tanh(β·h) ^ |A|`. Monotonicity is stated for an arbitrary pair of comparable graphs on
`ℤ^d` rather than for the nearest-neighbor one, and the closed form holds at an arbitrary
parameter record. The collapse statements fix the coupling at `0` inside the parameter
record instead of assuming an inequality, so apart from the graph inclusion in the
monotonicity statement no hypothesis is imposed anywhere here.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d inducedGraph_mono**: `G₁ ≤ G₂` lifts to `inducedGraph G₁ Λ ≤ inducedGraph G₂ Λ`. -/
theorem inducedGraph_mono_latticeGraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (h : G₁ ≤ G₂)
    (Λ : Finset (Fin d → ℤ)) :
    Ambient.inducedGraph G₁ Λ ≤ Ambient.inducedGraph G₂ Λ :=
  Ambient.inducedGraph_mono h Λ

/-- **ℤ^d `partitionFunction_eq_bot_at_J_zero`** at Λ-induced: at `J = 0`
the partition function is graph-independent (equals the `⊥`-graph value). -/
theorem partitionFunctionΛ_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = IsingModel.partitionFunction (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d `correlation_eq_bot_at_J_zero`** at Λ-induced: at `J = 0`
the correlation is graph-independent. -/
theorem correlationΛ_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = IsingModel.correlation (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β A

/-- **ℤ^d `correlation_bot_closed`** at Λ-induced:
`⟨σ^A⟩_⊥ = tanh(β·h)^|A|`. -/
theorem correlation_bot_closed_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation (⊥ : SimpleGraph (↑Λ : Type _)) p A
      = Real.tanh (p.β * p.h) ^ A.card :=
  IsingModel.correlation_bot_closed p A

end Ambient
end IsingModel
