import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete finite-volume basic wrappers

Narrow child module for concrete `latticeGraph` finite-volume graph, spin
algebra, bottom-graph, and Hamiltonian symmetry wrappers. The theorem names are
the same as the former declarations, but callers can now avoid importing
the monolithic concrete module.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### ℤ^d finite-volume basic wrappers -/

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

/-- **ℤ^d `correlation_bot_closed`** at Λ-induced:
`⟨σ^A⟩_⊥ = tanh(β·h)^|A|`. -/
theorem correlation_bot_closed_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation (⊥ : SimpleGraph (↑Λ : Type _)) p A
      = Real.tanh (p.β * p.h) ^ A.card :=
  IsingModel.correlation_bot_closed p A

/-! ## Moved: spinProduct + edgeSpin algebra wrappers

The four wrappers
`sum_config_spinProduct_{eq_zero,empty}_latticeGraph`,
`spinProduct_mul_latticeGraph`, and `edgeSpin_sq_latticeGraph`
now live in `FiniteVolumeBasicsSpin.lean`. -/


/-! ## Moved: Walsh basis + spin-config wrappers

The five wrappers
`walsh_{orthogonality,completeness,fourier_inversion,normalization}_latticeGraph`
and `card_config_eq_two_pow_latticeGraph` now live in
`FiniteVolumeBasicsWalsh.lean`. -/


/-! ## Moved: Hamiltonian flip / symmetry wrappers

The three wrappers
`edgeSpin_flip_latticeGraph`, `interactionEnergy_flip_latticeGraph`,
and `hamiltonian_bot_latticeGraph` now live in
`FiniteVolumeBasicsHamiltonian.lean`. The spin-flip invariance at `h = 0` and
the `h ↦ -h` reflection are stated once, in `EnergyClosedFormsHamiltonian.lean`,
as `hamiltonian_flip_eq_latticeGraph` and `hamiltonian_neg_h_latticeGraph`. -/


end Ambient
end IsingModel
