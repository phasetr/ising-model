import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete finite-volume partition-function bounds

Narrow child module for direct concrete `latticeGraph` finite-volume
`partitionFunction` absolute-field, positivity, and ferromagnetic lower-bound
wrappers. The theorem names are the same as the former declarations, but
callers can now avoid importing the monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d direct finite-volume partition-function bounds -/

/-- **ℤ^d partitionFunction_eq_abs_h direct** at Λ-induced. -/
theorem partitionFunction_eq_abs_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, β⟩ : IsingParams ℝ)
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_eq_abs_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β

/-! ## Moved: ferromagnetic / |h|-monotonicity wrappers

The three wrappers
`partitionFunction_monotone_abs_h_latticeGraph`,
`partitionFunction_ge_one_of_ferromagnetic_latticeGraph`, and
`log_partitionFunction_nonneg_of_ferromagnetic_latticeGraph` now live
in `FiniteVolumePartitionBoundsFerromagnetic.lean`. -/


/-! ## Moved: ferromagnetic 2^|Λ| / (2 cosh)^|Λ| partition wrappers

The four wrappers
`partitionFunction_ge_two_pow_card_of_ferromagnetic_latticeGraph`,
`partitionFunction_ge_two_cosh_pow_card_of_ferromagnetic_latticeGraph`,
`log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic_latticeGraph`,
`log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic_latticeGraph`
now live in `FiniteVolumePartitionBoundsFerromagneticPow.lean`. -/

/-- **ℤ^d partitionFunction_pos direct** at Λ-induced: `0 < Z_Λ`. -/
theorem partitionFunction_pos_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    0 < IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.partitionFunction_pos
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d partitionFunction_ne_zero direct** at Λ-induced. -/
theorem partitionFunction_ne_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p ≠ 0 :=
  IsingModel.partitionFunction_ne_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

end Ambient
end IsingModel
