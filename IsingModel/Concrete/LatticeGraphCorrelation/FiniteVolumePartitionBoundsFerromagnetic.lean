import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete finite-volume partition-function ferromagnetic wrappers

Narrow child module for 3 ℤ^d `latticeGraph` finite-volume
`partitionFunction` ferromagnetic / |h|-monotonicity wrappers extracted
from `FiniteVolumePartitionBounds.lean`:

* `partitionFunction_monotone_abs_h_latticeGraph`,
* `partitionFunction_ge_one_of_ferromagnetic_latticeGraph`,
* `log_partitionFunction_nonneg_of_ferromagnetic_latticeGraph`.

Each is a thin pass-through to the corresponding abstract
`IsingModel.partitionFunction_*` lemma at
`Ambient.inducedGraph (latticeGraph d) Λ`. The theorem names are
unchanged from the former `FiniteVolumePartitionBounds` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunction_monotone_abs_h direct** at Λ-induced
(ferromagnetic). -/
theorem partitionFunction_monotone_abs_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_monotone_abs_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ hh

/-- **ℤ^d partitionFunction_ge_one_of_ferromagnetic direct** (Λ-induced). -/
theorem partitionFunction_ge_one_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (1 : ℝ) ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.partitionFunction_ge_one_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

/-- **ℤ^d log_partitionFunction_nonneg_of_ferromagnetic direct** (Λ-induced). -/
theorem log_partitionFunction_nonneg_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ Real.log (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p) :=
  IsingModel.log_partitionFunction_nonneg_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

end Ambient
end IsingModel
