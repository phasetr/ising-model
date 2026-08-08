import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Extensive ferromagnetic lower bounds on the finite-volume partition function in ℤ^d

Records that under the ferromagnetic condition the partition function of the subgraph
induced by the nearest-neighbor lattice graph on a finite `Λ ⊆ ℤ^d` is bounded below by `2`
and by `2·cosh(β·h)`, each raised to the number of sites, in the multiplicative form and in
the logarithmic form alike. The ferromagnetic condition is the only hypothesis, and `Λ` is
not required to be nonempty.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d partitionFunction_ge_two_pow_card_of_ferromagnetic direct** (Λ-induced). -/
theorem partitionFunction_ge_two_pow_card_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (2 : ℝ) ^ Fintype.card (↑Λ : Type _)
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.partitionFunction_ge_two_pow_card_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

/-- **ℤ^d partitionFunction_ge_two_cosh_pow_card_of_ferromagnetic direct**
(Λ-induced). -/
theorem partitionFunction_ge_two_cosh_pow_card_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (2 * Real.cosh (p.β * p.h)) ^ Fintype.card (↑Λ : Type _)
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.partitionFunction_ge_two_cosh_pow_card_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

/-- **ℤ^d log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic direct**
(Λ-induced). -/
theorem log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Fintype.card (↑Λ : Type _) : ℝ) * Real.log 2
      ≤ Real.log (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p) :=
  IsingModel.log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

/-- **ℤ^d log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic direct**
(Λ-induced). -/
theorem log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Fintype.card (↑Λ : Type _) : ℝ) * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p) :=
  IsingModel.log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf


end Ambient
end IsingModel
