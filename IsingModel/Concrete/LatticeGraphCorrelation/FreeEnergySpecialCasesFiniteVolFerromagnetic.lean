import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d finite-volume free-energy ferromagnetic / bot wrappers

Narrow child module for four ℤ^d Λ-induced finite-volume free-energy wrappers
extracted from `FreeEnergySpecialCasesFiniteVol.lean`:

* `card_mul_freeEnergy_eq_log_partitionFunction_latticeGraph`,
* `freeEnergy_ge_log_two_of_ferromagnetic_latticeGraph`,
* `freeEnergy_nonneg_of_ferromagnetic_latticeGraph`,
* `freeEnergy_bot_latticeGraph`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d card_mul_freeEnergy_eq_log_partitionFunction direct** (Λ-induced):
`|ι|·f = log Z` for nonempty Λ. -/
theorem card_mul_freeEnergy_eq_log_partitionFunction_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    (Fintype.card (↑Λ : Type _) : ℝ)
      * IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p
      = Real.log (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p) :=
  IsingModel.card_mul_freeEnergy_eq_log_partitionFunction
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hne

/-- **ℤ^d freeEnergy_ge_log_two_of_ferromagnetic at Λ-induced**:
`log 2 ≤ freeEnergy Λ p` for ferromagnetic `p` and nonempty Λ. -/
theorem freeEnergy_ge_log_two_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    Real.log 2
      ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.freeEnergy_ge_log_two_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf hne

/-- **ℤ^d freeEnergy_nonneg_of_ferromagnetic at Λ-induced**:
`0 ≤ freeEnergy G Λ p` for ferromagnetic `p` and nonempty Λ. -/
theorem freeEnergy_nonneg_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    0 ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.freeEnergy_nonneg_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf hne

/-- **ℤ^d freeEnergy_bot at Λ-induced type**: `freeEnergy ⊥ = log(2 cosh(βh))`. -/
theorem freeEnergy_bot_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy (⊥ : SimpleGraph (↑Λ : Type _)) p
      = Real.log (2 * Real.cosh (p.β * p.h)) :=
  IsingModel.freeEnergy_bot p hne

end Ambient
end IsingModel
