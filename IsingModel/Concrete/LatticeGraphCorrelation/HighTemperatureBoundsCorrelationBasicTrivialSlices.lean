import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete HT correlation basic trivial-slice wrappers (J = 0, β = 0)

Narrow child module for 4 ℤ^d Λ-level correlation `h = 0` trivial-slice
wrappers extracted from `HighTemperatureBoundsCorrelationBasic.lean`:

* `correlationΛ_latticeGraph_high_temp_h_zero_at_singleton_J_zero`,
* `correlationΛ_latticeGraph_high_temp_h_zero_at_pair_J_zero`,
* `correlationΛ_latticeGraph_high_temp_h_zero_at_singleton_beta_zero`,
* `correlationΛ_latticeGraph_high_temp_h_zero_at_pair_beta_zero`.

Each result is a thin pass-through of the corresponding ambient
`correlationΛ_high_temp_h_zero_at_*_{J,beta}_zero` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `HighTemperatureBoundsCorrelationBasic` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ singleton at J=0,h=0**: = 0. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_singleton_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) (i : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_singleton_J_zero
    (IsingModel.latticeGraph d) Λ β i

/-- **ℤ^d Λ pair at J=0,h=0**: = 0. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_pair_J_zero
    (IsingModel.latticeGraph d) Λ β i j

/-- **ℤ^d Λ singleton at β=0,h=0**: = 0. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_singleton_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (i : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_singleton_beta_zero
    (IsingModel.latticeGraph d) Λ J i

/-- **ℤ^d Λ pair at β=0,h=0**: = 0. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_pair_beta_zero
    (IsingModel.latticeGraph d) Λ J i j

end Ambient

end IsingModel
