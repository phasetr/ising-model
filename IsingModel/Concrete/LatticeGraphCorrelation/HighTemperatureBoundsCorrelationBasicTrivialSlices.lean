import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d fixed-volume correlations vanish on the trivial slices `J = 0` and `β = 0`

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the vanishing of
`correlationΛ` on a singleton `{i}` and on a pair `{i, j}` at the parameter records
`⟨0, 0, β⟩` and `⟨J, 0, 0⟩`. The vanishing coupling or vanishing inverse temperature is fixed
inside the parameter record rather than assumed, so no hypothesis is carried by any statement
here.
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
