import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `spontaneousCorrelation_latticeGraph_*` wrappers

Narrow child module for three ℤ^d
`spontaneousCorrelation_latticeGraph_*` trivial-slice wrappers
extracted from `UniformMag.lean`:

* `spontaneousCorrelation_latticeGraph_J_zero` (Step 272),
* `spontaneousCorrelation_latticeGraph_beta_zero` (Step 272),
* `spontaneousCorrelation_latticeGraph_empty` (Step 274).

Each result is a thin pass-through of the ambient
`Ambient.spontaneousCorrelation_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `UniformMag` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d spontaneousCorrelation at J = 0 general nonempty A** (Step 272). -/
theorem spontaneousCorrelation_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ 0 β A = 0 :=
  spontaneousCorrelation_J_zero (IsingModel.latticeGraph d) Λ hβ A hA

/-- **ℤ^d spontaneousCorrelation at β = 0 general nonempty A** (Step 272). -/
theorem spontaneousCorrelation_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J : ℝ)
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J 0 A = 0 :=
  spontaneousCorrelation_beta_zero (IsingModel.latticeGraph d) Λ J A hA

/-- **ℤ^d spontaneousCorrelation at empty A is 1** (Step 274). -/
theorem spontaneousCorrelation_latticeGraph_empty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β
        (∅ : Finset (Fin d → ℤ)) = 1 :=
  spontaneousCorrelation_empty (IsingModel.latticeGraph d) Λ J β

end Ambient
end IsingModel
