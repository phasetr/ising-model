import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.Convergent

/-!
# ℤ^d Λ-layer susceptibility parameter-direction convergent wrappers

Narrow child module for three ℤ^d
`susceptibilityΛ_latticeGraph_convergent_*` wrappers extracted from
`SusceptibilityLambda.lean`:

* `susceptibilityΛ_latticeGraph_convergent_beta`,
* `susceptibilityΛ_latticeGraph_convergent_h`,
* `susceptibilityΛ_latticeGraph_convergent_J`.

Each result is a thin pass-through of the ambient
`Ambient.susceptibilityΛ_convergent_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `SusceptibilityLambda` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: susceptibility β → ∞ convergence**. -/
theorem susceptibilityΛ_latticeGraph_convergent_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => Ambient.susceptibilityΛ (IsingModel.latticeGraph d)
        Λ (⟨J, h, (n + 1 : ℝ)⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) :=
  Ambient.susceptibilityΛ_convergent_beta
    (IsingModel.latticeGraph d) Λ J hJ h hh i

/-- **ℤ^d Λ: susceptibility h → ∞ convergence**. -/
theorem susceptibilityΛ_latticeGraph_convergent_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => Ambient.susceptibilityΛ (IsingModel.latticeGraph d)
        Λ (⟨J, (n : ℝ), β⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) :=
  Ambient.susceptibilityΛ_convergent_h
    (IsingModel.latticeGraph d) Λ J hJ β hβ i

/-- **ℤ^d Λ: susceptibility J → ∞ convergence**. -/
theorem susceptibilityΛ_latticeGraph_convergent_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => Ambient.susceptibilityΛ (IsingModel.latticeGraph d)
        Λ (⟨(n : ℝ), h, β⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) :=
  Ambient.susceptibilityΛ_convergent_J
    (IsingModel.latticeGraph d) Λ h hh β hβ i

end Ambient
end IsingModel
