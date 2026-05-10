import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs

/-!
# Concrete Lambda-layer susceptibility wrappers

Narrow child module for concrete `latticeGraph` specializations of
`susceptibilityΛ` regularity and parameter-direction convergence wrappers.
The theorem names are the same as the former legacy declarations, but callers
can now avoid importing the monolithic concrete legacy module.
-/

namespace IsingModel
namespace Ambient

/-! ### susceptibility regularity ℤ^d wraps -/

/-- **ℤ^d Λ: susceptibility Continuous in `h`**. -/
theorem susceptibilityΛ_latticeGraph_continuous_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    Continuous (fun h' =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i) :=
  Ambient.susceptibilityΛ_continuous_field
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d Λ: susceptibility Differentiable in `h`**. -/
theorem susceptibilityΛ_latticeGraph_differentiable_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun h' =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i) :=
  Ambient.susceptibilityΛ_differentiable_field
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d Λ: susceptibility Continuous in `J`**. -/
theorem susceptibilityΛ_latticeGraph_continuous_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h β : ℝ) (i : ↑Λ) :
    Continuous (fun J' =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i) :=
  Ambient.susceptibilityΛ_continuous_J
    (IsingModel.latticeGraph d) Λ h β i

/-- **ℤ^d Λ: susceptibility Differentiable in `J`**. -/
theorem susceptibilityΛ_latticeGraph_differentiable_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h β : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun J' =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i) :=
  Ambient.susceptibilityΛ_differentiable_J
    (IsingModel.latticeGraph d) Λ h β i

/-! ### susceptibility parameter-direction convergent (β/h/J → ∞) ℤ^d wraps -/

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
