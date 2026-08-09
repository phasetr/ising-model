import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityConvergence

/-!
# ℤ^d along-exhaustion susceptibility as a parameter grows without bound

Concrete `latticeGraph d` statements that, at a fixed site of `Fin d → ℤ` and a fixed stage
of an arbitrary `Ambient.Exhaustion`, the susceptibility of that stage converges when one
parameter is sampled along the natural numbers and the others are held fixed. Growth of the
inverse temperature, taken shifted by one, assumes `0 ≤ J` and `0 ≤ h`; growth of the
external field assumes `0 ≤ J` and `0 < β`; growth of the coupling assumes `0 ≤ h` and
`0 < β`. Each statement also requires a `Fintype` instance on the edge set induced at every
stage.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: susceptibility β → ∞ convergence**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_convergent_beta_param
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : Fin d → ℤ) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => Ambient.susceptibilityAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) :=
  Ambient.susceptibilityAlongExhaustion_convergent_beta_param
    (IsingModel.latticeGraph d) Λ J hJ h hh i n

/-- **ℤ^d along-ex: susceptibility h → ∞ convergence**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_convergent_h_param
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : Fin d → ℤ) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => Ambient.susceptibilityAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) :=
  Ambient.susceptibilityAlongExhaustion_convergent_h_param
    (IsingModel.latticeGraph d) Λ J hJ β hβ i n

/-- **ℤ^d along-ex: susceptibility J → ∞ convergence**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_convergent_J_param
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : Fin d → ℤ) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => Ambient.susceptibilityAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) :=
  Ambient.susceptibilityAlongExhaustion_convergent_J_param
    (IsingModel.latticeGraph d) Λ h hh β hβ i n

end Ambient
end IsingModel
