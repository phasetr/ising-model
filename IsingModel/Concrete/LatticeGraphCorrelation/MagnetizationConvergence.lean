import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.Magnetization

/-!
# ℤ^d along-exhaustion magnetization as a parameter grows without bound

Concrete `latticeGraph d` statements that, at a fixed site of `Fin d → ℤ` and a fixed stage
of an arbitrary `Ambient.Exhaustion`, the magnetization of that stage converges when one
parameter is sampled along the natural numbers and the others are held fixed. Growth of the
inverse temperature, taken shifted by one, assumes `0 ≤ J` and `0 ≤ h`; growth of the
external field assumes `0 ≤ J` and `0 < β`; growth of the coupling assumes `0 ≤ h` and
`0 < β`. Each statement also requires a `Fintype` instance on the edge set induced at every
stage.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: magnetization β → ∞ convergence**. -/
theorem magnetizationAlongExhaustion_latticeGraph_convergent_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : Fin d → ℤ) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => Ambient.magnetizationAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) :=
  Ambient.magnetizationAlongExhaustion_convergent_beta
    (IsingModel.latticeGraph d) Λ J hJ h hh i n

/-- **ℤ^d along-ex: magnetization h → ∞ convergence**. -/
theorem magnetizationAlongExhaustion_latticeGraph_convergent_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : Fin d → ℤ) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => Ambient.magnetizationAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) :=
  Ambient.magnetizationAlongExhaustion_convergent_h
    (IsingModel.latticeGraph d) Λ J hJ β hβ i n

/-- **ℤ^d along-ex: magnetization J → ∞ convergence**. -/
theorem magnetizationAlongExhaustion_latticeGraph_convergent_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : Fin d → ℤ) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => Ambient.magnetizationAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) :=
  Ambient.magnetizationAlongExhaustion_convergent_J
    (IsingModel.latticeGraph d) Λ h hh β hβ i n

end Ambient
end IsingModel
