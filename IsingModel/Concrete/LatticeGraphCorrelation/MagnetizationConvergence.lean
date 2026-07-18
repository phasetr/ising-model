import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.Magnetization

/-!
# Concrete magnetization convergence wrappers

Narrow child module for concrete finite-stage magnetization convergence
wrappers on the lattice graph. The theorem names are the same as the former
former declarations, but callers can now avoid importing the monolithic
concrete original module.
-/

namespace IsingModel
namespace Ambient

/-! ### magnetization parameter-direction convergent (β/h/J → ∞)
ℤ^d wraps. Λ-direct versions already exist as
`magnetizationΛ_latticeGraph_convergent_{beta,h,J}` (in
`correlationΛ` form) earlier in the original module; this section adds the
along-exhaustion versions only. -/

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
