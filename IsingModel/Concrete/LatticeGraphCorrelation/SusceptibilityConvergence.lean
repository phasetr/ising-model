import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityConvergence

/-!
# Concrete susceptibility convergence wrappers

Narrow child module for concrete finite-stage susceptibility convergence
wrappers on the lattice graph. The theorem names are the same as the former
former declarations, but callers can now avoid importing the monolithic
concrete original module.
-/

namespace IsingModel
namespace Ambient

/-! ### susceptibility parameter-direction convergent (β/h/J → ∞)
ℤ^d wraps. Λ-direct versions remain in the original module because they sit with
the nearby Λ-level susceptibility regularity wrappers; this module contains the
along-exhaustion versions only. -/

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
