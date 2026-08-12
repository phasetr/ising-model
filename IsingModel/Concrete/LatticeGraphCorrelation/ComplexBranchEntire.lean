import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.RealAxis

/-!
# ℤ^d analytic branch of the complex free energy over the Lee-Yang domain (§4.6)

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the Lee-Yang branch statement: at every point of `leeYangDomain`
there is a function analytic at that point whose exponential, scaled by the cardinality of
`Λ`, is the complex partition function; in a plain form, and in a strengthened form that also
pins the branch value at the base point to the principal-branch `freeEnergyComplex`. Every
branch statement here assumes `Λ` nonempty, `0 < β` and `0 < J`. The module also records that
`freeEnergyComplex` is `AnalyticOnNhd` on `leeYangSubdomain`, and that statement assumes
`0 < β` alone: no nonemptiness of `Λ`, and no sign condition on the coupling.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `freeEnergyComplex` has analytic branch over leeYangDomain**
(Λ-induced, nonempty `Λ`, ferromagnetic): headline form. -/
theorem freeEnergyComplex_exists_analyticBranch_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ h ∈ IsingModel.leeYangDomain, ∃ f : ℂ → ℂ, AnalyticAt ℂ f h ∧
        Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h (β : ℂ) :=
  IsingModel.freeEnergyComplex_exists_analyticBranch
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d `freeEnergyComplex` analyticBranch (strong form)**
(Λ-induced, nonempty `Λ`, ferromagnetic): additionally identifies the
branch value at the basepoint with the principal-branch
`freeEnergyComplex`. -/
theorem freeEnergyComplex_exists_analyticBranch_strong_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ h ∈ IsingModel.leeYangDomain, ∃ f : ℂ → ℂ,
        AnalyticAt ℂ f h
      ∧ Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h (β : ℂ)
      ∧ f h = IsingModel.freeEnergyComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h (β : ℂ) :=
  IsingModel.freeEnergyComplex_exists_analyticBranch_strong
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d packaged `AnalyticOnNhd` on Lee-Yang subdomain** (Λ-induced,
ferromagnetic `β > 0`). -/
theorem freeEnergyComplex_analyticOnNhd_of_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    AnalyticOnNhd ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_analyticOnNhd_of_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

end Ambient

end IsingModel
