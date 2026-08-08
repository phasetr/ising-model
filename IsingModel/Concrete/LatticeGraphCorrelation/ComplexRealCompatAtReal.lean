import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Locus

/-!
# Concrete real-axis evaluation of complex partition function / free energy

Instantiates the real-axis evaluation identities of the complexified partition function and
free energy at `IsingModel.latticeGraph d`. These are the pointwise real-axis values the
Vitali–Porter convergence argument compares against the real model.
-/

namespace IsingModel
namespace Ambient

/-! #### Real-axis evaluation of the complex partition function / free energy

Direct ℤ^d forwarders for the real-axis evaluation identities of the
complex partition function and free energy. These restate the
real-complex bridge in the form most useful for Vitali convergence
(pointwise values on the real axis via Fekete). -/

/-- **ℤ^d `partitionFunctionComplex` at real `h₀`** (Λ-induced):
`Z_ℂ(J, ↑h₀, β) = ↑(Z G ⟨J, h₀, β⟩)`. -/
theorem partitionFunctionComplex_at_real_pos_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β h₀ : ℝ) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) (h₀ : ℂ) (β : ℂ)
      = ((IsingModel.partitionFunction
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            ⟨J, h₀, β⟩ : ℝ) : ℂ) :=
  IsingModel.partitionFunctionComplex_at_real_pos
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `freeEnergyComplex` at real parameters** (Λ-induced):
`f_ℂ(J, h, β) = ↑(f G ⟨J, h, β⟩)`. -/
theorem freeEnergyComplex_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) (h : ℂ) (β : ℂ)
      = ((IsingModel.freeEnergy
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            ⟨J, h, β⟩ : ℝ) : ℂ) :=
  IsingModel.freeEnergyComplex_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β

/-- **ℤ^d `freeEnergyComplex ↔ freeEnergy` Vitali form** (Λ-induced):
`f_ℂ G ↑p.J ↑p.h ↑p.β = ↑(f G p)`. Thin restatement of
`freeEnergy_ofReal_eq_freeEnergyComplex` in the orientation most useful
for Vitali convergence (RHS is the cast of the real-parameter value). -/
theorem freeEnergyComplex_ofReal_eq_freeEnergy_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)
      = ((IsingModel.freeEnergy
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℝ) : ℂ) :=
  IsingModel.freeEnergyComplex_ofReal_eq_freeEnergy
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `‖Z_ℂ‖ = Z` at real parameters** (Λ-induced). -/
theorem norm_partitionFunctionComplex_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)‖
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.norm_partitionFunctionComplex_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `Z_ℂ` is a positive real at real parameters** (Λ-induced):
explicit witness for `Z_ℂ = ↑x` with `0 < x`. -/
theorem partitionFunctionComplex_is_pos_real_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ∃ x : ℝ, 0 < x ∧ IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) = (x : ℂ) :=
  IsingModel.partitionFunctionComplex_is_pos_real_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

end Ambient

end IsingModel
