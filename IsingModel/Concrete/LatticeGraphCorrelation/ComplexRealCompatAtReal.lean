import IsingModel.Concrete.LatticeGraphBED
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity

/-!
# Concrete real-axis evaluation of complex partition function / free energy

Narrow child module for ten ℤ^d `*_at_real_latticeGraph` real-axis
evaluation wrappers of the complex partition function and free energy.
Each wrapper is a thin pass-through to the corresponding ambient
`IsingModel.*_at_real` lemma at the induced graph.
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

/-- **ℤ^d `Re Z_ℂ > 0` at real parameters** (Λ-induced):
immediate from positivity of the real `Z`. -/
theorem partitionFunctionComplex_re_pos_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    0 < (IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)).re :=
  IsingModel.partitionFunctionComplex_re_pos_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `Im Z_ℂ = 0` at real parameters** (Λ-induced). -/
theorem partitionFunctionComplex_im_zero_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)).im = 0 :=
  IsingModel.partitionFunctionComplex_im_zero_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `Im (log Z_ℂ) = 0` at real parameters** (Λ-induced). -/
theorem log_partitionFunctionComplex_im_zero_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (Complex.log (IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))).im = 0 :=
  IsingModel.log_partitionFunctionComplex_im_zero_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `Im f_ℂ = 0` at real parameters** (Λ-induced). -/
theorem freeEnergyComplex_im_zero_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)).im = 0 :=
  IsingModel.freeEnergyComplex_im_zero_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `Re f_ℂ = f` at real parameters** (Λ-induced). -/
theorem freeEnergyComplex_re_eq_freeEnergy_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)).re
      = IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.freeEnergyComplex_re_eq_freeEnergy_at_real
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
