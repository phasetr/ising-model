import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Locus

/-!
# ℤ^d ComplexRealCompat at real parameters: im-zero / re-equalities

Narrow child module for five ℤ^d `*_at_real_latticeGraph` wrappers
extracted from `ComplexRealCompatAtReal.lean`:

* `partitionFunctionComplex_re_pos_at_real_latticeGraph`,
* `partitionFunctionComplex_im_zero_at_real_latticeGraph`,
* `log_partitionFunctionComplex_im_zero_at_real_latticeGraph`,
* `freeEnergyComplex_im_zero_at_real_latticeGraph`,
* `freeEnergyComplex_re_eq_freeEnergy_at_real_latticeGraph`.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
