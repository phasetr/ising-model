import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Bounds

/-!
# Concrete Complex norm-bound wrappers

Narrow child module for four ℤ^d
`norm_{partitionFunction,freeEnergy}Complex_*_latticeGraph` norm-bound
wrappers. Each wrapper is a thin pass-through to the corresponding
ambient lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `‖Z_ℂ‖ ≤ Z_ℝ(J, Re h, β)`** (Λ-induced): dominate the complex
partition function by its real counterpart at `Re h`. -/
theorem norm_partitionFunctionComplex_le_partitionFunction_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) (h : ℂ) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)‖
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          ⟨J, h.re, β⟩ :=
  IsingModel.norm_partitionFunctionComplex_le_partitionFunction
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h

/-- **ℤ^d trivial upper bound on `‖Z_ℂ‖`** (Λ-induced):
`‖Z_ℂ‖ ≤ 2^|Λ| · exp(|β|·(|J|·|E|_Λ + |Re h|·|Λ|))`. Locally uniform
on compact sets in `h`; input for Montel in the Vitali lift. -/
theorem norm_partitionFunctionComplex_le_trivial_bound_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) (h : ℂ) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)‖
      ≤ Fintype.card (IsingModel.Config (↑Λ : Type _)) *
          Real.exp (|β| *
            (|J| *
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              + |h.re| * Fintype.card (↑Λ : Type _))) :=
  IsingModel.norm_partitionFunctionComplex_le_trivial_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h

/-- **ℤ^d `‖Z_ℂ‖` upper bound under `|Re h| ≤ R`** (Λ-induced):
uniform over the strip `|Re h| ≤ R`. -/
theorem norm_partitionFunctionComplex_le_of_re_bound_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) {R : ℝ} {h : ℂ}
    (hh : |h.re| ≤ R) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)‖
      ≤ Fintype.card (IsingModel.Config (↑Λ : Type _)) *
          Real.exp (|β| *
            (|J| *
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              + R * Fintype.card (↑Λ : Type _))) :=
  IsingModel.norm_partitionFunctionComplex_le_of_re_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J hh

/-- **ℤ^d trivial upper bound on `‖f_ℂ‖`** (Λ-induced, nonempty `Λ`):
`‖f_ℂ‖ ≤ |log ‖Z_ℂ‖|/|Λ| + π/|Λ|`. Combined with `BoundedEdgeDensity`
this gives the Vitali uniform-on-compacts bound. -/
theorem norm_freeEnergyComplex_le_trivial_bound_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)] (β J : ℝ) (h : ℂ) :
    ‖IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)‖
      ≤ |Real.log ‖IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h (β : ℂ)‖|
          / (Fintype.card (↑Λ : Type _) : ℝ)
        + Real.pi / (Fintype.card (↑Λ : Type _) : ℝ) :=
  IsingModel.norm_freeEnergyComplex_le_trivial_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h

end Ambient
end IsingModel
