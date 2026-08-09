import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Bounds

/-!
# ℤ^d norm bounds for the complex partition function and free energy

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` upper bounds on the modulus of the complex partition function and
of the complex free-energy density. The partition function is dominated by its real
counterpart evaluated at the real part of the field, and by an explicit exponential
expression in the number of configurations, the number of edges and the number of sites of
the induced subgraph; each of those holds for arbitrary real `β` and `J` and arbitrary
complex field, with no hypothesis. One further partition-function bound replaces the real
part of the field by an upper bound for it, and assumes exactly that inequality. The
free-energy bound is stated through the logarithm of the modulus of the partition function,
and assumes that `Λ` is nonempty.
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
