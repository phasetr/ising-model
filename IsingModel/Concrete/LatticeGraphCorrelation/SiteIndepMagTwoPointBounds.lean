import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance

/-!
# Range of the ℤ^d two-point function

Concrete statements about `twoPointFunction` at `IsingModel.latticeGraph d` along
`Ambient.cubicExhaustion d`, at an arbitrary separation. The value is at most `1` and at
least `-1` with no assumption on the parameter record. Under `Ferromagnetic` the lower
bound sharpens to `0`, by the first Griffiths-Kelly-Sherman inequality applied to the
anchoring site set. No instance argument is taken.
-/

namespace IsingModel
namespace Ambient

/-- **Nonnegativity of `twoPointFunction`** (GKS-I).
`0 ≤ twoPointFunction d p r`. -/
theorem twoPointFunction_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    0 ≤ twoPointFunction d p r :=
  correlationInfinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf {(0 : Fin d → ℤ), r}

/-- **Upper bound on `twoPointFunction`** (boundedness of correlation).
`twoPointFunction d p r ≤ 1`. -/
theorem twoPointFunction_le_one
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    twoPointFunction d p r ≤ 1 :=
  correlationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **`-1 ≤ twoPointFunction`** unconditionally. Direct specialization
of `neg_one_le_correlationInfinite` at `A = {0, r}`. -/
theorem neg_one_le_twoPointFunction
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    -1 ≤ twoPointFunction d p r :=
  neg_one_le_correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

end Ambient
end IsingModel
