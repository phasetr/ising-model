import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance

/-!
# ℤ^d twoPointFunction basic bound wrappers

Narrow child module for three ℤ^d basic `twoPointFunction` bound
wrappers extracted from `SiteIndepMagTwoPoint.lean`:

* `twoPointFunction_nonneg`,
* `twoPointFunction_le_one`,
* `neg_one_le_twoPointFunction`.
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
