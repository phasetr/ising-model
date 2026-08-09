import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag

/-!
# Range of the ℤ^d uniform magnetization

Concrete statements about `uniformMagnetization` at `IsingModel.latticeGraph d` along
`Ambient.cubicExhaustion d`. With no assumption on the parameter record the value is
bounded below by `-1` and above by `1`, and the corresponding bounds on its absolute value
and on its square are recorded too. Non-negativity is the one statement here that assumes
`Ferromagnetic`. No instance argument is taken.
-/

namespace IsingModel
namespace Ambient

/-- **Nonnegativity of `uniformMagnetization`** (ferromagnetic).
Specialization of the abstract `magnetizationInfinite_nonneg`. -/
theorem uniformMagnetization_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ uniformMagnetization d p :=
  magnetizationInfinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf 0

/-- **Upper bound on `uniformMagnetization`**:
`uniformMagnetization d p ≤ 1`. -/
theorem uniformMagnetization_le_one
    (d : ℕ) (p : IsingParams ℝ) :
    uniformMagnetization d p ≤ 1 :=
  magnetizationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **`-1 ≤ uniformMagnetization`** unconditionally. Specialization of
`neg_one_le_magnetizationInfinite` at site `0`. -/
theorem neg_one_le_uniformMagnetization
    (d : ℕ) (p : IsingParams ℝ) :
    -1 ≤ uniformMagnetization d p :=
  neg_one_le_magnetizationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **`|uniformMagnetization| ≤ 1`** unconditionally. Specialization of
`abs_magnetizationInfinite_le_one` at site `0`. -/
theorem abs_uniformMagnetization_le_one
    (d : ℕ) (p : IsingParams ℝ) :
    |uniformMagnetization d p| ≤ 1 :=
  abs_magnetizationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **`uniformMagnetization² ≤ 1`** unconditionally. Specialization of
`magnetizationInfinite_sq_le_one` at site `0`. -/
theorem uniformMagnetization_sq_le_one
    (d : ℕ) (p : IsingParams ℝ) :
    uniformMagnetization d p ^ 2 ≤ 1 :=
  magnetizationInfinite_sq_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

end Ambient
end IsingModel
