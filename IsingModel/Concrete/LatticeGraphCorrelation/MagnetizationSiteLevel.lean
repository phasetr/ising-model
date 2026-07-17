/- MagnetizationSiteLevel.lean
Narrow child module for ℤ^d site-level magnetization wrappers extracted
from `Magnetization.lean` in PR #2031. Theorems:
`magnetization_apply_latticeGraph`,
`{abs_magnetization_le_one,magnetization_le_one,neg_one_le_magnetization,
magnetization_nonneg,magnetization_sq_le_one}_latticeGraph`. Each is a
thin pass-through of the abstract `IsingModel.magnetization_*` at
`Ambient.inducedGraph (latticeGraph d) Λ`. The trivial-slice /
monotone wrappers
(`{zero_at_h_zero,beta_zero,J_zero,monotone_h,monotone_beta}_latticeGraph`)
now live in `MagnetizationSiteLevelTrivialAndMonotone.lean`. The
theorem names are unchanged from the former `Magnetization` declarations.
-/
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### Site-level magnetization wrappers (GJ §5.3, pp. 77–80)

Direct ℤ^d forwarders for `magnetization G p i = correlation G p {i}`
in `PhaseTransition.lean`. All pass through the abstract
`IsingModel.magnetization_*` theorems on
`Ambient.inducedGraph (latticeGraph d) Λ`. -/

/-- **ℤ^d magnetization_apply direct** (Λ-induced):
`magnetization = correlation … {i}`. -/
theorem magnetization_apply_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p {i} :=
  IsingModel.magnetization_apply
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i

/-! ## Moved: sign/bound wrappers

The five wrappers
`abs_magnetization_le_one_latticeGraph`,
`magnetization_le_one_latticeGraph`,
`neg_one_le_magnetization_latticeGraph`,
`magnetization_nonneg_latticeGraph`,
`magnetization_sq_le_one_latticeGraph` now live in
`MagnetizationSiteLevelBounds.lean`. -/


/-! ## Moved: magnetization trivial-slice / monotone wrappers

The five `magnetization_*_latticeGraph` wrappers
(`zero_at_h_zero`, `beta_zero`, `J_zero`, `monotone_h`, `monotone_beta`)
now live in `MagnetizationSiteLevelTrivialAndMonotone.lean`. -/



end Ambient

end IsingModel
