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
import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG

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

/-- **ℤ^d abs_magnetization_le_one direct** (Λ-induced):
`|M_i| ≤ 1` unconditionally. -/
theorem abs_magnetization_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (i : (↑Λ : Type _)) :
    |IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i| ≤ 1 :=
  IsingModel.abs_magnetization_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i

/-- **ℤ^d magnetization_le_one direct** (Λ-induced):
`M_i ≤ 1` unconditionally. -/
theorem magnetization_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i ≤ 1 :=
  IsingModel.magnetization_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i

/-- **ℤ^d neg_one_le_magnetization direct** (Λ-induced):
`-1 ≤ M_i` unconditionally. -/
theorem neg_one_le_magnetization_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (i : (↑Λ : Type _)) :
    -1 ≤ IsingModel.magnetization
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i :=
  IsingModel.neg_one_le_magnetization
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i

/-- **ℤ^d magnetization_nonneg direct** (Λ-induced, ferromagnetic):
`0 ≤ M_i` via GKS-I. -/
theorem magnetization_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (i : (↑Λ : Type _)) :
    0 ≤ IsingModel.magnetization
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i :=
  IsingModel.magnetization_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf i

/-- **ℤ^d magnetization_sq_le_one direct** (Λ-induced):
`M_i² ≤ 1` unconditionally. -/
theorem magnetization_sq_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i ^ 2 ≤ 1 :=
  IsingModel.magnetization_sq_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i

/-! ## Moved: magnetization trivial-slice / monotone wrappers

The five `magnetization_*_latticeGraph` wrappers
(`zero_at_h_zero`, `beta_zero`, `J_zero`, `monotone_h`, `monotone_beta`)
now live in `MagnetizationSiteLevelTrivialAndMonotone.lean`. -/



end Ambient

end IsingModel
