import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d site-level magnetization sign/bound wrappers

Narrow child module for five ℤ^d `magnetization_*_latticeGraph`
sign/bound wrappers extracted from `MagnetizationSiteLevel.lean`:

* `abs_magnetization_le_one_latticeGraph`,
* `magnetization_le_one_latticeGraph`,
* `neg_one_le_magnetization_latticeGraph`,
* `magnetization_nonneg_latticeGraph` (ferromagnetic),
* `magnetization_sq_le_one_latticeGraph`.

Each result is a thin pass-through of the abstract
`IsingModel.magnetization_*` lemma at
`Ambient.inducedGraph (IsingModel.latticeGraph d) Λ`. The theorem
names are unchanged from the former `MagnetizationSiteLevel`
declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

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

end Ambient

end IsingModel
