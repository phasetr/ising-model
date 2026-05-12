/- MagnetizationSiteLevel.lean
Narrow child module for the 11 ℤ^d site-level magnetization wrappers
extracted from `Magnetization.lean` in PR #2031. Theorems:
`magnetization_apply_latticeGraph`,
`{abs,_le_one,neg_one_le,nonneg,sq_le_one}_latticeGraph`,
`{zero_at_h_zero,beta_zero,J_zero}_latticeGraph`,
`{monotone_h,monotone_beta}_latticeGraph`. Each is a thin
pass-through of the abstract `IsingModel.magnetization_*` at
`Ambient.inducedGraph (latticeGraph d) Λ`. The theorem names are
unchanged from the former `Magnetization` declarations.
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

/-- **ℤ^d magnetization_zero_at_h_zero direct** (Λ-induced):
`M_i(J, 0, β) = 0` — Z₂ symmetry at `h = 0`. -/
theorem magnetization_zero_at_h_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, 0, β⟩ i = 0 :=
  IsingModel.magnetization_zero_at_h_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β i

/-- **ℤ^d magnetization_beta_zero direct** (Λ-induced):
`M_i(J, h, 0) = 0` — infinite-temperature slice. -/
theorem magnetization_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, h, 0⟩ i = 0 :=
  IsingModel.magnetization_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h i

/-- **ℤ^d magnetization_J_zero direct** (Λ-induced):
`M_i(0, h, β) = tanh(β·h)` — non-interacting slice. -/
theorem magnetization_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) :=
  IsingModel.magnetization_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β i

/-- **ℤ^d magnetization_monotone_h direct** (Λ-induced, ferromagnetic):
`h ↦ M_i(J, h, β)` is `MonotoneOn (Set.Ici 0)` for `J ≥ 0`, `β > 0`. -/
theorem magnetization_monotone_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (i : (↑Λ : Type _)) :
    MonotoneOn
      (fun h : ℝ => IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  IsingModel.magnetization_monotone_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ i

/-- **ℤ^d magnetization_monotone_beta direct** (Λ-induced, ferromagnetic):
`β ↦ M_i(J, h, β)` is `MonotoneOn (Set.Ioi 0)` for `J, h ≥ 0`. -/
theorem magnetization_monotone_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (i : (↑Λ : Type _)) :
    MonotoneOn
      (fun β : ℝ => IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, h, β⟩ i)
      (Set.Ioi 0) :=
  IsingModel.magnetization_monotone_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh i

end Ambient

end IsingModel
