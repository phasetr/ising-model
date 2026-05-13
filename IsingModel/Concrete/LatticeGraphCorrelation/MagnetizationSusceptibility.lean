import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.Concrete.LatticeGraphCorrelation.Magnetization

/-!
# ℤ^d susceptibility + η wrappers on `latticeGraph d`

Narrow child module for 11 ℤ^d wrappers covering the
`susceptibility_*_latticeGraph` family (apply, nonneg, trivial slices
at `J = 0` / `β = 0`, h-symmetry, and `{J,h,β} → ∞` subsequence
convergence), the supporting `truncated2_h_zero_latticeGraph`, and
the finite-volume `eta_nonneg_finite_vol_latticeGraph` (GJ §17.7,
Thm 17.7.1 finite-volume slice). All are thin pass-throughs of the
corresponding abstract wrappers on
`Ambient.inducedGraph (latticeGraph d) Λ`. Theorem names are
unchanged from the former `Magnetization` declarations.
-/

namespace IsingModel
namespace Ambient

/-! ### Susceptibility (GJ §5.3) and eta critical-exponent wrappers

Direct ℤ^d forwarders for the `susceptibility` family (apply, nonneg,
trivial slices at `J=0` / `β=0`, and `{J,h,β} → ∞` subsequence
convergence) and the GJ §17.7 finite-volume `η ≥ 0` slice
`eta_nonneg_finite_vol`. -/

/-- **ℤ^d susceptibility_apply direct** (Λ-induced):
`susceptibility ι = ∑ j, truncated2 ι j`. Thin pass-through of
`IsingModel.susceptibility_apply`. -/
theorem susceptibility_apply_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (i : (↑Λ : Type _)) :
    IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i
      = ∑ j : (↑Λ : Type _), IsingModel.truncated2
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i j :=
  IsingModel.susceptibility_apply
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i

/-- **ℤ^d susceptibility_nonneg direct** (Λ-induced, ferromagnetic):
`0 ≤ χ_i`. Thin pass-through of `IsingModel.susceptibility_nonneg`
(GKS-II summed over `j`). -/
theorem susceptibility_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (i : (↑Λ : Type _)) :
    0 ≤ IsingModel.susceptibility
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i :=
  IsingModel.susceptibility_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf i

/-- **ℤ^d susceptibility_J_zero direct** (Λ-induced): at `J = 0`,
`χ_i = t · (1 - t)` with `t = tanh(β·h)`. Thin pass-through of
`IsingModel.susceptibility_J_zero`. Note: uses the Finset-based
`truncated2` so the diagonal `{i, i} = {i}` term is `t - t²`, not
the physical `1 - t²` — see the base theorem's doc comment. -/
theorem susceptibility_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h)) :=
  IsingModel.susceptibility_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β i

/-- **ℤ^d truncated2 h=0 direct** (Λ-induced): at `h = 0`,
`truncated2 i j = correlation {i, j}`. Thin pass-through of
`IsingModel.truncated2_h_zero`. -/
theorem truncated2_h_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i j : (↑Λ : Type _)) :
    IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, 0, β⟩ : IsingParams ℝ) i j
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} :=
  IsingModel.truncated2_h_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β i j

/-- **ℤ^d susceptibility_h_zero direct** (Λ-induced): at `h = 0`,
`χ_i = ∑_j correlation {i, j}`. Thin pass-through of
`IsingModel.susceptibility_h_zero`. -/
theorem susceptibility_h_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, 0, β⟩ : IsingParams ℝ) i
      = ∑ j : (↑Λ : Type _),
          IsingModel.correlation
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} :=
  IsingModel.susceptibility_h_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β i

/-- **ℤ^d susceptibility_neg_h direct** (Λ-induced):
`χ(-h) = χ(h) - 2·M(h)`. Concrete wrapper for
`IsingModel.susceptibility_neg_h` (#767). -/
theorem susceptibility_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i
      = IsingModel.susceptibility
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i
        - 2 * IsingModel.magnetization
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  IsingModel.susceptibility_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β i

/-- **ℤ^d susceptibility_beta_zero direct** (Λ-induced): at `β = 0`,
`χ_i = 0` for any `J, h`. Thin pass-through of
`IsingModel.susceptibility_beta_zero`. -/
theorem susceptibility_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ) i = 0 :=
  IsingModel.susceptibility_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h i

/-! ## Moved: susceptibility_convergent wrappers

The three `susceptibility_convergent_{J,h,beta}_latticeGraph` wrappers
now live in `MagnetizationSusceptibilityConvergent.lean`. -/



/-- **ℤ^d eta_nonneg_finite_vol direct** (Λ-induced, GJ §17.7
Thm 17.7.1 finite-volume slice, ferromagnetic):
`0 ≤ ⟨σ_i; σ_j⟩` via GKS-II. Thin pass-through of
`IsingModel.eta_nonneg_finite_vol`. -/
theorem eta_nonneg_finite_vol_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (i j : (↑Λ : Type _)) :
    0 ≤ IsingModel.truncated2
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i j :=
  IsingModel.eta_nonneg_finite_vol
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf i j


end Ambient

end IsingModel
