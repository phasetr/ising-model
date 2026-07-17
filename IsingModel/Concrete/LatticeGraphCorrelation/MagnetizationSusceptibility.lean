import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

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

/-! ## Moved: susceptibility / truncated2 J=0 / h=0 trivial-slice wrappers

The three wrappers
`susceptibility_J_zero_latticeGraph`,
`truncated2_h_zero_latticeGraph`,
`susceptibility_h_zero_latticeGraph` now live in
`MagnetizationSusceptibilityTrivialSlices.lean`. -/


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
