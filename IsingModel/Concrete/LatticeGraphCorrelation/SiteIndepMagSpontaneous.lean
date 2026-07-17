import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `spontaneousCorrelation`/`spontaneousMagnetization_latticeGraph` wrappers

Narrow child module for the 8 ℤ^d
`spontaneousCorrelation_latticeGraph_apply` and
`spontaneousMagnetization_latticeGraph_*` wrappers
(`_apply`, `neg_one_le_*`, `abs_*_le_one`, `_nonneg`, `_le_one`,
`_monotone_J`, `_monotone_beta`) extracted from `SiteIndepMag.lean`
in PR #2048. Each is a thin pass-through to the corresponding ambient
`spontaneousCorrelation_*` / `spontaneousMagnetization_*` lemma at
`latticeGraph d`. The theorem names are unchanged from the former
`SiteIndepMag` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `spontaneousCorrelation` apply** (any-Exhaustion):
`spontaneousCorrelation = ⨅ h ∈ Ioi 0, correlationInfinite ⟨J, h, β⟩ A`. -/
theorem spontaneousCorrelation_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A
      = ⨅ h : ↥(Set.Ioi (0 : ℝ)),
          correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h.val, β⟩ A :=
  spontaneousCorrelation_apply (IsingModel.latticeGraph d) Λ J β A

/-- **ℤ^d `spontaneousMagnetization` apply** (any-Exhaustion):
singleton specialization of `spontaneousCorrelation_apply`. -/
theorem spontaneousMagnetization_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i
      = ⨅ h : ↥(Set.Ioi (0 : ℝ)),
          magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h.val, β⟩ i :=
  spontaneousCorrelation_apply (IsingModel.latticeGraph d) Λ J β {i}

/-! ## Moved: sign/bound wrappers

The four wrappers
`neg_one_le_spontaneousMagnetization_latticeGraph`,
`abs_spontaneousMagnetization_latticeGraph_le_one`,
`spontaneousMagnetization_latticeGraph_nonneg`,
`spontaneousMagnetization_latticeGraph_le_one` now live in
`SiteIndepMagSpontaneousBounds.lean`. -/


/-- **ℤ^d J-direction monotonicity of `spontaneousMagnetization`**
(ferromagnetic). -/
theorem spontaneousMagnetization_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    MonotoneOn
      (fun J : ℝ => spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i)
      (Set.Ici 0) :=
  spontaneousMagnetization_monotone_J (IsingModel.latticeGraph d) Λ hβ i

/-- **ℤ^d β-direction monotonicity of `spontaneousMagnetization`**
(ferromagnetic). -/
theorem spontaneousMagnetization_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) (i : Fin d → ℤ) :
    MonotoneOn
      (fun β : ℝ => spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i)
      (Set.Ioi 0) :=
  spontaneousMagnetization_monotone_beta (IsingModel.latticeGraph d) Λ hJ i

end Ambient

end IsingModel
