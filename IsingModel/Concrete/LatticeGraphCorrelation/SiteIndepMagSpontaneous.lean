import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `spontaneousCorrelation` / `spontaneousMagnetization` wrappers

Instantiates the defining evaluations of the spontaneous correlation and spontaneous
magnetization at `IsingModel.latticeGraph d`, together with their monotonicity in `J` and in
`β` — the ℤ^d entry point for the spontaneous-magnetization arguments.
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
