/- BaseSpontaneousCorrelationMonotone.lean
Narrow child module for 3 ℤ^d `spontaneousCorrelation_latticeGraph_*`
monotonicity + singleton-set wrappers extracted from
`BaseSpontaneousCorrelation.lean`. Each is a thin pass-through to the
abstract `spontaneousCorrelation_*` lemma at `latticeGraph d`. The
theorem names are unchanged.
-/
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d J-direction monotonicity of `spontaneousCorrelation`**
(ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun J : ℝ => spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A)
      (Set.Ici 0) :=
  spontaneousCorrelation_monotone_J (IsingModel.latticeGraph d) Λ hβ A

/-- **ℤ^d β-direction monotonicity of `spontaneousCorrelation`**
(ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun β : ℝ => spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A)
      (Set.Ioi 0) :=
  spontaneousCorrelation_monotone_beta (IsingModel.latticeGraph d) Λ hJ A

/-- **ℤ^d `spontaneousCorrelation ... {i} = spontaneousMagnetization ... i`**
(any-Exhaustion): singleton-set spontaneous correlation equals
spontaneous magnetization. -/
theorem spontaneousCorrelation_latticeGraph_singleton_eq_spontaneousMagnetization
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (i : Fin d → ℤ) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β {i}
      = spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i :=
  spontaneousCorrelation_singleton_eq_spontaneousMagnetization
    (IsingModel.latticeGraph d) Λ J β i

end Ambient

end IsingModel
