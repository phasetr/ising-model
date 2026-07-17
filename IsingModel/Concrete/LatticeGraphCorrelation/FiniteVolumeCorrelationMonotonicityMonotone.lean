import IsingModel.InfiniteVolume
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d finite-volume correlation_monotone_{J,h,β} wrappers

Narrow child module for three ℤ^d
`correlation_monotone_{J,h,beta}_latticeGraph` wrappers extracted
from `FiniteVolumeCorrelationMonotonicity.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlation_monotone_J direct** (Λ-induced, ferromagnetic). -/
theorem correlation_monotone_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (B : Finset (↑Λ : Type _)) :
    MonotoneOn (IsingModel.correlationJ
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B) (Set.Ici 0) :=
  IsingModel.correlation_monotone_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ B

/-- **ℤ^d correlation_monotone_h direct** (Λ-induced, ferromagnetic). -/
theorem correlation_monotone_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (B : Finset (↑Λ : Type _)) :
    MonotoneOn (IsingModel.correlationH
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β B) (Set.Ici 0) :=
  IsingModel.correlation_monotone_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ B

/-- **ℤ^d correlation_monotone_beta direct** (Λ-induced, ferromagnetic). -/
theorem correlation_monotone_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun β : ℝ => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, h, β⟩ A)
      (Set.Ioi 0) :=
  IsingModel.correlation_monotone_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh A

end Ambient
end IsingModel
