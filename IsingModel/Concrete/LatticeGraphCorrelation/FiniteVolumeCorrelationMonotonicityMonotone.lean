import IsingModel.InfiniteVolume
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Parameter monotonicity of finite-volume correlations in ℤ^d

Records that on the subgraph induced by the nearest-neighbor lattice graph on a finite
`Λ ⊆ ℤ^d` the correlation of a fixed spin product is monotone increasing in each parameter
separately: in the coupling and in the external field on `[0, ∞)`, and in the inverse
temperature on `(0, ∞)`. Each statement assumes nonnegativity of the two parameters held
fixed, strengthened to strict positivity when the inverse temperature is one of them.

Reference: Glimm–Jaffe §4.2 Proposition 4.2.1, p. 58, for the coupling direction.
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
