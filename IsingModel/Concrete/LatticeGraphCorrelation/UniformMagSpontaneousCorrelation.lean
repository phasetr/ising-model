import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `spontaneousCorrelation` on degenerate slices

Evaluates the ℤ^d spontaneous correlation — the infimum of `correlationInfinite` over
the positive external fields — where its value is forced: it vanishes on every nonempty
finite set of sites at zero coupling under `0 < β`, and again at zero inverse
temperature with no condition on the coupling, while on the empty site set it is `1` for
every coupling and inverse temperature.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d spontaneousCorrelation at J = 0 general nonempty A** (Step 272). -/
theorem spontaneousCorrelation_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ 0 β A = 0 :=
  spontaneousCorrelation_J_zero (IsingModel.latticeGraph d) Λ hβ A hA

/-- **ℤ^d spontaneousCorrelation at β = 0 general nonempty A** (Step 272). -/
theorem spontaneousCorrelation_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J : ℝ)
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J 0 A = 0 :=
  spontaneousCorrelation_beta_zero (IsingModel.latticeGraph d) Λ J A hA

/-- **ℤ^d spontaneousCorrelation at empty A is 1** (Step 274). -/
theorem spontaneousCorrelation_latticeGraph_empty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β
        (∅ : Finset (Fin d → ℤ)) = 1 :=
  spontaneousCorrelation_empty (IsingModel.latticeGraph d) Λ J β

end Ambient
end IsingModel
