import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d spontaneous magnetization and correlation on degenerate parameter slices

Records the vanishing of the ℤ^d order parameter `spontaneousMagnetization` at zero coupling
under `0 < β`, and at zero inverse temperature with no condition on the coupling, together
with the vanishing of `correlationInfinite` on every nonempty finite set of sites when the
coupling and the field are both zero and `0 < β`.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d spontaneousMagnetization at J = 0 vanishes** (Step 269). -/
theorem spontaneousMagnetization_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β : ℝ} (hβ : 0 < β)
    (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ 0 β i = 0 :=
  spontaneousMagnetization_J_zero (IsingModel.latticeGraph d) Λ hβ i

/-- **ℤ^d spontaneousMagnetization at β = 0 vanishes** (Step 269). -/
theorem spontaneousMagnetization_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J : ℝ) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J 0 i = 0 :=
  spontaneousMagnetization_beta_zero (IsingModel.latticeGraph d) Λ J i

/-- **ℤ^d correlationInfinite at J = h = 0 vanishes for nonempty A** (Step 280). -/
theorem correlationInfinite_latticeGraph_zero_params_vanish_of_nonempty_A
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β : ℝ} (hβ : 0 < β)
    {A : Finset (Fin d → ℤ)} (hA : A.Nonempty) :
    correlationInfinite (IsingModel.latticeGraph d) Λ ⟨0, 0, β⟩ A = 0 :=
  correlationInfinite_zero_params_vanish_of_nonempty_A
    (IsingModel.latticeGraph d) Λ hβ hA

end Ambient
end IsingModel
