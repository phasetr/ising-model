import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `truncated3Infinite` trivial-slice wrappers

Evaluates the third truncated infinite-volume correlation on the degenerate `β = 0` slice and
on the zero-field slice at `IsingModel.latticeGraph d`, including the coincident-site cases
where the truncation degenerates.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d truncated3Infinite β=0 site-wise**: `= 0`. -/
theorem truncated3Infinite_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i j k = 0 :=
  truncated3Infinite_beta_zero (IsingModel.latticeGraph d) Λ J h i j k

/-- **ℤ^d truncated3Infinite h=0 pair coincidence** (#750):
`truncated3Infinite ⟨J,0,β⟩ i i k = correlationInfinite ⟨J,0,β⟩ {i,k}`
for `i ≠ k` (any Exhaustion). -/
theorem truncated3Infinite_latticeGraph_h_zero_of_pair_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    {i k : Fin d → ℤ} (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i i k
      = correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, k} :=
  truncated3Infinite_h_zero_of_pair_coincidence
    (IsingModel.latticeGraph d) Λ J β hik

/-- **ℤ^d truncated3Infinite h=0 all-coincident vanishes** (#750). -/
theorem truncated3Infinite_latticeGraph_h_zero_all_coincident
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i i i = 0 :=
  truncated3Infinite_h_zero_all_coincident
    (IsingModel.latticeGraph d) Λ J β i

end Ambient

end IsingModel
