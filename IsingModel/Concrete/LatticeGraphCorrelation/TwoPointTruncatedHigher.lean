import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint

/-!
# ℤ^d truncated3/4Infinite_latticeGraph trivial-slice wrappers

Narrow child module for 18 ℤ^d `truncated3Infinite_latticeGraph_*`
and `truncated4Infinite_latticeGraph_*` trivial-slice + nonpos +
exhaustion-independence wrappers (β = 0, J = 0 with various
coincidence patterns, h = 0, nonpos, `_indep_exhaustion`).
Theorem names are unchanged from the former `TwoPoint`
declarations.
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

/-- **ℤ^d truncated3Infinite J=0 pairwise distinct site-wise**: `= 0`. -/
theorem truncated3Infinite_latticeGraph_J_zero_of_pairwise_distinct
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i j k : Fin d → ℤ} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i j k = 0 :=
  truncated3Infinite_J_zero_of_pairwise_distinct (IsingModel.latticeGraph d) Λ
    h β hf hij hjk hik

/-- **ℤ^d truncated3Infinite J=0 pair coincidence vanishes**
(`i = j ≠ k`): concrete wrapper for
`truncated3Infinite_J_zero_of_pair_coincidence` (#742). -/
theorem truncated3Infinite_latticeGraph_J_zero_of_pair_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k : Fin d → ℤ} (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i k = 0 :=
  truncated3Infinite_J_zero_of_pair_coincidence (IsingModel.latticeGraph d) Λ
    h β hf hik

/-- **ℤ^d truncated3Infinite J=0 all-coincident closed form**:
`truncated3Infinite ⟨0,h,β⟩ i i i = t·(1-t)·(1-2t)` with `t = tanh(β·h)`.
Concrete wrapper for `truncated3Infinite_J_zero_all_coincident` (#743). -/
theorem truncated3Infinite_latticeGraph_J_zero_all_coincident
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h))
          * (1 - 2 * Real.tanh (β * h)) :=
  truncated3Infinite_J_zero_all_coincident (IsingModel.latticeGraph d) Λ h β hf i

/-! ## Moved: truncated4Infinite trivial-slice wrappers

The six `truncated4Infinite_latticeGraph_*` trivial-slice wrappers
(β = 0 and J = 0 under various coincidence patterns) now live in
`TwoPointTruncatedHigherTruncated4.lean`. -/

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

/-- **ℤ^d truncated3Infinite nonpos** (GHS) site-wise (any Exhaustion). -/
theorem truncated3Infinite_latticeGraph_nonpos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {i j k : Fin d → ℤ} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k ≤ 0 :=
  truncated3Infinite_nonpos (IsingModel.latticeGraph d) Λ p hf hij hjk hik

/-- **ℤ^d truncated4Infinite nonpos at h=0** (Lebowitz) site-wise. -/
theorem truncated4Infinite_latticeGraph_nonpos_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : Fin d → ℤ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ i j k l ≤ 0 :=
  truncated4Infinite_nonpos_h_zero (IsingModel.latticeGraph d) Λ J β hf
    hij hik hil hjk hjl hkl

/-- **ℤ^d truncated3Infinite at h=0 vanishes** site-wise, pairwise distinct. -/
theorem truncated3Infinite_latticeGraph_h_zero_of_distinct
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    {i j k : Fin d → ℤ}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ i j k = 0 :=
  truncated3Infinite_h_zero_of_distinct (IsingModel.latticeGraph d) Λ J β
    hij hjk hik

/-! ## Moved: truncated{2,3,4}Infinite exhaustion-independence wrappers

The three wrappers
`truncated{2,3,4}Infinite_latticeGraph_indep_exhaustion`
now live in `TwoPointTruncatedHigherIndepExhaustion.lean`. -/



end Ambient

end IsingModel
