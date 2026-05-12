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
# ℤ^d truncated4Infinite trivial-slice wrappers

Narrow child module for six ℤ^d `truncated4Infinite_latticeGraph_*`
trivial-slice wrappers (β = 0 and J = 0 under various coincidence
patterns). Each wrapper is a thin pass-through to the corresponding
ambient `truncated4Infinite_*` lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d truncated4Infinite β=0 site-wise**: `= 0`. -/
theorem truncated4Infinite_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i j k l = 0 :=
  truncated4Infinite_beta_zero (IsingModel.latticeGraph d) Λ J h i j k l

/-- **ℤ^d truncated4Infinite J=0 pairwise distinct site-wise**: `= -2·tanh(β·h)^4`. -/
theorem truncated4Infinite_latticeGraph_J_zero_of_pairwise_distinct
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i j k l : Fin d → ℤ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i j k l
      = -2 * Real.tanh (β * h) ^ 4 :=
  truncated4Infinite_J_zero_of_pairwise_distinct (IsingModel.latticeGraph d) Λ
    h β hf hij hik hil hjk hjl hkl

/-- **ℤ^d truncated4Infinite J=0 one-pair coincidence** (#745). -/
theorem truncated4Infinite_latticeGraph_J_zero_of_one_pair_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k l : Fin d → ℤ}
    (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i k l
      = -2 * Real.tanh (β * h) ^ 4 :=
  truncated4Infinite_J_zero_of_one_pair_coincidence
    (IsingModel.latticeGraph d) Λ h β hf hik hil hkl

/-- **ℤ^d truncated4Infinite J=0 two-pair coincidence** (#746). -/
theorem truncated4Infinite_latticeGraph_J_zero_of_two_pair_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k : Fin d → ℤ} (hik : i ≠ k) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i k k
      = -2 * Real.tanh (β * h) ^ 4 :=
  truncated4Infinite_J_zero_of_two_pair_coincidence
    (IsingModel.latticeGraph d) Λ h β hf hik

/-- **ℤ^d truncated4Infinite J=0 triple coincidence** (#747):
`t² − 3·t³`. -/
theorem truncated4Infinite_latticeGraph_J_zero_of_triple_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i l : Fin d → ℤ} (hil : i ≠ l) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i i l
      = Real.tanh (β * h) ^ 2 - 3 * Real.tanh (β * h) ^ 3 :=
  truncated4Infinite_J_zero_of_triple_coincidence
    (IsingModel.latticeGraph d) Λ h β hf hil

/-- **ℤ^d truncated4Infinite J=0 all-coincident** (#748): `t − 3·t²`. -/
theorem truncated4Infinite_latticeGraph_J_zero_all_coincident
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i i i
      = Real.tanh (β * h) - 3 * Real.tanh (β * h) ^ 2 :=
  truncated4Infinite_J_zero_all_coincident
    (IsingModel.latticeGraph d) Λ h β hf i

end Ambient
end IsingModel
