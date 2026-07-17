import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d truncated3/4Infinite_latticeGraph nonpos + h_zero_of_distinct wrappers

Narrow child module for three ℤ^d wrappers extracted from
`TwoPointTruncatedHigher.lean`:

* `truncated3Infinite_latticeGraph_nonpos` (GHS),
* `truncated4Infinite_latticeGraph_nonpos_h_zero` (Lebowitz),
* `truncated3Infinite_latticeGraph_h_zero_of_distinct`.

Each result is a thin pass-through of the ambient
`Ambient.truncated{3,4}Infinite_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `TwoPointTruncatedHigher` declarations.
-/

namespace IsingModel
namespace Ambient

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

end Ambient

end IsingModel
