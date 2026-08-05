/- BaseCorrelationAlongExBounds.lean
Narrow child module for the 4 ℤ^d per-stage `correlationAlongExhaustion_latticeGraph_*`
bound wrappers extracted from `Base.lean` in PR #2038. Theorems:
`correlationAlongExhaustion_latticeGraph_le_one`,
`_le_correlationInfinite_of_other`,
`_le_correlationInfinite`,
`_nonneg`. Each is a thin pass-through to the corresponding
abstract `correlationAlongExhaustion_*` lemma at `latticeGraph d`.
The theorem names are unchanged from the former `Base`
declarations.
-/
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `correlationAlongExhaustion` is ≤ 1** per stage (unconditional).
Concrete specialization of `correlationAlongExhaustion_le_one`. -/
theorem correlationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n ≤ 1 :=
  correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d cross-exhaustion sandwich** (ferromagnetic): for any two ℤ^d
exhaustions `Λ, Λ'`, per stage `correlationAlongExhaustion Λ'` is ≤
the `correlationInfinite` computed via `Λ`. -/
theorem correlationAlongExhaustion_latticeGraph_le_correlationInfinite_of_other
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ' p A n
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  correlationAlongExhaustion_le_correlationInfinite_of_other
    (IsingModel.latticeGraph d) Λ Λ' p hf A n

/-- **ℤ^d `correlationAlongExhaustion ≤ correlationInfinite`** per stage
(ferromagnetic): stage-wise upper bound by the limsup value. -/
theorem correlationAlongExhaustion_latticeGraph_le_correlationInfinite
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  correlationAlongExhaustion_le_correlationInfinite
    (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `correlationAlongExhaustion` is ≥ 0** per stage (ferromagnetic).
Concrete specialization of `correlationAlongExhaustion_nonneg`. -/
theorem correlationAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  correlationAlongExhaustion_nonneg (IsingModel.latticeGraph d) Λ p hf A n

end Ambient

end IsingModel
