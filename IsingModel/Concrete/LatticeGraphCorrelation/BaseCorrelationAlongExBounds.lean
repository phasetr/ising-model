import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d per-stage bounds on the correlation along an exhaustion

Concrete `IsingModel.latticeGraph d` statements at an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ`, for a fixed site set and a fixed stage.

The correlation at a stage is at most `1`, and it is at most the infinite-volume
correlation taken along the same exhaustion; neither of those assumes anything about the
parameter record, the second because the infinite-volume value is by definition the
supremum over stages.

Comparing across two exhaustions does assume `Ferromagnetic`: under it, the correlation at
a stage of one exhaustion is at most the infinite-volume correlation formed from the other.
`Ferromagnetic` is also what makes the correlation at a stage non-negative, through the
first Griffiths-Kelly-Sherman inequality at that stage's volume. No instance argument is
taken anywhere in this module.
-/

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
(unconditional): stage-wise upper bound by the supremum over stages. -/
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
