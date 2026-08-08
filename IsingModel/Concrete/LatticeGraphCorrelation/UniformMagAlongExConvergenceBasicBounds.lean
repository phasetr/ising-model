import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d per-stage bounds on `magnetizationAlongExhaustion`

Bounds the ℤ^d single-site magnetization at each stage of an exhaustion: it
never exceeds `1`, it is nonnegative for `Ferromagnetic` parameters, and it
never exceeds the infinite-volume magnetization, which is by definition the `⨆`
over stages of that same sequence.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetizationAlongExhaustion ≤ 1** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n ≤ 1 :=
  magnetizationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d magnetizationAlongExhaustion ≥ 0** per stage (ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) (n : ℕ) :
    0 ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  magnetizationAlongExhaustion_nonneg (IsingModel.latticeGraph d) Λ p hf i n

/-- **ℤ^d `magnetizationAlongExhaustion ≤ magnetizationInfinite`** per stage:
stage-wise upper bound by the `⨆` over stages. -/
theorem magnetizationAlongExhaustion_latticeGraph_le_magnetizationInfinite
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationAlongExhaustion_le_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ p i n

end Ambient
end IsingModel
