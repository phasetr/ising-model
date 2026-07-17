import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergyAlongExhaustion tendsto disjoint_tower / super wrappers

Narrow child module for three ℤ^d
`freeEnergyAlongExhaustion_latticeGraph_tendsto_*` wrappers extracted
from `TwoPointFreeEnergyAlongExTendsto.lean`:

* `freeEnergyAlongExhaustion_latticeGraph_tendsto_of_disjoint_tower`,
* `freeEnergyAlongExhaustion_latticeGraph_tendsto_of_disjointTowerHypotheses`,
* `freeEnergyAlongExhaustion_latticeGraph_tendsto_of_superadditive`.

Each result is a thin pass-through of the ambient
`Ambient.freeEnergyAlongExhaustion_tendsto_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `TwoPointFreeEnergyAlongExTendsto` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Fekete-style convergence under disjoint-tower + BED** (any-Exhaustion):
if `|Λ.volume (m+n)| = |Λ.volume m| + |Λ.volume n|`, log Z is super-additive,
and BED holds, then `freeEnergyAlongExhaustion → freeEnergyInfinite`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_tendsto_of_disjoint_tower
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hsuper : ∀ m n,
        Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
            (Λ.volume m) p)
          + Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
              (Λ.volume n) p)
        ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
            (Λ.volume (m + n)) p))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
      Filter.atTop
      (nhds (freeEnergyInfinite (IsingModel.latticeGraph d) Λ p)) :=
  freeEnergyAlongExhaustion_tendsto_of_disjoint_tower
    (IsingModel.latticeGraph d) Λ p hBED hcard_add hsuper hcard_one

/-- **ℤ^d Fekete-style convergence under disjoint-tower + BED, bundled form**
(any-Exhaustion): same as `_of_disjoint_tower` but takes a
`DisjointTowerHypotheses` record. -/
theorem freeEnergyAlongExhaustion_latticeGraph_tendsto_of_disjointTowerHypotheses
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (h : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
      Filter.atTop
      (nhds (freeEnergyInfinite (IsingModel.latticeGraph d) Λ p)) :=
  freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses
    (IsingModel.latticeGraph d) Λ p hBED h

/-- **ℤ^d Fekete-style convergence under super-additivity**
(any-Exhaustion): if `|Λ.volume (m+n)| = |Λ.volume m| + |Λ.volume n|`,
log Z is super-additive on this additive grading, the range is bounded above,
and `|Λ.volume 1| ≠ 0`, then `freeEnergyAlongExhaustion → freeEnergyInfinite`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_tendsto_of_superadditive
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hsuper : ∀ m n,
        Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
            (Λ.volume m) p)
          + Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
              (Λ.volume n) p)
        ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
            (Λ.volume (m + n)) p))
    (hbdd : BddAbove (Set.range
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
      Filter.atTop
      (nhds (freeEnergyInfinite (IsingModel.latticeGraph d) Λ p)) :=
  freeEnergyAlongExhaustion_tendsto_of_superadditive
    (IsingModel.latticeGraph d) Λ p hcard_add hsuper hbdd hcard_one

end Ambient

end IsingModel
