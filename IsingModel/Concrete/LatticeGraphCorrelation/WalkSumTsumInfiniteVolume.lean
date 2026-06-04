import IsingModel.Concrete.LatticeGraphCorrelation.WalkSumTsumLatticeGraph
import IsingModel.Concrete.CubicBoxConnectivity
import IsingModel.AmbientLattice.Exhaustion
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Infinite-volume random-walk (walk-sum) upper representation on ℤ^d (FFS Ch 12 / GJ §18)

The finite-volume random-walk upper representation
`correlation_inducedLatticeGraph_le_tsum_walkSum` bounds the two-point function at
each exhaustion stage by the walk sum confined to that stage's box:

  `⟨σ_i σ_j⟩_{Λ_n} ≤ ∑_{k ≥ 1} walkSum (β J) i j k`   (walks inside `Λ_n`).

Passing to the thermodynamic limit `correlationInfinite = ⨆_n correlationAlongExhaustion`
gives the **infinite-volume walk-sum representation**

  `⟨σ_i σ_j⟩_∞ ≤ ⨆_n  walkTsumAlongCubic (β J) i j n`,

where `walkTsumAlongCubic (β J) i j n` is the box-confined positive-length walk sum
at exhaustion stage `n` (or `0` before the pair is contained).  The supremum on the
right is finite: every stage walk sum is dominated by the geometric series
`∑_{k ≥ 1} (β J · 2d)^k` (each induced-box vertex has degree `≤ 2d`), so the family is
bounded above and `le_ciSup` / `ciSup_le` apply.

This complements the infinite-volume *decay* bound
`correlationInfinite_latticeGraph_le_pow_latticeDistance` (which gives a sharp
distance-decaying estimate): here the random-walk *structure* itself survives the
thermodynamic limit, exhibiting `⟨σ_i σ_j⟩_∞` as a supremum of box-confined walk
sums.  It is a contribution to the project's central long-term goal, the
infinite-volume limit.

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Ch 12.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **Box-confined positive-length walk sum at an exhaustion stage** (FFS Ch 12):
`walkTsumAlongCubic d z i j n` is the sum `∑_{k ≥ 1} walkSum z i j k` over walks
confined to the cubic-exhaustion box `(cubicExhaustion d).volume n`, provided that
box already contains the pair `{i, j}`; otherwise it is `0`.  The lifted endpoints
use the membership proofs extracted from the containment hypothesis (irrelevant by
proof irrelevance). -/
noncomputable def walkTsumAlongCubic (d : ℕ) (z : ℝ) (i j : Fin d → ℤ) (n : ℕ) : ℝ :=
  if h : ({i, j} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n then
    ∑' k : ℕ, walkSum (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n)) z
      ⟨i, (Finset.insert_subset_iff.mp h).1⟩
      ⟨j, Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h).2⟩ (k + 1)
  else 0

/-- **Uniform geometric domination of the box-confined walk sums**: for the
ferromagnetic high-temperature regime `β J · 2d < 1`, every stage walk sum
`walkTsumAlongCubic (β J) i j n` is bounded above by the geometric series
`∑_{k ≥ 1} (β J · 2d)^k`, uniformly in `n`.  Termwise domination is the walk count
bound `walkSum ≤ (β J · 2d)^k` (`walkSum_le_pow_degree_bound`, degree `≤ 2d`); both
series are summable, so `tsum_le_tsum` applies.  Stages not containing the pair are
`0 ≤` the (nonnegative) geometric sum. -/
theorem walkTsumAlongCubic_le_tsum_geom (d : ℕ) {β J : ℝ}
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hlt : β * J * (2 * (d : ℝ)) < 1) (i j : Fin d → ℤ) (n : ℕ) :
    walkTsumAlongCubic d (β * J) i j n
      ≤ ∑' k : ℕ, (β * J * (2 * (d : ℝ))) ^ (k + 1) := by
  have hβJ : (0 : ℝ) ≤ β * J := mul_nonneg hf.hβ.le hf.hJ
  have hzD : (0 : ℝ) ≤ β * J * (2 * (d : ℝ)) := mul_nonneg hβJ (by positivity)
  have hgeo : Summable (fun k : ℕ => (β * J * (2 * (d : ℝ))) ^ (k + 1)) := by
    simpa only [pow_succ'] using
      (summable_geometric_of_lt_one hzD hlt).mul_left (β * J * (2 * (d : ℝ)))
  unfold walkTsumAlongCubic
  split
  · rename_i h
    set Λ := (cubicExhaustion d).volume n
    have hD : ∀ v : ↑Λ,
        ((inducedGraph (IsingModel.latticeGraph d) Λ).neighborFinset v).card ≤ 2 * d :=
      fun v => inducedLatticeGraph_degree_le d Λ v
    have hlt' : β * J * ((2 * d : ℕ) : ℝ) < 1 := by
      rwa [show ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) from by push_cast; ring]
    have hsum : Summable (fun k : ℕ =>
        walkSum (inducedGraph (IsingModel.latticeGraph d) Λ) (β * J)
          ⟨i, (Finset.insert_subset_iff.mp h).1⟩
          ⟨j, Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h).2⟩ (k + 1)) :=
      summable_walkSum_of_lt_one (inducedGraph (IsingModel.latticeGraph d) Λ) hβJ hD hlt' _ _
    refine hsum.tsum_le_tsum (fun k => ?_) hgeo
    have := walkSum_le_pow_degree_bound (inducedGraph (IsingModel.latticeGraph d) Λ) hβJ hD
      ⟨i, (Finset.insert_subset_iff.mp h).1⟩
      ⟨j, Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h).2⟩ (k + 1)
    rwa [show ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) from by push_cast; ring] at this
  · exact tsum_nonneg fun k => pow_nonneg hzD (k + 1)

/-- **Infinite-volume random-walk (walk-sum) upper representation on ℤ^d**
(FFS Ch 12 / GJ §18): in the ferromagnetic high-temperature regime `β J · 2d < 1`,
for distinct sites `i ≠ j`,

`correlationInfinite (latticeGraph d) (cubicExhaustion d) ⟨J,0,β⟩ {i, j}
   ≤ ⨆ n, walkTsumAlongCubic (β J) i j n`,

the thermodynamic-limit form of the discrete random-walk bound: the two-point
function in the infinite volume is dominated by the supremum of the box-confined
walk sums.  Each exhaustion stage `correlationAlongExhaustion n` is bounded by its
own walk sum (`correlation_inducedLatticeGraph_le_tsum_walkSum` when the box
contains the pair, `0` otherwise), and that family is bounded above (uniform
geometric domination, `walkTsumAlongCubic_le_tsum_geom`), so the supremum
`correlationInfinite = ⨆_n correlationAlongExhaustion` is bounded by `⨆_n` of the
walk sums via `le_ciSup` and `ciSup_le`. -/
theorem correlationInfinite_latticeGraph_le_iSup_tsum_walkSum (d : ℕ)
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hlt : β * J * (2 * (d : ℝ)) < 1) {i j : Fin d → ℤ} (hij : i ≠ j) :
    correlationInfinite (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ ⨆ n, walkTsumAlongCubic d (β * J) i j n := by
  have hbdd : BddAbove (Set.range (fun n => walkTsumAlongCubic d (β * J) i j n)) :=
    ⟨∑' k : ℕ, (β * J * (2 * (d : ℝ))) ^ (k + 1), by
      rintro _ ⟨n, rfl⟩; exact walkTsumAlongCubic_le_tsum_geom d hf hlt i j n⟩
  rw [correlationInfinite_eq_ciSup]
  apply ciSup_le
  intro n
  refine le_trans ?_ (le_ciSup hbdd n)
  by_cases hsub : ({i, j} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n
  · have hi : i ∈ (cubicExhaustion d).volume n :=
      (Finset.insert_subset_iff.mp hsub).1
    have hj : j ∈ (cubicExhaustion d).volume n :=
      Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp hsub).2
    have hne : (⟨i, hi⟩ : ↑((cubicExhaustion d).volume n)) ≠ ⟨j, hj⟩ :=
      fun h => hij (congrArg Subtype.val h)
    rw [correlationAlongExhaustion, dif_pos hsub, correlationΛ, liftFinset_pair hsub hi hj,
      walkTsumAlongCubic, dif_pos hsub]
    exact correlation_inducedLatticeGraph_le_tsum_walkSum d ((cubicExhaustion d).volume n)
      hf hlt hne
  · rw [correlationAlongExhaustion, dif_neg hsub, walkTsumAlongCubic, dif_neg hsub]

end Ambient

end IsingModel
