import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DartSumNeighborGrouping
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMassDist

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1i: dart-profile sum ≤ box-vertex sum (p.312)

Applies the dart-sum-by-neighbor grouping (#4348 `sum_dart_eq_sum_neighborFinset`) to the PR-1i
dart-profile sum (#4347) and bounds each induced-graph neighbour sum by the **lattice** neighbour
sum (the induced-box neighbours of a vertex inject, via `.val`, into the full lattice neighbours):
`∑_{dt} s(x,dt.fst)·s(z,dt.snd) ≤ ∑_{v:↑box} s(x,v.val)·∑_{u∼v.val (lattice)} s(z,u)`,
where `s(a,b) = 1/(1+(m⁻·d(a,b))^α)`.  The box-vertex sum is then bounded by the infinite-lattice
convolution (#4336) in the final step.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- **Dart-profile sum ≤ box-vertex sum** (GJ p.312): the PR-1i dart-profile sum over the induced
cubic graph is bounded by the box-vertex sum whose inner neighbour sum ranges over the *lattice*
neighbours.  Grouping by `dt.fst` (#4348); factor out `s(x,v.val)` (`Finset.mul_sum`); the
induced-box neighbour sum is bounded by the lattice neighbour sum because the box neighbours inject
(via `.val`) into the lattice neighbours (`Finset.sum_image` +
`Finset.sum_le_sum_of_subset_of_nonneg`). -/
theorem dart_profile_sum_le_box_vertex_sum {α d : ℕ} {m : ℝ} (hm_nn : 0 ≤ m)
    {n : ℕ} (x z : Fin d → ℤ) :
    ∑ dt : (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).Dart,
        (1 / (1 + (m * (latticeDistance d x dt.fst.val : ℝ)) ^ α))
          * (1 / (1 + (m * (latticeDistance d z dt.snd.val : ℝ)) ^ α))
      ≤ ∑ v : (↑((cubicExhaustion d).volume n) : Type _),
          (1 / (1 + (m * (latticeDistance d x v.val : ℝ)) ^ α))
            * ∑ u ∈ (latticeGraph d).neighborFinset v.val,
                (1 / (1 + (m * (latticeDistance d z u : ℝ)) ^ α)) := by
  classical
  -- denominators are positive (m ≥ 0, distances ≥ 0).
  have hden : ∀ y w : Fin d → ℤ, (0 : ℝ) < 1 + (m * (latticeDistance d y w : ℝ)) ^ α := by
    intro y w
    have : (0 : ℝ) ≤ (m * (latticeDistance d y w : ℝ)) ^ α :=
      pow_nonneg (mul_nonneg hm_nn (by positivity)) α
    linarith
  rw [SimpleGraph.sum_dart_eq_sum_neighborFinset
    (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
    (fun a b => (1 / (1 + (m * (latticeDistance d x a.val : ℝ)) ^ α))
      * (1 / (1 + (m * (latticeDistance d z b.val : ℝ)) ^ α)))]
  refine Finset.sum_le_sum (fun v _ => ?_)
  rw [Finset.mul_sum]
  have hconv : ∑ w ∈ (inducedGraph (latticeGraph d)
          ((cubicExhaustion d).volume n)).neighborFinset v,
        (1 / (1 + (m * (latticeDistance d x v.val : ℝ)) ^ α))
          * (1 / (1 + (m * (latticeDistance d z w.val : ℝ)) ^ α))
      = ∑ u ∈ ((inducedGraph (latticeGraph d)
            ((cubicExhaustion d).volume n)).neighborFinset v).image Subtype.val,
        (1 / (1 + (m * (latticeDistance d x v.val : ℝ)) ^ α))
          * (1 / (1 + (m * (latticeDistance d z u : ℝ)) ^ α)) := by
    rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  rw [hconv]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun u _ _ => mul_nonneg (le_of_lt (one_div_pos.mpr (hden x v.val)))
      (le_of_lt (one_div_pos.mpr (hden z u))))
  intro u hu
  rw [Finset.mem_image] at hu
  obtain ⟨w, hw, rfl⟩ := hu
  rw [SimpleGraph.mem_neighborFinset]
  have hadj_ind : (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).Adj v w :=
    (SimpleGraph.mem_neighborFinset _ _ _).mp hw
  have hadj : (latticeGraph d).Adj v.val w.val := hadj_ind
  exact hadj

end Ambient
end IsingModel
