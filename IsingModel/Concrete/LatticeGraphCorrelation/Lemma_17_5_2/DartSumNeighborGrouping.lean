import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import IsingModel.Concrete.LatticeGraphBED.HandshakeIdentity

/-!
# Dart-sum-by-neighbor grouping (GJ §17.5 Theorem 17.5.1 — PR-1i convolution infrastructure)

A general fiber-decomposition identity: the sum over the darts of a finite simple graph of a
function of the dart's two endpoints equals the double sum over vertices `v` and their neighbours
`w`: `∑_{d:Dart} F(d.fst, d.snd) = ∑_v ∑_{w ∈ neighborFinset v} F(v, w)`.

This is the dart analog of `Finset.sum_fiberwise` grouped by `Dart.fst` (via `dart_fst_fiber` and
the `dartOfNeighborSet` bijection), needed to convert the GJ p.312 cross-sum's dart sum into the
neighbour-shifted double sum that the m⁻-scaled HLS convolution (#4336) consumes.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace SimpleGraph

open Finset

variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]

/-- **Dart-sum-by-neighbor grouping.**  For a finite simple graph `G` and `F : V → V → ℝ`,
`∑_{d:Dart} F(d.fst, d.snd) = ∑_v ∑_{w ∈ neighborFinset v} F(v, w)`.  Groups the dart sum by
`d.fst` (`Finset.sum_fiberwise_of_maps_to`), identifies each fibre with the neighbour set
(`dart_fst_fiber`, `dartOfNeighborSet` injective), and converts the subtype sum to a
`neighborFinset` sum (`Finset.sum_subtype`). -/
theorem sum_dart_eq_sum_neighborFinset (F : V → V → ℝ) :
    ∑ d : G.Dart, F d.fst d.snd = ∑ v, ∑ w ∈ G.neighborFinset v, F v w := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun d _ => Finset.mem_univ d.fst)
    (fun d : G.Dart => F d.fst d.snd)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [G.dart_fst_fiber v, Finset.sum_image
    (fun a _ b _ h => G.dartOfNeighborSet_injective v h),
    Finset.sum_subtype (G.neighborFinset v) (fun x => G.mem_neighborFinset v x) (fun w => F v w)]
  rfl

end SimpleGraph
