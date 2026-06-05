import Mathlib.Combinatorics.SimpleGraph.Walks.Counting
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Degree bound on the number of walks of a given length

The number of walks of length `k` starting from a vertex is at most `Δ^k`, where `Δ` is a
uniform degree bound. This is the counting input to the FV §3.7.3 bound
`#{connected edge-sets of size ℓ containing the origin} ≤ (2d)^{2ℓ}` (via the Eulerian
closed-walk injection), towards the high-temperature `m*(β)=0` (Issue #3613).

* `walksFromCount` — the number of walks of length `k` starting at `u`.
* `walksFromCount_le_pow` — the degree bound `walksFromCount u k ≤ Δ^k`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, eq. (3.49) (the `(2d)^{2ℓ}` walk count), p. 118.
-/

namespace IsingModel

open Finset SimpleGraph

variable {V : Type*}

/-- **The number of walks of length `k` starting at `u`**: summed over all endpoints. -/
noncomputable def walksFromCount (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (u : V) (k : ℕ) : ℕ :=
  ∑ v : V, (G.finsetWalkLength k u v).card

/-- **Degree bound on the walk count**: if every vertex has degree at most `Δ`, then the
number of length-`k` walks starting at any vertex is at most `Δ^k`. Proved by induction on
`k`: each length-`(k+1)` walk is a first edge to a neighbour followed by a length-`k` walk,
so the count multiplies by at most the degree. -/
theorem walksFromCount_le_pow (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {Δ : ℕ} (hΔ : ∀ w, G.degree w ≤ Δ) (k : ℕ) (u : V) :
    walksFromCount G u k ≤ Δ ^ k := by
  induction k generalizing u with
  | zero =>
    unfold walksFromCount
    rw [pow_zero, Finset.sum_eq_single u]
    · simp [SimpleGraph.finsetWalkLength]
    · intro v _ hvu
      simp [SimpleGraph.finsetWalkLength, Ne.symm hvu]
    · intro h; exact absurd (Finset.mem_univ u) h
  | succ k ih =>
    have hstep : ∀ v : V, (G.finsetWalkLength (k + 1) u v).card
        ≤ ∑ w : G.neighborSet u, (G.finsetWalkLength k w.val v).card := by
      intro v
      simp only [SimpleGraph.finsetWalkLength]
      refine (Finset.card_biUnion_le).trans ?_
      exact Finset.sum_le_sum (fun w _ => by rw [Finset.card_map])
    calc walksFromCount G u (k + 1)
        = ∑ v : V, (G.finsetWalkLength (k + 1) u v).card := rfl
      _ ≤ ∑ v : V, ∑ w : G.neighborSet u, (G.finsetWalkLength k w.val v).card :=
          Finset.sum_le_sum (fun v _ => hstep v)
      _ = ∑ w : G.neighborSet u, ∑ v : V, (G.finsetWalkLength k w.val v).card :=
          Finset.sum_comm
      _ = ∑ w : G.neighborSet u, walksFromCount G w.val k := rfl
      _ ≤ ∑ _w : G.neighborSet u, Δ ^ k := Finset.sum_le_sum (fun w _ => ih w.val)
      _ = Fintype.card (G.neighborSet u) • Δ ^ k := by
          rw [Finset.sum_const, Finset.card_univ]
      _ = G.degree u * Δ ^ k := by rw [card_neighborSet_eq_degree, smul_eq_mul]
      _ ≤ Δ * Δ ^ k := Nat.mul_le_mul_right _ (hΔ u)
      _ = Δ ^ (k + 1) := by rw [pow_succ, mul_comm]

/-- **Walk count bound on the induced lattice box graph**: in the induced cubic-lattice
graph on a finite box `Λ`, the number of length-`k` walks from any site is at most
`(2d)^k` (every vertex has degree at most `2d`). The `(2d)^{2ℓ}` factor of FV (3.49). -/
theorem walksFromCount_inducedLatticeGraph_le {d : ℕ} (Λ : Finset (Fin d → ℤ))
    (u : ↑Λ) (k : ℕ) :
    walksFromCount (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) u k ≤ (2 * d) ^ k :=
  walksFromCount_le_pow _ (fun w => Ambient.inducedLatticeGraph_degree_le d Λ w) k u

end IsingModel
