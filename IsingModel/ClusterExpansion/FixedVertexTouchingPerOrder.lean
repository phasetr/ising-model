import IsingModel.ClusterExpansion.FixedVertexChainMid
import IsingModel.ClusterExpansion.FixedVertexTouchingUnion

/-!
# Fixed-vertex touching per-order bound

This file proves the coordinate-reindexing step for fixed-vertex touching cluster sequences and
combines it with the fixed-root Kotecky--Preiss bound.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Coordinate reindexing of the polymer-sequence incompatibility graph.**  Precomposing a
polymer sequence with a permutation of `Fin n` gives a graph isomorphic to the original
incompatibility graph, with the same permutation as the vertex bijection. -/
def polymerSeqIncompatibilityGraph_comp_equiv_iso {n : ℕ}
    (ω : Fin n → Finset (Sym2 ι)) (e : Fin n ≃ Fin n) :
    polymerSeqIncompatibilityGraph (fun i => ω (e i)) ≃g polymerSeqIncompatibilityGraph ω :=
  ⟨e, by
    intro i j
    rw [polymerSeqIncompatibilityGraph_adj, polymerSeqIncompatibilityGraph_adj]
    simp
  ⟩

/-- **Ursell coefficients are invariant under coordinate permutations.**  This follows by
rewriting the coefficient as the alternating connected-spanning subgraph sum divided by `n!` and
using graph-isomorphism invariance of that alternating sum. -/
theorem ursellCoefficient_comp_equiv {n : ℕ}
    (ω : Fin n → Finset (Sym2 ι)) (e : Fin n ≃ Fin n) :
    ursellCoefficient (fun i => ω (e i)) = ursellCoefficient ω := by
  rw [ursellCoefficient_eq_alternatingConnectedSubgraphSum_div,
    ursellCoefficient_eq_alternatingConnectedSubgraphSum_div]
  rw [alternatingConnectedSubgraphSum_iso (polymerSeqIncompatibilityGraph_comp_equiv_iso ω e)]

/-- **Cluster-sequence activity is invariant under coordinate permutations.**  The activity is a
finite product over the sequence coordinates, so precomposition by an equivalence only reorders the
factors. -/
theorem clusterSeqActivity_comp_equiv {n : ℕ} (t : ℝ)
    (ω : Fin n → Finset (Sym2 ι)) (e : Fin n ≃ Fin n) :
    clusterSeqActivity t (fun i => ω (e i)) = clusterSeqActivity t ω := by
  unfold clusterSeqActivity
  exact Equiv.prod_comp e (fun i => t ^ (ω i).card)

open Classical in
/-- **A fixed coordinate touching `v` has the same term-absolute sum as the root coordinate.**
The proof reindexes the constant `piFinset` by the transposition swapping `0` and `i`; the Ursell
coefficient and activity are invariant under this coordinate permutation. -/
theorem fixedVertexCoordRoot_termAbsSum_succ_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet] (v : ι) (n : ℕ) (t : ℝ) (i : Fin (n + 1)) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      = ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => v ∈ polymerSupport (ω 0)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
  classical
  let S := Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)
  let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap 0 i
  let a : (Fin (n + 1) → Finset (Sym2 ι)) → ℝ :=
    fun ω => |ursellCoefficient ω| * clusterSeqActivity t ω
  have hterm : ∀ ω : Fin (n + 1) → Finset (Sym2 ι),
      a (fun j => ω (e j)) = a ω := by
    intro ω
    dsimp [a]
    rw [ursellCoefficient_comp_equiv, clusterSeqActivity_comp_equiv]
  have hpred : ∀ ω : Fin (n + 1) → Finset (Sym2 ι),
      (v ∈ polymerSupport ((fun j => ω (e j)) i)) ↔ v ∈ polymerSupport (ω 0) := by
    intro ω
    dsimp [e]
    simp
  have hreindex := sum_piFinset_const_domEquiv e (allPolymers G)
    (fun ω : Fin (n + 1) → Finset (Sym2 ι) =>
      if v ∈ polymerSupport (ω i) then a ω else 0)
  calc
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
        = ∑ ω ∈ S, if v ∈ polymerSupport (ω i) then a ω else 0 := by
          dsimp [S, a]
          rw [Finset.sum_filter]
    _ = ∑ ω ∈ S, if v ∈ polymerSupport ((fun j => ω (e j)) i) then
          a (fun j => ω (e j)) else 0 := by
          dsimp [S] at hreindex
          exact hreindex
    _ = ∑ ω ∈ S, if v ∈ polymerSupport (ω 0) then a ω else 0 := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          by_cases h : v ∈ polymerSupport (ω 0)
          · rw [if_pos h, if_pos ((hpred ω).mpr h), hterm]
          · rw [if_neg h, if_neg (fun h' => h ((hpred ω).mp h'))]
    _ = ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => v ∈ polymerSupport (ω 0)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
          dsimp [S, a]
          rw [Finset.sum_filter]

open Classical in
/-- **Fixed-vertex touching per-order bound.**  The touching sum is bounded by the coordinate
union bound, each coordinate-rooted sum is reindexed to the root coordinate, and the fixed-root
Kotecky--Preiss estimate supplies the common geometric bound. -/
theorem fixedVertexTouching_termAbsSum_succ_le_nat_mul_geometric
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t)
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ ((n + 1 : ℕ) : ℝ)
        * ((1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)))
          * (4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
              / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2) ^ n) := by
  classical
  let B : ℝ := (1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)))
    * (4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2) ^ n
  have htouch :
      (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
            (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
          |ursellCoefficient ω| * clusterSeqActivity t ω)
        ≤ ∑ i : Fin (n + 1),
          ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
              (fun ω => v ∈ polymerSupport (ω i)),
            |ursellCoefficient ω| * clusterSeqActivity t ω := by
    have h := fixedVertexTouching_termAbsSum_succ_le_sum_coord_rooted G v n (t : ℂ)
    simpa [Complex.norm_real, Real.norm_eq_abs, clusterSeqActivity, abs_of_nonneg ht] using h
  have hcoord :
      (∑ i : Fin (n + 1),
          ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
              (fun ω => v ∈ polymerSupport (ω i)),
            |ursellCoefficient ω| * clusterSeqActivity t ω)
        ≤ ∑ _i : Fin (n + 1), B := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [fixedVertexCoordRoot_termAbsSum_succ_eq G v n t i]
    exact fixedVertexRoot_termAbsSum_succ_le_div_mul_geometric G v n ht hkp
  calc
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
        ≤ ∑ i : Fin (n + 1),
          ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
              (fun ω => v ∈ polymerSupport (ω i)),
            |ursellCoefficient ω| * clusterSeqActivity t ω := htouch
    _ ≤ ∑ _i : Fin (n + 1), B := hcoord
    _ = ((n + 1 : ℕ) : ℝ) * B := by simp [B]

end IsingModel
