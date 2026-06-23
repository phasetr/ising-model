import IsingModel.ClusterExpansion.FixedVertexPeelBound
import IsingModel.ClusterExpansion.MayerCore.TermsComplexHolomorphic

/-!
# Fixed-vertex bookend clones for the rooted chain (GJ §18.6)

This file contains the two safe bookend clones for the fixed-vertex rooted chain used in the
Route B fixed-site Kotecky--Preiss bound.  The first theorem is the root-filtered clone of
`termAbsSum_succ_le_treeSum_rootedExpActivity`; the second is the fixed-vertex clone of
`sum_pow_rootedParentActivePeelBound_le`, using the #4249 peel bound without the global
`Fintype.card ι` factor.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Root-filtered shifted term-absolute tree-sum bound.** This is the direct
fixed-root-filtered clone of `termAbsSum_succ_le_treeSum_rootedExpActivity`: the outer
polymer-sequence sum is restricted to sequences whose root polymer `ω 0` contains the fixed
vertex `v`, while the per-sequence Penrose tree bound is unchanged. -/
theorem fixedVertexRoot_termAbsSum_succ_le_treeSum_rootedExpActivity
    (G : SimpleGraph ι) [Fintype G.edgeSet] (v : ι) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => v ∈ polymerSupport (ω 0)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ (((n + 1).factorial : ℝ)⁻¹)
        * ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
            (fun ω => v ∈ polymerSupport (ω 0)),
            ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
              |t| ^ (ω 0).card
                * ∏ i : Fin n,
                    Real.exp 1 ^ (ω (Fin.succ i)).card
                      * |t| ^ (ω (Fin.succ i)).card := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hact : clusterSeqActivity t ω = |clusterSeqActivity t ω| := by
    rw [abs_of_nonneg (by rw [clusterSeqActivity]; positivity)]
  rw [hact, clusterSeqActivity_abs]
  calc
    |ursellCoefficient ω| * ∏ i : Fin (n + 1), |t| ^ (ω i).card
        ≤ ((Penrose.numSpanningTrees (polymerSeqIncompatibilityGraph ω) : ℝ)
            / (n + 1).factorial) * ∏ i : Fin (n + 1), |t| ^ (ω i).card :=
          mul_le_mul_of_nonneg_right
            (ursellCoefficient_abs_le_numSpanningTrees_div_factorial ω) (by positivity)
    _ = (((n + 1).factorial : ℝ)⁻¹)
          * ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
              ∏ i : Fin (n + 1), |t| ^ (ω i).card := by
        rw [Finset.sum_const, nsmul_eq_mul, Penrose.numSpanningTrees]
        ring
    _ ≤ (((n + 1).factorial : ℝ)⁻¹)
          * ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
              |t| ^ (ω 0).card
                * ∏ i : Fin n,
                    Real.exp 1 ^ (ω (Fin.succ i)).card
                      * |t| ^ (ω (Fin.succ i)).card := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Finset.sum_le_sum fun T _ => ?_
        rw [Fin.prod_univ_succ]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
        refine le_mul_of_one_le_left (by positivity) ?_
        exact one_le_pow₀ (Real.one_le_exp_iff.mpr zero_le_one)

/-- **Fixed-vertex `(Δ²e|t|)^n`-weighted summed peel bound.** This is the fixed-root clone of
`sum_pow_rootedParentActivePeelBound_le`: the active peel bound is replaced by
`fixedVertexRootedParentActivePeelBound G root`, and #4249 gives the factorial-product bound
without the global factor `Fintype.card ι`. -/
theorem sum_pow_fixedVertexRootedParentActivePeelBound_le
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (root : ι) (n : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
        S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
        ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
          * fixedVertexRootedParentActivePeelBound G root
              (Penrose.completeGraphTreeParentCode n T) (Finset.univ : Finset (Fin n))
              (fun _ => 0) t)
      ≤ (((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n * (4 : ℝ) ^ n
            * (n.factorial : ℝ))
          / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (2 * n + 1) := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  have hrr0 : 0 ≤ rr := by rw [hrr]; positivity
  have hcast : (∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
        S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
        ∏ v : Fin (n + 1),
          ((rootedParentChildCount (Penrose.completeGraphTreeParentCode n T)
            (Finset.univ : Finset (Fin n)) v).factorial : ℝ))
      ≤ (4 : ℝ) ^ n * (n.factorial : ℝ) := by
    have h := sum_completeGraphTrees_prod_childCount_factorial_le_four_pow_mul_factorial
      (n := n)
    calc
      (∑ T, ∏ v : Fin (n + 1),
          ((rootedParentChildCount (Penrose.completeGraphTreeParentCode n T)
            (Finset.univ : Finset (Fin n)) v).factorial : ℝ))
          = ((∑ T, ∏ v : Fin (n + 1),
              (rootedParentChildCount (Penrose.completeGraphTreeParentCode n T)
                (Finset.univ : Finset (Fin n)) v).factorial : ℕ) : ℝ) := by
            push_cast
            ring
      _ ≤ ((4 ^ n * n.factorial : ℕ) : ℝ) := by exact_mod_cast h
      _ = (4 : ℝ) ^ n * (n.factorial : ℝ) := by
            push_cast
            ring
  rw [← Finset.mul_sum]
  have hpeel : (∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
        S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
        fixedVertexRootedParentActivePeelBound G root
          (Penrose.completeGraphTreeParentCode n T) (Finset.univ : Finset (Fin n))
          (fun _ => 0) t)
      ≤ ((1 : ℝ) / q ^ (2 * n + 1)) * ((4 : ℝ) ^ n * (n.factorial : ℝ)) := by
    calc
      (∑ T, fixedVertexRootedParentActivePeelBound G root
          (Penrose.completeGraphTreeParentCode n T) (Finset.univ : Finset (Fin n))
          (fun _ => 0) t)
          ≤ ∑ T, (∏ v : Fin (n + 1),
              ((rootedParentChildCount (Penrose.completeGraphTreeParentCode n T)
                (Finset.univ : Finset (Fin n)) v).factorial : ℝ))
              / q ^ (2 * n + 1) := by
            refine Finset.sum_le_sum fun T _ => ?_
            exact fixedVertexRootedParentActivePeelBound_univ_zero_le_prod_childCount_factorial_div
              G root (Penrose.completeGraphTreeParentCode n T) hqpos
      _ = ((1 : ℝ) / q ^ (2 * n + 1))
            * ∑ T, ∏ v : Fin (n + 1),
                ((rootedParentChildCount (Penrose.completeGraphTreeParentCode n T)
                  (Finset.univ : Finset (Fin n)) v).factorial : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun T _ => ?_
            rw [one_div, div_eq_inv_mul]
      _ ≤ ((1 : ℝ) / q ^ (2 * n + 1)) * ((4 : ℝ) ^ n * (n.factorial : ℝ)) := by
            refine mul_le_mul_of_nonneg_left hcast ?_
            exact div_nonneg zero_le_one (le_of_lt (pow_pos hqpos _))
  calc
    rr ^ n
        * ∑ T, fixedVertexRootedParentActivePeelBound G root
            (Penrose.completeGraphTreeParentCode n T) (Finset.univ : Finset (Fin n))
            (fun _ => 0) t
        ≤ rr ^ n * (((1 : ℝ) / q ^ (2 * n + 1))
            * ((4 : ℝ) ^ n * (n.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hpeel (pow_nonneg hrr0 n)
    _ = (rr ^ n * (4 : ℝ) ^ n * (n.factorial : ℝ)) / q ^ (2 * n + 1) := by
          rw [one_div]
          ring

end IsingModel
