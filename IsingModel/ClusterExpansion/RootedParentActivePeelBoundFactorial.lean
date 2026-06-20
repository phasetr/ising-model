import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelInduction
import IsingModel.ClusterExpansion.RootMomentBound

/-!
# The child-count peel bound in factorial-product form (GJ §18.5)

Bounding the root moment factor of the child-count peel bound by the root moment bound
`sum_allPolymers_cardPow_expWeighted_le`
(#4127) and collecting the per-vertex `(1−r)` powers (`r = Δ²e|t|`) recasts the peel
bound (at the full active set, exponent `0`) as a factorial product:

`rootedParentActivePeelBound G par univ (fun _ => 0) t`
` ≤ (|V|·∏_v (childCount v)!) / (1−r)^{2n+1}`,

since the per-vertex exponents `(childCount v + 1)` sum to `n + (n + 1) = 2n + 1` (the
child counts sum to `n`).  This is the form that pairs with the
spanning-tree factorial bound `∑_T ∏_v (childCount v)! ≤ 4^n·n!` (#4126).

* `rootedParentActivePeelBound_univ_zero_le_card_mul_prod_childCount_factorial_div`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **The peel bound in factorial-product form.**  For the full active set, exponent `0`,
and `0 < 1 − Δ²e|t|`, the child-count peel bound is at most
`(|V|·∏_v (childCount v)!)/(1 − Δ²e|t|)^{2n+1}`.  The root moment factor is bounded by
`sum_allPolymers_cardPow_expWeighted_le` (#4127), and the per-vertex `(1 − Δ²e|t|)` powers
`childCount v + 1` sum to `2n + 1` because the child counts sum to `n` (one parent-edge
per non-root vertex). -/
theorem rootedParentActivePeelBound_univ_zero_le_card_mul_prod_childCount_factorial_div
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (par : Fin n → Fin (n + 1))
    {t : ℝ} (hpos : 0 < 1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) :
    rootedParentActivePeelBound G par (Finset.univ : Finset (Fin n)) (fun _ => 0) t
      ≤ ((Fintype.card ι : ℝ)
          * ∏ v : Fin (n + 1),
              ((rootedParentChildCount par (Finset.univ : Finset (Fin n)) v).factorial : ℝ))
          / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (2 * n + 1) := by
  classical
  set q : ℝ := 1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hq
  set d : Fin (n + 1) → ℕ :=
    fun v => rootedParentChildCount par (Finset.univ : Finset (Fin n)) v with hd
  have hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1 := by linarith [hpos]
  have hqpos : 0 < q := hpos
  -- The child counts sum to n (one parent-edge per non-root vertex).
  have hsum_child : (∑ v : Fin (n + 1), d v) = n := by
    simp only [hd, rootedParentChildCount]
    rw [← Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (Fin (n + 1)))) (f := par) (fun i _ => Finset.mem_univ _)]
    simp
  -- The product of peel factors as a single fraction.
  have hprod : (∏ j : Fin n, rootedParentPeelFactor G t (d (Fin.succ j)))
      = (∏ j : Fin n, ((d (Fin.succ j)).factorial : ℝ))
          / q ^ (∑ j : Fin n, (d (Fin.succ j) + 1)) := by
    simp only [rootedParentPeelFactor, ← hq]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  -- The root moment factor.
  have hroot : (∑ P ∈ allPolymers G, (P.card : ℝ) ^ d 0 * (Real.exp 1 * |t|) ^ P.card)
      ≤ (Fintype.card ι : ℝ) * ((d 0).factorial : ℝ) / q ^ (d 0 + 1) := by
    rw [mul_div_assoc]
    exact sum_allPolymers_cardPow_expWeighted_le G (d 0) hkp
  -- Exponent arithmetic: ∑_j (childCount(succ j)+1) + (childCount 0 + 1) = 2n + 1.
  have hexp : (∑ j : Fin n, (d (Fin.succ j) + 1)) + (d 0 + 1) = 2 * n + 1 := by
    have hsplit : d 0 + ∑ j : Fin n, d (Fin.succ j) = n := by
      rw [← Fin.sum_univ_succ (fun v : Fin (n + 1) => d v)]; exact hsum_child
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
    omega
  -- The product over all vertices splits off the root.
  have hnum : ((d 0).factorial : ℝ) * (∏ j : Fin n, ((d (Fin.succ j)).factorial : ℝ))
      = ∏ v : Fin (n + 1), ((d v).factorial : ℝ) :=
    (Fin.prod_univ_succ (fun v : Fin (n + 1) => ((d v).factorial : ℝ))).symm
  -- Assemble.
  rw [rootedParentActivePeelBound]
  simp only [Nat.zero_add, ← hd]
  calc
    (∏ j : Fin n, rootedParentPeelFactor G t (d (Fin.succ j)))
        * ∑ P ∈ allPolymers G, (P.card : ℝ) ^ d 0 * (Real.exp 1 * |t|) ^ P.card
        ≤ (∏ j : Fin n, rootedParentPeelFactor G t (d (Fin.succ j)))
            * ((Fintype.card ι : ℝ) * ((d 0).factorial : ℝ) / q ^ (d 0 + 1)) := by
          refine mul_le_mul_of_nonneg_left hroot ?_
          exact Finset.prod_nonneg fun j _ => rootedParentPeelFactor_nonneg G hkp _
    _ = ((Fintype.card ι : ℝ) * ∏ v : Fin (n + 1), ((d v).factorial : ℝ)) / q ^ (2 * n + 1) := by
          rw [hprod, ← hnum, ← hexp, pow_add]
          field_simp
          ring

end IsingModel
