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

omit [DecidableEq ι] in
/-- **The gas peel bound in factorial-product form.**  For the full active set, exponent
`0`, `0 < 1 − Δ²e|t|`, and `0 ≤ c`, the child-count gas peel bound is at most
`c^n·(|V|·∏_v (childCount v)!)/(1 − Δ²e|t|)^{2n+1}`.  The root moment factor is bounded by
`sum_gasPolymers_cardPow_expWeighted_le`, the `c` factors collect into `c^n` (one per
non-root vertex), and the per-vertex `(1 − Δ²e|t|)` powers `childCount v + 1` sum to
`2n + 1` because the child counts sum to `n`.  The even gas (`allPolymers G`) takes `c = 1`
in `rootedParentActivePeelBound_univ_zero_le_card_mul_prod_childCount_factorial_div`. -/
theorem rootedGasParentActivePeelBound_univ_zero_le_card_mul_prod_childCount_factorial_div
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {𝓟 : Finset (Finset (Sym2 ι))} (hgas : PolymerGasData G 𝓟) (c : ℝ) (hc : 0 ≤ c)
    (par : Fin n → Fin (n + 1))
    {t : ℝ} (hpos : 0 < 1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) :
    rootedGasParentActivePeelBound G 𝓟 c par (Finset.univ : Finset (Fin n)) (fun _ => 0) t
      ≤ c ^ n * (((Fintype.card ι : ℝ)
          * ∏ v : Fin (n + 1),
              ((rootedParentChildCount par (Finset.univ : Finset (Fin n)) v).factorial : ℝ))
          / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (2 * n + 1)) := by
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
  have hroot : (∑ P ∈ 𝓟, (P.card : ℝ) ^ d 0 * (Real.exp 1 * |t|) ^ P.card)
      ≤ (Fintype.card ι : ℝ) * ((d 0).factorial : ℝ) / q ^ (d 0 + 1) := by
    rw [mul_div_assoc]
    exact sum_gasPolymers_cardPow_expWeighted_le G hgas (d 0) hkp
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
  -- The even-shaped fraction identity (root moment fraction times the peel-factor product).
  have heven : (∏ j : Fin n, rootedParentPeelFactor G t (d (Fin.succ j)))
        * ((Fintype.card ι : ℝ) * ((d 0).factorial : ℝ) / q ^ (d 0 + 1))
      = ((Fintype.card ι : ℝ) * ∏ v : Fin (n + 1), ((d v).factorial : ℝ)) / q ^ (2 * n + 1) := by
    rw [hprod, ← hnum, ← hexp, pow_add]
    field_simp
    ring
  -- The `c` factors collect into `c ^ n`.
  have hprodc : (∏ j : Fin n, c * rootedParentPeelFactor G t (d (Fin.succ j)))
      = c ^ n * ∏ j : Fin n, rootedParentPeelFactor G t (d (Fin.succ j)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Assemble.
  rw [rootedGasParentActivePeelBound]
  simp only [Nat.zero_add, ← hd]
  calc
    (∏ j : Fin n, c * rootedParentPeelFactor G t (d (Fin.succ j)))
        * ∑ P ∈ 𝓟, (P.card : ℝ) ^ d 0 * (Real.exp 1 * |t|) ^ P.card
        ≤ (∏ j : Fin n, c * rootedParentPeelFactor G t (d (Fin.succ j)))
            * ((Fintype.card ι : ℝ) * ((d 0).factorial : ℝ) / q ^ (d 0 + 1)) := by
          refine mul_le_mul_of_nonneg_left hroot ?_
          exact Finset.prod_nonneg fun j _ => mul_nonneg hc (rootedParentPeelFactor_nonneg G hkp _)
    _ = c ^ n * (((Fintype.card ι : ℝ) * ∏ v : Fin (n + 1), ((d v).factorial : ℝ))
          / q ^ (2 * n + 1)) := by
          rw [hprodc, mul_assoc, heven]

/-- **The peel bound in factorial-product form.**  For the full active set, exponent `0`,
and `0 < 1 − Δ²e|t|`, the child-count peel bound is at most
`(|V|·∏_v (childCount v)!)/(1 − Δ²e|t|)^{2n+1}`.  Even-gas (`c = 1`) instance of
`rootedGasParentActivePeelBound_univ_zero_le_card_mul_prod_childCount_factorial_div`. -/
theorem rootedParentActivePeelBound_univ_zero_le_card_mul_prod_childCount_factorial_div
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (par : Fin n → Fin (n + 1))
    {t : ℝ} (hpos : 0 < 1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) :
    rootedParentActivePeelBound G par (Finset.univ : Finset (Fin n)) (fun _ => 0) t
      ≤ ((Fintype.card ι : ℝ)
          * ∏ v : Fin (n + 1),
              ((rootedParentChildCount par (Finset.univ : Finset (Fin n)) v).factorial : ℝ))
          / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (2 * n + 1) := by
  rw [rootedParentActivePeelBound]
  simpa using rootedGasParentActivePeelBound_univ_zero_le_card_mul_prod_childCount_factorial_div
    G (evenPolymerGasData G) 1 zero_le_one par hpos

end IsingModel
