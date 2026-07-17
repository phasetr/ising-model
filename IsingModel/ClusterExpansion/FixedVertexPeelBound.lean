import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelInduction

/-!
# Fixed-vertex child-count peel bound in factorial-product form (GJ §18.5)

This module is the fixed-root analogue of
`rootedParentActivePeelBound_univ_zero_le_card_mul_prod_childCount_factorial_div`.
The non-root leaf-peel factors are unchanged, but the root moment is restricted to
polymers through one prescribed vertex. The per-vertex moment bound
`rootedPolymerActivity_cardPow_le` therefore removes the global factor `Fintype.card ι`.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **The fixed-vertex child-count gas peel bound.** The gas-parametrized fixed-root peel
bound: the non-root active vertices each carry a support-bump factor `c` (as in
`rootedGasParentActivePeelBound`), and the root moment is restricted to gas polymers (from
`𝓟`) whose support contains the fixed vertex `root`. The even gas (`allPolymers G`) takes
`c = 1` in `fixedVertexRootedParentActivePeelBound`. -/
noncomputable def fixedVertexRootedGasParentActivePeelBound (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (𝓟 : Finset (Finset (Sym2 ι))) (c : ℝ)
    (root : ι) (par : Fin n → Fin (n + 1))
    (A : Finset (Fin n)) (k : Fin (n + 1) → ℕ) (t : ℝ) : ℝ :=
  (∏ j ∈ A, c * rootedParentPeelFactor G t
      (k (Fin.succ j) + rootedParentChildCount par A (Fin.succ j)))
    * ∑ P ∈ rootedGasPolymers 𝓟 root,
        (P.card : ℝ) ^ (k 0 + rootedParentChildCount par A 0) * (Real.exp 1 * |t|) ^ P.card

/-- **The fixed-vertex child-count peel bound.** This is the same expression as
`rootedParentActivePeelBound`, except that the root moment is restricted to polymers whose
support contains the fixed vertex `root`. Even-gas (`allPolymers G`, `c = 1`) instance of
`fixedVertexRootedGasParentActivePeelBound`. -/
noncomputable def fixedVertexRootedParentActivePeelBound (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (root : ι) (par : Fin n → Fin (n + 1))
    (A : Finset (Fin n)) (k : Fin (n + 1) → ℕ) (t : ℝ) : ℝ :=
  fixedVertexRootedGasParentActivePeelBound G (allPolymers G) 1 root par A k t

/-- **Fixed-vertex factorial-product gas peel bound.** For the full active set, exponent
`0`, `0 < 1 − Δ²e|t|`, and `0 ≤ c`, the fixed-vertex child-count gas peel bound is at most
`c^n·(∏_v (childCount v)!)/(1 − Δ²e|t|)^{2n+1}`. Compared with
`rootedGasParentActivePeelBound_univ_zero_le_card_mul_prod_childCount_factorial_div`, the
only change is the root-moment estimate: `rootedGasPolymerActivity_cardPow_le` is used for
the fixed vertex `root`, so no factor `Fintype.card ι` appears. The even gas takes `c = 1`
in `fixedVertexRootedParentActivePeelBound_univ_zero_le_prod_childCount_factorial_div`. -/
theorem fixedVertexRootedGasParentActivePeelBound_univ_zero_le_prod_childCount_factorial_div
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {𝓟 : Finset (Finset (Sym2 ι))} (hgas : PolymerGasData G 𝓟) (c : ℝ) (hc : 0 ≤ c) (root : ι)
    (par : Fin n → Fin (n + 1)) {t : ℝ}
    (hpos : 0 < 1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) :
    fixedVertexRootedGasParentActivePeelBound G 𝓟 c root par (Finset.univ : Finset (Fin n))
        (fun _ => 0) t
      ≤ c ^ n * ((∏ v : Fin (n + 1),
              ((rootedParentChildCount par (Finset.univ : Finset (Fin n)) v).factorial : ℝ))
          / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (2 * n + 1)) := by
  classical
  set q : ℝ := 1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hq
  set d : Fin (n + 1) → ℕ :=
    fun v => rootedParentChildCount par (Finset.univ : Finset (Fin n)) v with hd
  have hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1 := by linarith [hpos]
  have hsum_child : (∑ v : Fin (n + 1), d v) = n := by
    simp only [hd, rootedParentChildCount]
    rw [← Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (Fin (n + 1)))) (f := par) (fun i _ => Finset.mem_univ _)]
    simp
  have hprod : (∏ j : Fin n, rootedParentPeelFactor G t (d (Fin.succ j)))
      = (∏ j : Fin n, ((d (Fin.succ j)).factorial : ℝ))
          / q ^ (∑ j : Fin n, (d (Fin.succ j) + 1)) := by
    simp only [rootedParentPeelFactor, ← hq]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hroot : (∑ P ∈ rootedGasPolymers 𝓟 root,
        (P.card : ℝ) ^ d 0 * (Real.exp 1 * |t|) ^ P.card)
      ≤ ((d 0).factorial : ℝ) / q ^ (d 0 + 1) := by
    simpa [hq] using
      rootedGasPolymerActivity_cardPow_le G hgas root (d 0) (by positivity)
        (u := Real.exp 1 * |t|) hkp
  have hexp : (∑ j : Fin n, (d (Fin.succ j) + 1)) + (d 0 + 1) = 2 * n + 1 := by
    have hsplit : d 0 + ∑ j : Fin n, d (Fin.succ j) = n := by
      rw [← Fin.sum_univ_succ (fun v : Fin (n + 1) => d v)]; exact hsum_child
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
    omega
  have hnum : ((d 0).factorial : ℝ) * (∏ j : Fin n, ((d (Fin.succ j)).factorial : ℝ))
      = ∏ v : Fin (n + 1), ((d v).factorial : ℝ) :=
    (Fin.prod_univ_succ (fun v : Fin (n + 1) => ((d v).factorial : ℝ))).symm
  have heven : (∏ j : Fin n, rootedParentPeelFactor G t (d (Fin.succ j)))
        * (((d 0).factorial : ℝ) / q ^ (d 0 + 1))
      = (∏ v : Fin (n + 1), ((d v).factorial : ℝ)) / q ^ (2 * n + 1) := by
    rw [hprod, ← hnum, ← hexp, pow_add]
    field_simp
    ring
  have hprodc : (∏ j : Fin n, c * rootedParentPeelFactor G t (d (Fin.succ j)))
      = c ^ n * ∏ j : Fin n, rootedParentPeelFactor G t (d (Fin.succ j)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [fixedVertexRootedGasParentActivePeelBound]
  simp only [Nat.zero_add, ← hd]
  calc
    (∏ j : Fin n, c * rootedParentPeelFactor G t (d (Fin.succ j)))
        * ∑ P ∈ rootedGasPolymers 𝓟 root, (P.card : ℝ) ^ d 0 * (Real.exp 1 * |t|) ^ P.card
        ≤ (∏ j : Fin n, c * rootedParentPeelFactor G t (d (Fin.succ j)))
            * (((d 0).factorial : ℝ) / q ^ (d 0 + 1)) := by
          refine mul_le_mul_of_nonneg_left hroot ?_
          exact Finset.prod_nonneg fun j _ =>
            mul_nonneg hc (rootedParentPeelFactor_nonneg G hkp _)
    _ = c ^ n * ((∏ v : Fin (n + 1), ((d v).factorial : ℝ)) / q ^ (2 * n + 1)) := by
          rw [hprodc, mul_assoc, heven]

/-- **Fixed-vertex factorial-product peel bound.** For the full active set, exponent `0`,
and `0 < 1 − Δ²e|t|`, the fixed-vertex child-count peel bound is at most
`(∏_v (childCount v)!)/(1 − Δ²e|t|)^{2n+1}`. Compared with
`rootedParentActivePeelBound_univ_zero_le_card_mul_prod_childCount_factorial_div`, the only
change is the root-moment estimate: `rootedPolymerActivity_cardPow_le` is used for the fixed
vertex `root`, so no factor `Fintype.card ι` appears. Even-gas (`c = 1`) instance of
`fixedVertexRootedGasParentActivePeelBound_univ_zero_le_prod_childCount_factorial_div`. -/
theorem fixedVertexRootedParentActivePeelBound_univ_zero_le_prod_childCount_factorial_div
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (root : ι)
    (par : Fin n → Fin (n + 1)) {t : ℝ}
    (hpos : 0 < 1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) :
    fixedVertexRootedParentActivePeelBound G root par (Finset.univ : Finset (Fin n))
        (fun _ => 0) t
      ≤ (∏ v : Fin (n + 1),
              ((rootedParentChildCount par (Finset.univ : Finset (Fin n)) v).factorial : ℝ))
          / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (2 * n + 1) := by
  have h := fixedVertexRootedGasParentActivePeelBound_univ_zero_le_prod_childCount_factorial_div
    G (evenPolymerGasData G) 1 zero_le_one root par hpos
  simpa [fixedVertexRootedParentActivePeelBound] using h

end IsingModel
