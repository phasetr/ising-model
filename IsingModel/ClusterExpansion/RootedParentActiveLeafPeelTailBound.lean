import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelStep
import IsingModel.ClusterExpansion.RootedParentActiveLeafColumnTail

/-!
# The sharpened (tail) leaf-peel inequality for the active sum (GJ §18.5)

The tail sharpening of the leaf-peel inequality (`rootedParentActiveSum_leaf_peel_le`,
#4113): bounding each `leafColumnSum` factor by its tail estimate
(`leafColumnSum_tail_le`, #4123, which carries an extra factor `Δ²e|t|`) gives one
induction step with an extra `Δ²e|t|` factor:

`rootedParentActiveSum G par A hclosed k t`
` ≤ (Δ²e|t|)·(k (succ j))!/(1−Δ²e|t|)^{k (succ j)+1}`
`   · rootedParentActiveSum G par (A.erase j) _ (update k (par j) (k (par j)+1)) t`.

The extra `Δ²e|t|` per peeled vertex is what makes the iterated bound summable over the
Mayer order `n` (one factor per non-root vertex).

* `rootedParentActiveSum_leaf_peel_tail_le`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **The sharpened (tail) leaf-peel inequality.**  For a leaf `j` of an active-closed
set `A` and `Δ²e|t| < 1`, the active sum over `A` is bounded by `Δ²e|t|` times the leaf
Kotecky--Preiss factor times the active sum over `A.erase j` with the moment exponent at
the leaf's parent vertex bumped by one.  Identical to `rootedParentActiveSum_leaf_peel_le`
but using the tail leaf-column bound `leafColumnSum_tail_le`, which contributes the extra
`Δ²e|t|` factor. -/
theorem rootedParentActiveSum_leaf_peel_tail_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {par : Fin n → Fin (n + 1)} {A : Finset (Fin n)} {j : Fin n}
    (hclosed : RootedParentActiveClosed par A) (hleaf : RootedParentLeaf par A j)
    (k : Fin (n + 1) → ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    rootedParentActiveSum G par A hclosed k t
      ≤ ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
          * (((k (Fin.succ j)).factorial : ℝ)
              / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (k (Fin.succ j) + 1))
        * rootedParentActiveSum G par (A.erase j) (hclosed.erase_leaf hleaf)
            (Function.update k (par j) (k (par j) + 1)) t := by
  classical
  set hclosed' : RootedParentActiveClosed par (A.erase j) := hclosed.erase_leaf hleaf with hhc'
  set q : ℝ := Real.exp 1 * |t| with hq
  set w₀ : RootedParentActive (A.erase j) := ⟨par j, hleaf.parent_mem_erase hclosed⟩ with hw₀
  set k' : Fin (n + 1) → ℕ := Function.update k (par j) (k (par j) + 1) with hk'
  set Ct : ℝ := ((G.maxDegree : ℝ) ^ 2 * q)
    * (((k (Fin.succ j)).factorial : ℝ) / (1 - (G.maxDegree : ℝ) ^ 2 * q) ^ (k (Fin.succ j) + 1))
    with hCt
  set summand : (RootedParentActive (A.erase j) → Finset (Sym2 ι)) → (Fin (n + 1) → ℕ) → ℝ :=
    fun η K =>
      if ∀ i, ∀ hi : i ∈ A.erase j,
          PolymersIncompatible (η (rootedParentActiveChild hi))
            (η (rootedParentActiveParent hclosed' hi)) then
        ∏ w : RootedParentActive (A.erase j), ((η w).card : ℝ) ^ K w.1 * q ^ (η w).card
      else 0 with hsummand
  -- Multiplying the remainder weight by `|η w₀|` bumps the exponent at `w₀ = ⟨par j, _⟩`.
  have hbump : ∀ η : RootedParentActive (A.erase j) → Finset (Sym2 ι),
      summand η k * ((η w₀).card : ℝ) = summand η k' := by
    intro η
    have key : ∀ w : RootedParentActive (A.erase j),
        ((η w).card : ℝ) ^ k' w.1 * q ^ (η w).card
          = (((η w).card : ℝ) ^ k w.1 * q ^ (η w).card)
              * (if w = w₀ then ((η w₀).card : ℝ) else 1) := by
      intro w
      by_cases hw : w = w₀
      · subst hw
        rw [if_pos rfl, hk', show (w₀ : Fin (n + 1)) = par j from rfl,
          Function.update_self, pow_succ]
        ring
      · rw [if_neg hw, hk',
          Function.update_of_ne (show (w : Fin (n + 1)) ≠ par j from
            fun h => hw (Subtype.ext h)), mul_one]
    have hprod : (∏ w : RootedParentActive (A.erase j),
          ((η w).card : ℝ) ^ k w.1 * q ^ (η w).card) * ((η w₀).card : ℝ)
        = ∏ w : RootedParentActive (A.erase j),
          ((η w).card : ℝ) ^ k' w.1 * q ^ (η w).card := by
      symm
      rw [Finset.prod_congr rfl fun w _ => key w, Finset.prod_mul_distrib]
      congr 1
      simp
    simp only [hsummand]
    by_cases hC' : ∀ i, ∀ hi : i ∈ A.erase j,
        PolymersIncompatible (η (rootedParentActiveChild hi))
          (η (rootedParentActiveParent hclosed' hi))
    · simp only [if_pos hC']
      exact hprod
    · simp only [if_neg hC', zero_mul]
  -- The remainder summand is nonnegative.
  have hsummand_nonneg : ∀ η : RootedParentActive (A.erase j) → Finset (Sym2 ι),
      0 ≤ summand η k := by
    intro η
    simp only [hsummand]
    split_ifs
    · exact Finset.prod_nonneg fun w _ => by positivity
    · exact le_refl 0
  -- Assemble the inequality from the decomposition, using the tail leaf-column bound.
  rw [rootedParentActiveSum_leaf_peel G hclosed hleaf k t]
  calc
    (∑ η ∈ Fintype.piFinset (fun _ : RootedParentActive (A.erase j) => allPolymers G),
        summand η k * leafColumnSum G (η w₀) (k (Fin.succ j)) t)
        ≤ ∑ η ∈ Fintype.piFinset (fun _ : RootedParentActive (A.erase j) => allPolymers G),
            summand η k' * Ct := by
          refine Finset.sum_le_sum fun η hη => ?_
          have hηmem : η w₀ ∈ allPolymers G := Fintype.mem_piFinset.mp hη w₀
          calc
            summand η k * leafColumnSum G (η w₀) (k (Fin.succ j)) t
                ≤ summand η k * (((η w₀).card : ℝ) * Ct) := by
                  refine mul_le_mul_of_nonneg_left ?_ (hsummand_nonneg η)
                  exact leafColumnSum_tail_le G hηmem (k (Fin.succ j)) hkp
            _ = summand η k * ((η w₀).card : ℝ) * Ct := by ring
            _ = summand η k' * Ct := by rw [hbump η]
    _ = Ct * ∑ η ∈ Fintype.piFinset (fun _ : RootedParentActive (A.erase j) => allPolymers G),
          summand η k' := by rw [← Finset.sum_mul, mul_comm]
    _ = Ct * rootedParentActiveSum G par (A.erase j) hclosed'
          (Function.update k (par j) (k (par j) + 1)) t := by
        rw [rootedParentActiveSum]

end IsingModel
