import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelStep

/-!
# The leaf-peel inequality for the active sum (GJ §18.5)

Bounding each `leafColumnSum` factor in the leaf-peel decomposition
(`rootedParentActiveSum_leaf_peel`) by its Kotecky--Preiss estimate
(`leafColumnSum_le`) and folding the resulting `|η ⟨par j, _⟩|` moment bump into the
remainder weight gives the **leaf-peel inequality**: for a leaf `j` and
`Δ²·e·|t| < 1`,

`rootedParentActiveSum G par A hclosed k t`
` ≤ (k (succ j))!/(1 − Δ²e|t|)^{k (succ j)+1}`
`   · rootedParentActiveSum G par (A.erase j) _ (update k (par j) (k (par j)+1)) t`.

The moment bump is realised by `Function.update k (par j) (k (par j) + 1)`: multiplying
the remainder weight by `|η ⟨par j, _⟩|` raises the exponent at the (unique) active
vertex `⟨par j, _⟩` of `A.erase j` by one.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **The leaf-peel inequality.**  For a leaf `j` of an active-closed set `A` and
`Δ²·e·|t| < 1` (`Δ = G.maxDegree`), the active sum over `A` is bounded by the leaf
Kotecky--Preiss factor times the active sum over `A.erase j` with the moment exponent at
the leaf's parent vertex bumped by one.  Each leaf column sum is bounded by
`leafColumnSum_le`, and the resulting `|η ⟨par j, _⟩|` factor is absorbed into the
remainder weight via `Function.update k (par j) (k (par j) + 1)`. -/
theorem rootedParentActiveSum_leaf_peel_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {par : Fin n → Fin (n + 1)} {A : Finset (Fin n)} {j : Fin n}
    (hclosed : RootedParentActiveClosed par A) (hleaf : RootedParentLeaf par A j)
    (k : Fin (n + 1) → ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    rootedParentActiveSum G par A hclosed k t
      ≤ ((k (Fin.succ j)).factorial : ℝ)
          / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (k (Fin.succ j) + 1)
        * rootedParentActiveSum G par (A.erase j) (hclosed.erase_leaf hleaf)
            (Function.update k (par j) (k (par j) + 1)) t := by
  classical
  set hclosed' : RootedParentActiveClosed par (A.erase j) := hclosed.erase_leaf hleaf with hhc'
  set q : ℝ := Real.exp 1 * |t| with hq
  set w₀ : RootedParentActive (A.erase j) := ⟨par j, hleaf.parent_mem_erase hclosed⟩ with hw₀
  set k' : Fin (n + 1) → ℕ := Function.update k (par j) (k (par j) + 1) with hk'
  set C : ℝ := ((k (Fin.succ j)).factorial : ℝ)
    / (1 - (G.maxDegree : ℝ) ^ 2 * q) ^ (k (Fin.succ j) + 1) with hC
  -- The remainder summand at a labelling `η` and exponent function `K`.
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
  -- Assemble the inequality from the decomposition.
  rw [rootedParentActiveSum_leaf_peel G hclosed hleaf k t]
  calc
    (∑ η ∈ Fintype.piFinset (fun _ : RootedParentActive (A.erase j) => allPolymers G),
        summand η k * leafColumnSum G (η w₀) (k (Fin.succ j)) t)
        ≤ ∑ η ∈ Fintype.piFinset (fun _ : RootedParentActive (A.erase j) => allPolymers G),
            summand η k' * C := by
          refine Finset.sum_le_sum fun η hη => ?_
          have hηmem : η w₀ ∈ allPolymers G := Fintype.mem_piFinset.mp hη w₀
          calc
            summand η k * leafColumnSum G (η w₀) (k (Fin.succ j)) t
                ≤ summand η k * ((η w₀).card : ℝ) * C := by
                  rw [mul_assoc]
                  refine mul_le_mul_of_nonneg_left ?_ (hsummand_nonneg η)
                  exact leafColumnSum_le G hηmem (k (Fin.succ j)) hkp
            _ = summand η k' * C := by rw [hbump η]
    _ = C * ∑ η ∈ Fintype.piFinset (fun _ : RootedParentActive (A.erase j) => allPolymers G),
          summand η k' := by rw [← Finset.sum_mul, mul_comm]
    _ = C * rootedParentActiveSum G par (A.erase j) hclosed'
          (Function.update k (par j) (k (par j) + 1)) t := by
        rw [rootedParentActiveSum]

end IsingModel
