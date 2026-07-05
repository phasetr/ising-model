import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelInduction
import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelTailBound

/-!
# The sharpened (tail) leaf-peel induction (GJ §18.5)

Iterating the tail leaf-peel inequality (`rootedParentActiveSum_leaf_peel_tail_le`,
#4128) down to the empty active set, and reusing the peel-bound recursion identity
(`rootedParentActivePeelBound_erase_update`, #4114), gives the child-count peel bound with
an extra factor `(Δ²e|t|)^{|A|}` — one `Δ²e|t|` per peeled (non-root) vertex:

`rootedParentActiveSum G par A hclosed k t`
` ≤ (Δ²e|t|)^{|A|}·rootedParentActivePeelBound G par A k t`.

* `rootedParentActiveSum_le_pow_mul_childCount_bound`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **The sharpened (tail) leaf-peel induction bound (gas form).**  For a parent function
in which every nonempty active set has a leaf, `Δ²e|t| < 1`, a support-cardinality bound
`|supp P| ≤ c·|P|` for all `P ∈ 𝓟`, and `0 ≤ c`, the active gas sum is bounded by
`(Δ²e|t|)^{|A|}` times the child-count gas peel bound, obtained by iterating the tail
leaf-peel inequality down to the empty active set.  The extra `(Δ²e|t|)^{|A|}` factor
(one `Δ²e|t|` per peeled non-root vertex) is the source of the geometric `(4r)^n` decay in
the cluster-expansion convergence.  The even gas (`allPolymers G`) takes `c = 1` in
`rootedParentActiveSum_le_pow_mul_childCount_bound`. -/
theorem rootedGasParentActiveSum_le_pow_mul_childCount_bound (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {𝓟 : Finset (Finset (Sym2 ι))}
    (hgas : PolymerGasData G 𝓟) {par : Fin n → Fin (n + 1)}
    (hleafExists : ∀ {B : Finset (Fin n)}, B.Nonempty → ∃ j, RootedParentLeaf par B j)
    (A : Finset (Fin n)) (hclosed : RootedParentActiveClosed par A) (k : Fin (n + 1) → ℕ)
    {c : ℝ} (hsupp : ∀ P ∈ 𝓟, ((polymerSupport P).card : ℝ) ≤ c * (P.card : ℝ)) (hc : 0 ≤ c)
    {t : ℝ} (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    rootedGasParentActiveSum G 𝓟 par A hclosed k t
      ≤ ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ A.card
          * rootedGasParentActivePeelBound G 𝓟 c par A k t := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  have hrr0 : (0 : ℝ) ≤ rr := by rw [hrr]; positivity
  suffices H : ∀ m (A : Finset (Fin n)), A.card = m → ∀ (hclosed : RootedParentActiveClosed par A)
      (k : Fin (n + 1) → ℕ), rootedGasParentActiveSum G 𝓟 par A hclosed k t
        ≤ rr ^ A.card * rootedGasParentActivePeelBound G 𝓟 c par A k t by
    exact H A.card A rfl hclosed k
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro A hAcard hclosed k
    rcases A.eq_empty_or_nonempty with rfl | hne
    · rw [Finset.card_empty, pow_zero, one_mul, rootedGasParentActiveSum_empty]
      refine le_of_eq ?_
      have hcc : rootedParentChildCount par (∅ : Finset (Fin n)) 0 = 0 := by
        simp [rootedParentChildCount]
      rw [rootedGasParentActivePeelBound]
      simp only [hcc, Finset.prod_empty, one_mul, Nat.add_zero]
    · obtain ⟨j, hleaf⟩ := hleafExists hne
      have hlt : (A.erase j).card < m := by
        rw [← hAcard]; exact Finset.card_erase_lt_of_mem hleaf.1
      have hcard : A.card = (A.erase j).card + 1 := by
        rw [Finset.card_erase_of_mem hleaf.1, Nat.sub_add_cancel (Finset.card_pos.mpr hne)]
      calc
        rootedGasParentActiveSum G 𝓟 par A hclosed k t
            ≤ c * (rr * rootedParentPeelFactor G t (k (Fin.succ j)))
                * rootedGasParentActiveSum G 𝓟 par (A.erase j) (hclosed.erase_leaf hleaf)
                    (Function.update k (par j) (k (par j) + 1)) t := by
              rw [hrr, rootedParentPeelFactor]
              exact rootedGasParentActiveSum_leaf_peel_tail_le G hgas hclosed hleaf k hsupp hkp
        _ ≤ c * (rr * rootedParentPeelFactor G t (k (Fin.succ j)))
              * (rr ^ (A.erase j).card * rootedGasParentActivePeelBound G 𝓟 c par (A.erase j)
                  (Function.update k (par j) (k (par j) + 1)) t) := by
              refine mul_le_mul_of_nonneg_left ?_
                (mul_nonneg hc (mul_nonneg hrr0 (rootedParentPeelFactor_nonneg G hkp _)))
              exact IH _ hlt (A.erase j) rfl (hclosed.erase_leaf hleaf) _
        _ = rr ^ A.card
              * (c * rootedParentPeelFactor G t (k (Fin.succ j))
                  * rootedGasParentActivePeelBound G 𝓟 c par (A.erase j)
                    (Function.update k (par j) (k (par j) + 1)) t) := by
              rw [hcard, pow_succ]; ring
        _ = rr ^ A.card * rootedGasParentActivePeelBound G 𝓟 c par A k t := by
              rw [rootedGasParentActivePeelBound_erase_update G 𝓟 c hleaf k t]

/-- **The sharpened (tail) leaf-peel induction bound.**  Even-gas (`c = 1`) instance of
`rootedGasParentActiveSum_le_pow_mul_childCount_bound`, discharging the support bound via
`polymerSupport_card_le_card_of_mem_allPolymers`. -/
theorem rootedParentActiveSum_le_pow_mul_childCount_bound (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {par : Fin n → Fin (n + 1)}
    (hleafExists : ∀ {B : Finset (Fin n)}, B.Nonempty → ∃ j, RootedParentLeaf par B j)
    (A : Finset (Fin n)) (hclosed : RootedParentActiveClosed par A) (k : Fin (n + 1) → ℕ)
    {t : ℝ} (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    rootedParentActiveSum G par A hclosed k t
      ≤ ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ A.card
          * rootedParentActivePeelBound G par A k t := by
  have hsupp : ∀ P ∈ allPolymers G, ((polymerSupport P).card : ℝ) ≤ 1 * (P.card : ℝ) := by
    intro P hP; rw [one_mul]; exact_mod_cast polymerSupport_card_le_card_of_mem_allPolymers G hP
  exact rootedGasParentActiveSum_le_pow_mul_childCount_bound G (evenPolymerGasData G) hleafExists A
    hclosed k hsupp zero_le_one hkp

end IsingModel
