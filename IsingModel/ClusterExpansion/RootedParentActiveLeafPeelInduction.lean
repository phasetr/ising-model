import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelBound

/-!
# The leaf-peel induction for the active sum (GJ §18.5)

Iterating the leaf-peel inequality (`rootedParentActiveSum_leaf_peel_le`) down to the
empty active set (base case `rootedParentActiveSum_empty`) yields a closed-form bound on
`rootedParentActiveSum` in terms of *child counts*.  The key observation (avoiding any
bump bookkeeping) is that the exponent a vertex `v` will carry when it is finally peeled
is statically `k v + #{i ∈ A | par i = v}`: the running moment-exponent plus the number
of its still-active children.

* `rootedParentChildCount par A v := #{i ∈ A | par i = v}` — the active out-degree.
* `rootedParentPeelFactor G t d := d!/(1 − Δ²e|t|)^{d+1}` — one leaf's Kotecky--Preiss
  factor.
* `rootedParentActivePeelBound G par A k t` — the product of peel factors over the
  active vertices (each at its child-count-shifted exponent) times the root moment sum.
* `rootedParentActiveSum_le_childCount_bound`: `rootedParentActiveSum ≤
  rootedParentActivePeelBound`, by strong induction on `A.card`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- **The active out-degree.**  The number of still-active vertices whose parent is
`v`: `#{i ∈ A | par i = v}`. -/
def rootedParentChildCount (par : Fin n → Fin (n + 1)) (A : Finset (Fin n))
    (v : Fin (n + 1)) : ℕ :=
  (A.filter fun i => par i = v).card

/-- **A leaf has no active children.**  If `j` is a leaf of `A` then no active vertex
has `Fin.succ j` as parent, so the child count at `Fin.succ j` is zero. -/
theorem rootedParentChildCount_leaf_succ {par : Fin n → Fin (n + 1)}
    {A : Finset (Fin n)} {j : Fin n} (hleaf : RootedParentLeaf par A j) :
    rootedParentChildCount par A (Fin.succ j) = 0 := by
  rw [rootedParentChildCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun i hi => hleaf.2 i hi

/-- **Erasing a vertex decreases its parent's child count by one.**  For `j ∈ A`,
`#{i ∈ A | par i = v} = #{i ∈ A.erase j | par i = v} + (if par j = v then 1 else 0)`. -/
theorem rootedParentChildCount_erase {par : Fin n → Fin (n + 1)}
    {A : Finset (Fin n)} {j : Fin n} (hj : j ∈ A) (v : Fin (n + 1)) :
    rootedParentChildCount par A v
      = rootedParentChildCount par (A.erase j) v + (if par j = v then 1 else 0) := by
  rw [rootedParentChildCount, rootedParentChildCount]
  conv_lhs => rw [← Finset.insert_erase hj]
  rw [Finset.filter_insert]
  by_cases h : par j = v
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem
      (fun hmem => Finset.notMem_erase j A (Finset.mem_of_mem_filter j hmem))]
  · rw [if_neg h, if_neg h, add_zero]

/-- **One leaf's Kotecky--Preiss factor.**  `d!/(1 − Δ²e|t|)^{d+1}`, the bound on a
single leaf column sum from `leafColumnSum_le`. -/
noncomputable def rootedParentPeelFactor (G : SimpleGraph ι) [DecidableRel G.Adj]
    (t : ℝ) (d : ℕ) : ℝ :=
  (d.factorial : ℝ) / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1)

/-- The peel factor is nonnegative when `Δ²·e·|t| < 1`. -/
theorem rootedParentPeelFactor_nonneg (G : SimpleGraph ι) [DecidableRel G.Adj] {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) (d : ℕ) :
    0 ≤ rootedParentPeelFactor G t d := by
  rw [rootedParentPeelFactor]
  exact div_nonneg (by positivity) (le_of_lt (pow_pos (by linarith) _))

section

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The child-count peel bound (gas form).**  The product of `c`-scaled leaf
Kotecky--Preiss factors over the active vertices, each at the child-count-shifted exponent
`k (succ j) + child count`, times the root moment sum over the gas `𝓟` at exponent
`k 0 + child count at the root`.  The `c` factor per active vertex is the support-bump
constant of the gas; the even gas (`allPolymers G`) takes `c = 1` in
`rootedParentActivePeelBound`. -/
noncomputable def rootedGasParentActivePeelBound (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (𝓟 : Finset (Finset (Sym2 ι))) (c : ℝ) (par : Fin n → Fin (n + 1))
    (A : Finset (Fin n)) (k : Fin (n + 1) → ℕ) (t : ℝ) : ℝ :=
  (∏ j ∈ A, c * rootedParentPeelFactor G t
      (k (Fin.succ j) + rootedParentChildCount par A (Fin.succ j)))
    * ∑ P ∈ 𝓟,
        (P.card : ℝ) ^ (k 0 + rootedParentChildCount par A 0) * (Real.exp 1 * |t|) ^ P.card

/-- **The child-count peel bound.**  Even-gas (`allPolymers G`, `c = 1`) instance of
`rootedGasParentActivePeelBound`. -/
noncomputable def rootedParentActivePeelBound (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (par : Fin n → Fin (n + 1)) (A : Finset (Fin n))
    (k : Fin (n + 1) → ℕ) (t : ℝ) : ℝ :=
  rootedGasParentActivePeelBound G (allPolymers G) 1 par A k t

omit [DecidableEq ι] in
/-- **The peel-bound recursion identity (gas form).**  Extracting the `c`-scaled leaf
factor at `j` and bumping the exponent at `par j` (compensating the child-count drop from
erasing `j`) recovers the gas peel bound for `A` from the gas peel bound for `A.erase j`. -/
theorem rootedGasParentActivePeelBound_erase_update (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (𝓟 : Finset (Finset (Sym2 ι))) (c : ℝ) {par : Fin n → Fin (n + 1)}
    {A : Finset (Fin n)} {j : Fin n}
    (hleaf : RootedParentLeaf par A j) (k : Fin (n + 1) → ℕ) (t : ℝ) :
    c * rootedParentPeelFactor G t (k (Fin.succ j))
        * rootedGasParentActivePeelBound G 𝓟 c par (A.erase j)
            (Function.update k (par j) (k (par j) + 1)) t
      = rootedGasParentActivePeelBound G 𝓟 c par A k t := by
  have hexp : ∀ v, Function.update k (par j) (k (par j) + 1) v
      + rootedParentChildCount par (A.erase j) v = k v + rootedParentChildCount par A v := by
    intro v
    rw [rootedParentChildCount_erase hleaf.1 v]
    by_cases h : v = par j
    · subst h; rw [Function.update_self, if_pos rfl]; omega
    · rw [Function.update_of_ne h, if_neg (fun e => h e.symm)]; omega
  rw [rootedGasParentActivePeelBound, rootedGasParentActivePeelBound,
    Finset.prod_congr rfl (fun j' _ => by rw [hexp (Fin.succ j')]),
    Finset.sum_congr rfl (fun P _ => by rw [hexp 0])]
  rw [← mul_assoc, ← Finset.mul_prod_erase A _ hleaf.1]
  congr 2
  rw [rootedParentChildCount_leaf_succ hleaf, add_zero]

/-- **The peel-bound recursion identity.**  Even-gas (`c = 1`) instance of
`rootedGasParentActivePeelBound_erase_update`. -/
theorem rootedParentActivePeelBound_erase_update (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {par : Fin n → Fin (n + 1)} {A : Finset (Fin n)} {j : Fin n}
    (hleaf : RootedParentLeaf par A j) (k : Fin (n + 1) → ℕ) (t : ℝ) :
    rootedParentPeelFactor G t (k (Fin.succ j))
        * rootedParentActivePeelBound G par (A.erase j)
            (Function.update k (par j) (k (par j) + 1)) t
      = rootedParentActivePeelBound G par A k t := by
  rw [rootedParentActivePeelBound, rootedParentActivePeelBound,
    ← rootedGasParentActivePeelBound_erase_update G (allPolymers G) 1 hleaf k t, one_mul]

/-- **The leaf-peel induction bound (gas form).**  For a parent function in which every
nonempty active set has a leaf (e.g. a rank-decreasing parent), `Δ²·e·|t| < 1`, a
support-cardinality bound `|supp P| ≤ c·|P|` for all `P ∈ 𝓟`, and `0 ≤ c`, the active gas
sum is bounded by the child-count gas peel bound, obtained by iterating the leaf-peel
inequality down to the empty active set.  The even gas (`allPolymers G`) takes `c = 1` in
`rootedParentActiveSum_le_childCount_bound`. -/
theorem rootedGasParentActiveSum_le_childCount_bound (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {𝓟 : Finset (Finset (Sym2 ι))} (hgas : PolymerGasData G 𝓟)
    {par : Fin n → Fin (n + 1)}
    (hleafExists : ∀ {B : Finset (Fin n)}, B.Nonempty → ∃ j, RootedParentLeaf par B j)
    (A : Finset (Fin n)) (hclosed : RootedParentActiveClosed par A) (k : Fin (n + 1) → ℕ)
    {c : ℝ} (hsupp : ∀ P ∈ 𝓟, ((polymerSupport P).card : ℝ) ≤ c * (P.card : ℝ)) (hc : 0 ≤ c)
    {t : ℝ} (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    rootedGasParentActiveSum G 𝓟 par A hclosed k t
      ≤ rootedGasParentActivePeelBound G 𝓟 c par A k t := by
  suffices H : ∀ m (A : Finset (Fin n)), A.card = m → ∀ (hclosed : RootedParentActiveClosed par A)
      (k : Fin (n + 1) → ℕ), rootedGasParentActiveSum G 𝓟 par A hclosed k t
        ≤ rootedGasParentActivePeelBound G 𝓟 c par A k t by
    exact H A.card A rfl hclosed k
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro A hAcard hclosed k
    rcases A.eq_empty_or_nonempty with rfl | hne
    · rw [rootedGasParentActiveSum_empty]
      refine le_of_eq ?_
      have hcc : rootedParentChildCount par (∅ : Finset (Fin n)) 0 = 0 := by
        simp [rootedParentChildCount]
      rw [rootedGasParentActivePeelBound]
      simp only [hcc, Finset.prod_empty, one_mul, Nat.add_zero]
    · obtain ⟨j, hleaf⟩ := hleafExists hne
      have hlt : (A.erase j).card < m := by
        rw [← hAcard]; exact Finset.card_erase_lt_of_mem hleaf.1
      calc
        rootedGasParentActiveSum G 𝓟 par A hclosed k t
            ≤ c * rootedParentPeelFactor G t (k (Fin.succ j))
                * rootedGasParentActiveSum G 𝓟 par (A.erase j) (hclosed.erase_leaf hleaf)
                    (Function.update k (par j) (k (par j) + 1)) t := by
              rw [rootedParentPeelFactor]
              exact rootedGasParentActiveSum_leaf_peel_le G hgas hclosed hleaf k hsupp hkp
        _ ≤ c * rootedParentPeelFactor G t (k (Fin.succ j))
              * rootedGasParentActivePeelBound G 𝓟 c par (A.erase j)
                  (Function.update k (par j) (k (par j) + 1)) t := by
              refine mul_le_mul_of_nonneg_left ?_
                (mul_nonneg hc (rootedParentPeelFactor_nonneg G hkp _))
              exact IH _ hlt (A.erase j) rfl (hclosed.erase_leaf hleaf) _
        _ = rootedGasParentActivePeelBound G 𝓟 c par A k t :=
              rootedGasParentActivePeelBound_erase_update G 𝓟 c hleaf k t

/-- **The leaf-peel induction bound.**  Even-gas (`c = 1`) instance of
`rootedGasParentActiveSum_le_childCount_bound`, discharging the support bound via
`polymerSupport_card_le_card_of_mem_allPolymers`. -/
theorem rootedParentActiveSum_le_childCount_bound (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {par : Fin n → Fin (n + 1)}
    (hleafExists : ∀ {B : Finset (Fin n)}, B.Nonempty → ∃ j, RootedParentLeaf par B j)
    (A : Finset (Fin n)) (hclosed : RootedParentActiveClosed par A) (k : Fin (n + 1) → ℕ)
    {t : ℝ} (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    rootedParentActiveSum G par A hclosed k t
      ≤ rootedParentActivePeelBound G par A k t := by
  have hsupp : ∀ P ∈ allPolymers G, ((polymerSupport P).card : ℝ) ≤ 1 * (P.card : ℝ) := by
    intro P hP; rw [one_mul]; exact_mod_cast polymerSupport_card_le_card_of_mem_allPolymers G hP
  exact rootedGasParentActiveSum_le_childCount_bound G (evenPolymerGasData G) hleafExists A hclosed
    k hsupp zero_le_one hkp

end

end IsingModel
