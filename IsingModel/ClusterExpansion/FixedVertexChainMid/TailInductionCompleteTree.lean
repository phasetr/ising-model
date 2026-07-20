import IsingModel.ClusterExpansion.FixedVertexChainMid.ActiveSumLeafPeel
import IsingModel.ClusterExpansion.RootedParentActiveLeafColumnTail
import IsingModel.ClusterExpansion.RootedParentActiveUnivReindex

/-!
# Fixed-vertex middle chain (2/3): tail leaf-peel induction and the complete-tree bound

Structural split (2/3) of `FixedVertexChainMid`.  This child holds the tail leaf-peel
inequality and the resulting strong induction
`fixedVertexRootedGasParentActiveSum_le_pow_mul_childCount_bound`, the `Fin (n+1)` labelling
form of the univ fixed-root active sum, and the complete-tree specialisation bounding it by
the weighted fixed-root peel bound.  It builds on the leaf-peel decomposition in the sibling
`...ActiveSumLeafPeel`.  See the `FixedVertexChainMid` facade module for the full contents
overview.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Tail leaf-peel inequality for the fixed-root active gas sum. -/
theorem fixedVertexRootedGasParentActiveSum_leaf_peel_tail_le
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {𝓟 : Finset (Finset (Sym2 ι))} (hgas : PolymerGasData G 𝓟) {c : ℝ}
    (hsupp : ∀ P ∈ 𝓟, ((polymerSupport P).card : ℝ) ≤ c * (P.card : ℝ))
    {par : Fin n → Fin (n + 1)} {A : Finset (Fin n)} {j : Fin n} (root : ι)
    (hclosed : RootedParentActiveClosed par A) (hleaf : RootedParentLeaf par A j)
    (k : Fin (n + 1) → ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    fixedVertexRootedGasParentActiveSum G 𝓟 root par A hclosed k t
      ≤ c * (((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
          * (((k (Fin.succ j)).factorial : ℝ)
              / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (k (Fin.succ j) + 1)))
        * fixedVertexRootedGasParentActiveSum G 𝓟 root par (A.erase j)
            (hclosed.erase_leaf hleaf)
            (Function.update k (par j) (k (par j) + 1)) t := by
  classical
  set hclosed' : RootedParentActiveClosed par (A.erase j) := hclosed.erase_leaf hleaf with hhc'
  set q : ℝ := Real.exp 1 * |t| with hq
  have hparent : par j ∈ rootedParentActiveVertices (A.erase j) :=
    hleaf.parent_mem_erase hclosed
  set w₀ : RootedParentActive (A.erase j) := ⟨par j, hparent⟩ with hw₀
  set k' : Fin (n + 1) → ℕ := Function.update k (par j) (k (par j) + 1) with hk'
  set Ct : ℝ := c * (((G.maxDegree : ℝ) ^ 2 * q)
    * (((k (Fin.succ j)).factorial : ℝ)
        / (1 - (G.maxDegree : ℝ) ^ 2 * q) ^ (k (Fin.succ j) + 1))) with hCt
  set summand : (RootedParentActive (A.erase j) → Finset (Sym2 ι)) →
      (Fin (n + 1) → ℕ) → ℝ :=
    fun η K =>
      if root ∈ polymerSupport (η (rootedParentActiveRoot (A.erase j))) ∧
          ∀ i, ∀ hi : i ∈ A.erase j,
            PolymersIncompatible (η (rootedParentActiveChild hi))
              (η (rootedParentActiveParent hclosed' hi)) then
        ∏ w : RootedParentActive (A.erase j), ((η w).card : ℝ) ^ K w.1 * q ^ (η w).card
      else 0 with hsummand
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
    by_cases hC' : root ∈ polymerSupport (η (rootedParentActiveRoot (A.erase j))) ∧
        ∀ i, ∀ hi : i ∈ A.erase j,
          PolymersIncompatible (η (rootedParentActiveChild hi))
            (η (rootedParentActiveParent hclosed' hi))
    · simp only [if_pos hC']
      exact hprod
    · simp only [if_neg hC', zero_mul]
  have hsummand_nonneg : ∀ η : RootedParentActive (A.erase j) → Finset (Sym2 ι),
      0 ≤ summand η k := by
    intro η
    simp only [hsummand]
    split_ifs
    · exact Finset.prod_nonneg fun w _ => by positivity
    · exact le_refl 0
  rw [fixedVertexRootedGasParentActiveSum_leaf_peel G 𝓟 root hclosed hleaf k t]
  calc
    (∑ η ∈ Fintype.piFinset (fun _ : RootedParentActive (A.erase j) => 𝓟),
        summand η k * leafGasColumnSum 𝓟 (η w₀) (k (Fin.succ j)) t)
        ≤ ∑ η ∈ Fintype.piFinset (fun _ : RootedParentActive (A.erase j) => 𝓟),
            summand η k' * Ct := by
          refine Finset.sum_le_sum fun η hη => ?_
          have hηmem : η w₀ ∈ 𝓟 := Fintype.mem_piFinset.mp hη w₀
          calc
            summand η k * leafGasColumnSum 𝓟 (η w₀) (k (Fin.succ j)) t
                ≤ summand η k * (((η w₀).card : ℝ) * Ct) := by
                  refine mul_le_mul_of_nonneg_left ?_ (hsummand_nonneg η)
                  have h := leafGasColumnSum_tail_le G hgas (η w₀) (k (Fin.succ j))
                    (hsupp (η w₀) hηmem) hkp
                  calc
                    leafGasColumnSum 𝓟 (η w₀) (k (Fin.succ j)) t
                        ≤ c * ((η w₀).card : ℝ)
                            * (((G.maxDegree : ℝ) ^ 2 * q)
                              * (((k (Fin.succ j)).factorial : ℝ)
                                  / (1 - (G.maxDegree : ℝ) ^ 2 * q) ^ (k (Fin.succ j) + 1))) := by
                          rw [hq]; exact h
                    _ = ((η w₀).card : ℝ) * Ct := by rw [hCt]; ring
            _ = summand η k * ((η w₀).card : ℝ) * Ct := by ring
            _ = summand η k' * Ct := by rw [hbump η]
    _ = Ct * ∑ η ∈ Fintype.piFinset (fun _ : RootedParentActive (A.erase j) => 𝓟),
          summand η k' := by rw [← Finset.sum_mul, mul_comm]
    _ = Ct * fixedVertexRootedGasParentActiveSum G 𝓟 root par (A.erase j) hclosed'
          (Function.update k (par j) (k (par j) + 1)) t := by
        rw [fixedVertexRootedGasParentActiveSum]

/-- Tail leaf-peel induction for the fixed-root active gas sum. -/
theorem fixedVertexRootedGasParentActiveSum_le_pow_mul_childCount_bound
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {𝓟 : Finset (Finset (Sym2 ι))} (hgas : PolymerGasData G 𝓟) {c : ℝ} (hc : 0 ≤ c)
    (hsupp : ∀ P ∈ 𝓟, ((polymerSupport P).card : ℝ) ≤ c * (P.card : ℝ)) (root : ι)
    {par : Fin n → Fin (n + 1)}
    (hleafExists : ∀ {B : Finset (Fin n)}, B.Nonempty → ∃ j, RootedParentLeaf par B j)
    (A : Finset (Fin n)) (hclosed : RootedParentActiveClosed par A)
    (k : Fin (n + 1) → ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    fixedVertexRootedGasParentActiveSum G 𝓟 root par A hclosed k t
      ≤ ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ A.card
          * fixedVertexRootedGasParentActivePeelBound G 𝓟 c root par A k t := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  have hrr0 : (0 : ℝ) ≤ rr := by rw [hrr]; positivity
  suffices H : ∀ m (A : Finset (Fin n)), A.card = m →
      ∀ (hclosed : RootedParentActiveClosed par A) (k : Fin (n + 1) → ℕ),
        fixedVertexRootedGasParentActiveSum G 𝓟 root par A hclosed k t
          ≤ rr ^ A.card * fixedVertexRootedGasParentActivePeelBound G 𝓟 c root par A k t by
    exact H A.card A rfl hclosed k
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro A hAcard hclosed k
    rcases A.eq_empty_or_nonempty with rfl | hne
    · rw [Finset.card_empty, pow_zero, one_mul,
        fixedVertexRootedGasParentActiveSum_empty]
      refine le_of_eq ?_
      have hcc : rootedParentChildCount par (∅ : Finset (Fin n)) 0 = 0 := by
        simp [rootedParentChildCount]
      rw [fixedVertexRootedGasParentActivePeelBound]
      simp only [hcc, Finset.prod_empty, one_mul, Nat.add_zero]
    · obtain ⟨j, hleaf⟩ := hleafExists hne
      have hlt : (A.erase j).card < m := by
        rw [← hAcard]
        exact Finset.card_erase_lt_of_mem hleaf.1
      have hcard : A.card = (A.erase j).card + 1 := by
        rw [Finset.card_erase_of_mem hleaf.1, Nat.sub_add_cancel (Finset.card_pos.mpr hne)]
      calc
        fixedVertexRootedGasParentActiveSum G 𝓟 root par A hclosed k t
            ≤ c * (rr * rootedParentPeelFactor G t (k (Fin.succ j)))
                * fixedVertexRootedGasParentActiveSum G 𝓟 root par (A.erase j)
                    (hclosed.erase_leaf hleaf) (Function.update k (par j) (k (par j) + 1))
                    t := by
              have h := fixedVertexRootedGasParentActiveSum_leaf_peel_tail_le G hgas hsupp
                root hclosed hleaf k hkp
              rw [hrr, rootedParentPeelFactor]
              calc
                fixedVertexRootedGasParentActiveSum G 𝓟 root par A hclosed k t
                    ≤ c * (((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
                        * (((k (Fin.succ j)).factorial : ℝ)
                            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
                                ^ (k (Fin.succ j) + 1)))
                      * fixedVertexRootedGasParentActiveSum G 𝓟 root par (A.erase j)
                          (hclosed.erase_leaf hleaf)
                          (Function.update k (par j) (k (par j) + 1)) t := h
                _ = c * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)
                        * (((k (Fin.succ j)).factorial : ℝ)
                            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
                                ^ (k (Fin.succ j) + 1)))
                      * fixedVertexRootedGasParentActiveSum G 𝓟 root par (A.erase j)
                          (hclosed.erase_leaf hleaf)
                          (Function.update k (par j) (k (par j) + 1)) t := by ring
        _ ≤ c * (rr * rootedParentPeelFactor G t (k (Fin.succ j)))
              * (rr ^ (A.erase j).card
                  * fixedVertexRootedGasParentActivePeelBound G 𝓟 c root par (A.erase j)
                    (Function.update k (par j) (k (par j) + 1)) t) := by
              refine mul_le_mul_of_nonneg_left ?_
                (mul_nonneg hc (mul_nonneg hrr0 (rootedParentPeelFactor_nonneg G hkp _)))
              exact IH _ hlt (A.erase j) rfl (hclosed.erase_leaf hleaf) _
        _ = rr ^ A.card
              * (c * rootedParentPeelFactor G t (k (Fin.succ j))
                  * fixedVertexRootedGasParentActivePeelBound G 𝓟 c root par (A.erase j)
                    (Function.update k (par j) (k (par j) + 1)) t) := by
              rw [hcard, pow_succ]
              ring
        _ = rr ^ A.card * fixedVertexRootedGasParentActivePeelBound G 𝓟 c root par A k t := by
              rw [fixedVertexRootedGasParentActivePeelBound_erase_update G 𝓟 c root hleaf k t]

/-- Tail leaf-peel induction for the fixed-root active sum.  Even-gas (`c = 1`) instance of
`fixedVertexRootedGasParentActiveSum_le_pow_mul_childCount_bound`. -/
theorem fixedVertexRootedParentActiveSum_le_pow_mul_childCount_bound
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (root : ι)
    {par : Fin n → Fin (n + 1)}
    (hleafExists : ∀ {B : Finset (Fin n)}, B.Nonempty → ∃ j, RootedParentLeaf par B j)
    (A : Finset (Fin n)) (hclosed : RootedParentActiveClosed par A)
    (k : Fin (n + 1) → ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    fixedVertexRootedParentActiveSum G root par A hclosed k t
      ≤ ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ A.card
          * fixedVertexRootedParentActivePeelBound G root par A k t := by
  have hsupp : ∀ P ∈ allPolymers G, ((polymerSupport P).card : ℝ) ≤ 1 * (P.card : ℝ) := by
    intro P hP
    rw [one_mul]; exact_mod_cast polymerSupport_card_le_card_of_mem_allPolymers G hP
  simpa [fixedVertexRootedParentActiveSum, fixedVertexRootedParentActivePeelBound] using
    fixedVertexRootedGasParentActiveSum_le_pow_mul_childCount_bound G (evenPolymerGasData G)
      zero_le_one hsupp root hleafExists A hclosed k hkp

/-- The univ fixed-root active gas sum in `Fin (n+1)` labelling form. -/
theorem fixedVertexRootedGasParentActiveSum_univ_zero_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (𝓟 : Finset (Finset (Sym2 ι))) (root : ι) (par : Fin n → Fin (n + 1)) (t : ℝ) :
    fixedVertexRootedGasParentActiveSum G 𝓟 root par (Finset.univ : Finset (Fin n))
        (rootedParentActiveClosed_univ par) (fun _ => 0) t
      = ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => 𝓟)).filter
          (fun ω => root ∈ polymerSupport (ω 0)),
          if ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i)) (ω (par i)) then
            ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card
          else 0 := by
  rw [fixedVertexRootedGasParentActiveSum,
    sum_piFinset_const_domEquiv rootedParentActiveUnivEquiv 𝓟]
  calc
    (∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => 𝓟),
        (if root ∈ polymerSupport
              ((fun a => ω (rootedParentActiveUnivEquiv a))
                (rootedParentActiveRoot (Finset.univ : Finset (Fin n)))) ∧
            ∀ j : Fin n, ∀ hj : j ∈ (Finset.univ : Finset (Fin n)),
              PolymersIncompatible
                ((fun a => ω (rootedParentActiveUnivEquiv a)) (rootedParentActiveChild hj))
                ((fun a => ω (rootedParentActiveUnivEquiv a))
                  (rootedParentActiveParent (rootedParentActiveClosed_univ par) hj)) then
          ∏ v : RootedParentActive (Finset.univ : Finset (Fin n)),
            (((fun a => ω (rootedParentActiveUnivEquiv a)) v).card : ℝ) ^ (fun _ => 0) v.1
              * (Real.exp 1 * |t|) ^
                ((fun a => ω (rootedParentActiveUnivEquiv a)) v).card
        else 0))
        = ∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => 𝓟),
            if root ∈ polymerSupport (ω 0) then
              if ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i)) (ω (par i)) then
                ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card
              else 0
            else 0 := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          have hroot :
              root ∈ polymerSupport
                  ((fun a => ω (rootedParentActiveUnivEquiv a))
                    (rootedParentActiveRoot (Finset.univ : Finset (Fin n))))
                ↔ root ∈ polymerSupport (ω 0) := by
            simp [rootedParentActiveRoot]
          have hconstraint :
              (∀ j : Fin n, ∀ hj : j ∈ (Finset.univ : Finset (Fin n)),
                PolymersIncompatible
                  ((fun a => ω (rootedParentActiveUnivEquiv a)) (rootedParentActiveChild hj))
                  ((fun a => ω (rootedParentActiveUnivEquiv a))
                    (rootedParentActiveParent (rootedParentActiveClosed_univ par) hj)))
                ↔ ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i)) (ω (par i)) := by
            constructor
            · intro h i
              have := h i (Finset.mem_univ i)
              simpa [rootedParentActiveChild, rootedParentActiveParent,
                rootedParentActiveUnivEquiv_apply] using this
            · intro h j _
              have := h j
              simpa [rootedParentActiveChild, rootedParentActiveParent,
                rootedParentActiveUnivEquiv_apply] using this
          have hprod :
              (∏ v : RootedParentActive (Finset.univ : Finset (Fin n)),
                (((fun a => ω (rootedParentActiveUnivEquiv a)) v).card : ℝ) ^ 0
                  * (Real.exp 1 * |t|) ^
                    ((fun a => ω (rootedParentActiveUnivEquiv a)) v).card)
                = ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card := by
            simp only [pow_zero, one_mul]
            rw [← Equiv.prod_comp rootedParentActiveUnivEquiv
              (fun a : Fin (n + 1) => (Real.exp 1 * |t|) ^ (ω a).card)]
          by_cases hroot' :
              root ∈ polymerSupport
                ((fun a => ω (rootedParentActiveUnivEquiv a))
                  (rootedParentActiveRoot (Finset.univ : Finset (Fin n))))
          · by_cases hconstraint' :
                ∀ j : Fin n, ∀ hj : j ∈ (Finset.univ : Finset (Fin n)),
                  PolymersIncompatible
                    ((fun a => ω (rootedParentActiveUnivEquiv a))
                      (rootedParentActiveChild hj))
                    ((fun a => ω (rootedParentActiveUnivEquiv a))
                      (rootedParentActiveParent (rootedParentActiveClosed_univ par) hj))
            · rw [if_pos ⟨hroot', hconstraint'⟩, if_pos (hroot.mp hroot'),
                if_pos (hconstraint.mp hconstraint'), hprod]
            · rw [if_neg (fun h => hconstraint' h.2), if_pos (hroot.mp hroot'),
                if_neg (fun h => hconstraint' (hconstraint.mpr h))]
          · rw [if_neg (fun h => hroot' h.1),
              if_neg (fun h => hroot' (hroot.mpr h))]
    _ = ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => 𝓟)).filter
          (fun ω => root ∈ polymerSupport (ω 0)),
          if ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i)) (ω (par i)) then
            ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card
          else 0 := by
          rw [Finset.sum_filter]

/-- The univ fixed-root active sum in `Fin (n+1)` labelling form.  Even-gas instance of
`fixedVertexRootedGasParentActiveSum_univ_zero_eq`. -/
theorem fixedVertexRootedParentActiveSum_univ_zero_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (root : ι) (par : Fin n → Fin (n + 1)) (t : ℝ) :
    fixedVertexRootedParentActiveSum G root par (Finset.univ : Finset (Fin n))
        (rootedParentActiveClosed_univ par) (fun _ => 0) t
      = ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => root ∈ polymerSupport (ω 0)),
          if ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i)) (ω (par i)) then
            ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card
          else 0 :=
  fixedVertexRootedGasParentActiveSum_univ_zero_eq G (allPolymers G) root par t

/-- The complete-tree fixed-root active gas sum is bounded by the weighted fixed-root gas
peel bound. -/
theorem fixedVertexRootedGasParentActiveSum_completeTree_univ_zero_le_pow_mul_peelBound
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {𝓟 : Finset (Finset (Sym2 ι))} (hgas : PolymerGasData G 𝓟) {c : ℝ} (hc : 0 ≤ c)
    (hsupp : ∀ P ∈ 𝓟, ((polymerSupport P).card : ℝ) ≤ c * (P.card : ℝ)) (root : ι) (n : ℕ)
    (T : {S : Finset (Sym2 (Fin (n + 1))) //
      S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))}) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    fixedVertexRootedGasParentActiveSum G 𝓟 root (Penrose.completeGraphTreeParentCode n T)
        (Finset.univ : Finset (Fin n))
        (rootedParentActiveClosed_univ (Penrose.completeGraphTreeParentCode n T))
        (fun _ => 0) t
      ≤ ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
          * fixedVertexRootedGasParentActivePeelBound G 𝓟 c root
              (Penrose.completeGraphTreeParentCode n T)
              (Finset.univ : Finset (Fin n)) (fun _ => 0) t := by
  have h := fixedVertexRootedGasParentActiveSum_le_pow_mul_childCount_bound G hgas hc hsupp root
    (fun hB => completeGraphTreeParentCode_exists_active_leaf hB T)
    (Finset.univ : Finset (Fin n))
    (rootedParentActiveClosed_univ (Penrose.completeGraphTreeParentCode n T)) (fun _ => 0) hkp
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- The complete-tree fixed-root active sum is bounded by the weighted fixed-root peel bound.
Even-gas (`c = 1`) instance of
`fixedVertexRootedGasParentActiveSum_completeTree_univ_zero_le_pow_mul_peelBound`. -/
theorem fixedVertexRootedParentActiveSum_completeGraphTreeParentCode_univ_zero_le_pow_mul_peelBound
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (root : ι) (n : ℕ)
    (T : {S : Finset (Sym2 (Fin (n + 1))) //
      S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))}) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    fixedVertexRootedParentActiveSum G root (Penrose.completeGraphTreeParentCode n T)
        (Finset.univ : Finset (Fin n))
        (rootedParentActiveClosed_univ (Penrose.completeGraphTreeParentCode n T))
        (fun _ => 0) t
      ≤ ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
          * fixedVertexRootedParentActivePeelBound G root
              (Penrose.completeGraphTreeParentCode n T)
              (Finset.univ : Finset (Fin n)) (fun _ => 0) t := by
  have hsupp : ∀ P ∈ allPolymers G, ((polymerSupport P).card : ℝ) ≤ 1 * (P.card : ℝ) := by
    intro P hP
    rw [one_mul]; exact_mod_cast polymerSupport_card_le_card_of_mem_allPolymers G hP
  simpa [fixedVertexRootedParentActiveSum, fixedVertexRootedParentActivePeelBound] using
    fixedVertexRootedGasParentActiveSum_completeTree_univ_zero_le_pow_mul_peelBound G
      (evenPolymerGasData G) zero_le_one hsupp root n T hkp

end IsingModel
