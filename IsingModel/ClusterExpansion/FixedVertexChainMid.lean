import IsingModel.ClusterExpansion.FixedVertexChainEnds
import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelTailTree

/-!
# Fixed-vertex middle chain for the rooted Kotecky--Preiss bound (GJ §18.6)

This file supplies the root-filtered middle part of the fixed-vertex Route B chain.  The
root coordinate is kept inside the active-sum recursion all the way to the empty active
set, so the base root moment is over `rootedPolymers G root` rather than over
`allPolymers G`.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The root active vertex of an active set. -/
def rootedParentActiveRoot (A : Finset (Fin n)) : RootedParentActive A :=
  ⟨0, zero_mem_rootedParentActiveVertices A⟩

/-- The root active vertex coerces to `0`. -/
@[simp]
theorem rootedParentActiveRoot_coe (A : Finset (Fin n)) :
    (rootedParentActiveRoot A : Fin (n + 1)) = 0 := rfl

/-- The fixed-root-filtered active sum.  It is the usual active sum with the additional
condition that the root active coordinate contains the prescribed vertex `root`. -/
noncomputable def fixedVertexRootedParentActiveSum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (root : ι) (par : Fin n → Fin (n + 1)) (A : Finset (Fin n))
    (hclosed : RootedParentActiveClosed par A) (k : Fin (n + 1) → ℕ) (t : ℝ) : ℝ :=
  ∑ ω ∈ Fintype.piFinset (fun _ : RootedParentActive A => allPolymers G),
    (if root ∈ polymerSupport (ω (rootedParentActiveRoot A)) ∧
        ∀ j : Fin n, ∀ hj : j ∈ A,
          PolymersIncompatible (ω (rootedParentActiveChild hj))
            (ω (rootedParentActiveParent hclosed hj)) then
      ∏ v : RootedParentActive A,
        ((ω v).card : ℝ) ^ k v.1 * (Real.exp 1 * |t|) ^ (ω v).card
    else 0)

/-- Empty-active-set base case for the fixed-root active sum. -/
theorem fixedVertexRootedParentActiveSum_empty (G : SimpleGraph ι) [Fintype G.edgeSet]
    (root : ι) (par : Fin n → Fin (n + 1))
    (hclosed : RootedParentActiveClosed par (∅ : Finset (Fin n)))
    (k : Fin (n + 1) → ℕ) (t : ℝ) :
    fixedVertexRootedParentActiveSum G root par ∅ hclosed k t
      = ∑ P ∈ rootedPolymers G root,
          (P.card : ℝ) ^ k 0 * (Real.exp 1 * |t|) ^ P.card := by
  rw [fixedVertexRootedParentActiveSum]
  calc
    (∑ ω ∈ Fintype.piFinset (fun _ : RootedParentActive (∅ : Finset (Fin n)) =>
          allPolymers G),
        (if root ∈ polymerSupport (ω (rootedParentActiveRoot ∅)) ∧
            ∀ j : Fin n, ∀ hj : j ∈ (∅ : Finset (Fin n)),
              PolymersIncompatible (ω (rootedParentActiveChild hj))
                (ω (rootedParentActiveParent hclosed hj)) then
          ∏ v : RootedParentActive (∅ : Finset (Fin n)),
            ((ω v).card : ℝ) ^ k v.1 * (Real.exp 1 * |t|) ^ (ω v).card
        else 0))
        = ∑ P ∈ allPolymers G,
            if root ∈ polymerSupport P then
              (P.card : ℝ) ^ k 0 * (Real.exp 1 * |t|) ^ P.card
            else 0 := by
          refine Finset.sum_bij' (fun ω _ => ω default) (fun P _ => fun _ => P)
            (fun ω hω => ?_) (fun P hP => ?_) (fun ω hω => ?_) (fun P hP => ?_)
            (fun ω hω => ?_)
          · exact (Fintype.mem_piFinset.mp hω) default
          · exact Fintype.mem_piFinset.mpr fun _ => hP
          · funext v
            rw [Unique.eq_default v]
          · rfl
          · have hroot :
                ω (rootedParentActiveRoot (∅ : Finset (Fin n)))
                  = ω (default : RootedParentActive (∅ : Finset (Fin n))) := by
              exact congrArg ω (Unique.eq_default _)
            have hdefault : (default : RootedParentActive (∅ : Finset (Fin n))).1 = 0 := by
              calc
                (default : RootedParentActive (∅ : Finset (Fin n))).1
                    = (rootedParentActiveRoot (∅ : Finset (Fin n))).1 := by
                      exact congrArg Subtype.val (Unique.eq_default
                        (rootedParentActiveRoot (∅ : Finset (Fin n)))).symm
                _ = 0 := rfl
            simp [hroot, hdefault]
    _ = ∑ P ∈ rootedPolymers G root,
          (P.card : ℝ) ^ k 0 * (Real.exp 1 * |t|) ^ P.card := by
          rw [rootedPolymers, Finset.sum_filter]

/-- The fixed-root peel bound satisfies the same erase/update recursion as the unfiltered
peel bound. -/
theorem fixedVertexRootedParentActivePeelBound_erase_update
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (root : ι)
    {par : Fin n → Fin (n + 1)} {A : Finset (Fin n)} {j : Fin n}
    (hleaf : RootedParentLeaf par A j) (k : Fin (n + 1) → ℕ) (t : ℝ) :
    rootedParentPeelFactor G t (k (Fin.succ j))
        * fixedVertexRootedParentActivePeelBound G root par (A.erase j)
            (Function.update k (par j) (k (par j) + 1)) t
      = fixedVertexRootedParentActivePeelBound G root par A k t := by
  have hexp : ∀ v, Function.update k (par j) (k (par j) + 1) v
      + rootedParentChildCount par (A.erase j) v
        = k v + rootedParentChildCount par A v := by
    intro v
    rw [rootedParentChildCount_erase hleaf.1 v]
    by_cases h : v = par j
    · subst h
      rw [Function.update_self, if_pos rfl]
      omega
    · rw [Function.update_of_ne h, if_neg (fun e => h e.symm)]
      omega
  rw [fixedVertexRootedParentActivePeelBound, fixedVertexRootedParentActivePeelBound,
    Finset.prod_congr rfl (fun j' _ => by rw [hexp (Fin.succ j')]),
    Finset.sum_congr rfl (fun P _ => by rw [hexp 0])]
  rw [← mul_assoc, ← Finset.mul_prod_erase A _ hleaf.1]
  congr 2
  rw [rootedParentChildCount_leaf_succ hleaf, add_zero]

/-- Per-labelling leaf isolation with the fixed root filter threaded through the remainder. -/
theorem fixedVertexRootedParentActiveSum_leaf_inner
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] {par : Fin n → Fin (n + 1)}
    {A : Finset (Fin n)} {j : Fin n} (root : ι)
    (hclosed : RootedParentActiveClosed par A) (hleaf : RootedParentLeaf par A j)
    (k : Fin (n + 1) → ℕ) (t : ℝ)
    (η : RootedParentActive (A.erase j) → Finset (Sym2 ι)) :
    (∑ x ∈ allPolymers G,
        (if root ∈ polymerSupport
              ((rootedParentActiveSplitEquiv hleaf.1 (rootedParentActiveRoot A)).elim x η) ∧
            ∀ i, ∀ hi : i ∈ A,
              PolymersIncompatible
                ((rootedParentActiveSplitEquiv hleaf.1 (rootedParentActiveChild hi)).elim x η)
                ((rootedParentActiveSplitEquiv hleaf.1
                  (rootedParentActiveParent hclosed hi)).elim x η) then
          ∏ v : RootedParentActive A,
            (((rootedParentActiveSplitEquiv hleaf.1 v).elim x η).card : ℝ) ^ k v.1
              * (Real.exp 1 * |t|) ^ ((rootedParentActiveSplitEquiv hleaf.1 v).elim x η).card
        else 0))
      = (if root ∈ polymerSupport (η (rootedParentActiveRoot (A.erase j))) ∧
            ∀ i, ∀ hi : i ∈ A.erase j,
              PolymersIncompatible (η (rootedParentActiveChild hi))
                (η (rootedParentActiveParent (hclosed.erase_leaf hleaf) hi)) then
          ∏ w : RootedParentActive (A.erase j),
            ((η w).card : ℝ) ^ k w.1 * (Real.exp 1 * |t|) ^ (η w).card
        else 0)
        * leafColumnSum G (η ⟨par j, hleaf.parent_mem_erase hclosed⟩)
            (k (Fin.succ j)) t := by
  classical
  have hrootRecon : ∀ x : Finset (Sym2 ι),
      root ∈ polymerSupport
          ((rootedParentActiveSplitEquiv hleaf.1 (rootedParentActiveRoot A)).elim x η)
        ↔ root ∈ polymerSupport (η (rootedParentActiveRoot (A.erase j))) := by
    intro x
    have hmem : ((rootedParentActiveRoot A : RootedParentActive A) : Fin (n + 1))
        ∈ rootedParentActiveVertices (A.erase j) := by
      simp [rootedParentActiveRoot]
    rw [rootedParentActiveSplitEquiv_recon_some hleaf.1 x η hmem]
    have heq :
        (⟨(rootedParentActiveRoot A : RootedParentActive A), hmem⟩ :
            RootedParentActive (A.erase j))
          = rootedParentActiveRoot (A.erase j) := Subtype.ext rfl
    rw [heq]
  by_cases hroot : root ∈ polymerSupport (η (rootedParentActiveRoot (A.erase j)))
  · simpa [hrootRecon, hroot] using
      rootedParentActiveSum_leaf_inner G hclosed hleaf k t η
  · simp [hrootRecon, hroot]

/-- Leaf-peel decomposition for the fixed-root active sum. -/
theorem fixedVertexRootedParentActiveSum_leaf_peel
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] {par : Fin n → Fin (n + 1)}
    {A : Finset (Fin n)} {j : Fin n} (root : ι)
    (hclosed : RootedParentActiveClosed par A) (hleaf : RootedParentLeaf par A j)
    (k : Fin (n + 1) → ℕ) (t : ℝ) :
    fixedVertexRootedParentActiveSum G root par A hclosed k t
      = ∑ η ∈ Fintype.piFinset (fun _ : RootedParentActive (A.erase j) => allPolymers G),
          (if root ∈ polymerSupport (η (rootedParentActiveRoot (A.erase j))) ∧
              ∀ i, ∀ hi : i ∈ A.erase j,
                PolymersIncompatible (η (rootedParentActiveChild hi))
                  (η (rootedParentActiveParent (hclosed.erase_leaf hleaf) hi)) then
            ∏ w : RootedParentActive (A.erase j),
              ((η w).card : ℝ) ^ k w.1 * (Real.exp 1 * |t|) ^ (η w).card
          else 0)
          * leafColumnSum G (η ⟨par j, hleaf.parent_mem_erase hclosed⟩)
              (k (Fin.succ j)) t := by
  rw [fixedVertexRootedParentActiveSum,
    sum_piFinset_const_optionEquiv (rootedParentActiveSplitEquiv hleaf.1) (allPolymers G),
    Finset.sum_comm]
  exact Finset.sum_congr rfl fun η _ =>
    fixedVertexRootedParentActiveSum_leaf_inner G root hclosed hleaf k t η

/-- Tail leaf-peel inequality for the fixed-root active sum. -/
theorem fixedVertexRootedParentActiveSum_leaf_peel_tail_le
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] {par : Fin n → Fin (n + 1)}
    {A : Finset (Fin n)} {j : Fin n} (root : ι)
    (hclosed : RootedParentActiveClosed par A) (hleaf : RootedParentLeaf par A j)
    (k : Fin (n + 1) → ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    fixedVertexRootedParentActiveSum G root par A hclosed k t
      ≤ ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
          * (((k (Fin.succ j)).factorial : ℝ)
              / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (k (Fin.succ j) + 1))
        * fixedVertexRootedParentActiveSum G root par (A.erase j) (hclosed.erase_leaf hleaf)
            (Function.update k (par j) (k (par j) + 1)) t := by
  classical
  set hclosed' : RootedParentActiveClosed par (A.erase j) := hclosed.erase_leaf hleaf with hhc'
  set q : ℝ := Real.exp 1 * |t| with hq
  have hparent : par j ∈ rootedParentActiveVertices (A.erase j) :=
    hleaf.parent_mem_erase hclosed
  set w₀ : RootedParentActive (A.erase j) := ⟨par j, hparent⟩ with hw₀
  set k' : Fin (n + 1) → ℕ := Function.update k (par j) (k (par j) + 1) with hk'
  set Ct : ℝ := ((G.maxDegree : ℝ) ^ 2 * q)
    * (((k (Fin.succ j)).factorial : ℝ)
        / (1 - (G.maxDegree : ℝ) ^ 2 * q) ^ (k (Fin.succ j) + 1)) with hCt
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
  rw [fixedVertexRootedParentActiveSum_leaf_peel G root hclosed hleaf k t]
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
    _ = Ct * fixedVertexRootedParentActiveSum G root par (A.erase j) hclosed'
          (Function.update k (par j) (k (par j) + 1)) t := by
        rw [fixedVertexRootedParentActiveSum]

/-- Tail leaf-peel induction for the fixed-root active sum. -/
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
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  have hrr0 : (0 : ℝ) ≤ rr := by rw [hrr]; positivity
  suffices H : ∀ m (A : Finset (Fin n)), A.card = m →
      ∀ (hclosed : RootedParentActiveClosed par A) (k : Fin (n + 1) → ℕ),
        fixedVertexRootedParentActiveSum G root par A hclosed k t
          ≤ rr ^ A.card * fixedVertexRootedParentActivePeelBound G root par A k t by
    exact H A.card A rfl hclosed k
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro A hAcard hclosed k
    rcases A.eq_empty_or_nonempty with rfl | hne
    · rw [Finset.card_empty, pow_zero, one_mul,
        fixedVertexRootedParentActiveSum_empty]
      refine le_of_eq ?_
      have hcc : rootedParentChildCount par (∅ : Finset (Fin n)) 0 = 0 := by
        simp [rootedParentChildCount]
      rw [fixedVertexRootedParentActivePeelBound]
      simp only [hcc, Finset.prod_empty, one_mul, Nat.add_zero]
    · obtain ⟨j, hleaf⟩ := hleafExists hne
      have hlt : (A.erase j).card < m := by
        rw [← hAcard]
        exact Finset.card_erase_lt_of_mem hleaf.1
      have hcard : A.card = (A.erase j).card + 1 := by
        rw [Finset.card_erase_of_mem hleaf.1, Nat.sub_add_cancel (Finset.card_pos.mpr hne)]
      calc
        fixedVertexRootedParentActiveSum G root par A hclosed k t
            ≤ rr * rootedParentPeelFactor G t (k (Fin.succ j))
                * fixedVertexRootedParentActiveSum G root par (A.erase j)
                    (hclosed.erase_leaf hleaf) (Function.update k (par j) (k (par j) + 1))
                    t := by
              rw [hrr, rootedParentPeelFactor]
              exact fixedVertexRootedParentActiveSum_leaf_peel_tail_le G root hclosed
                hleaf k hkp
        _ ≤ rr * rootedParentPeelFactor G t (k (Fin.succ j))
              * (rr ^ (A.erase j).card
                  * fixedVertexRootedParentActivePeelBound G root par (A.erase j)
                    (Function.update k (par j) (k (par j) + 1)) t) := by
              refine mul_le_mul_of_nonneg_left ?_
                (mul_nonneg hrr0 (rootedParentPeelFactor_nonneg G hkp _))
              exact IH _ hlt (A.erase j) rfl (hclosed.erase_leaf hleaf) _
        _ = rr ^ A.card
              * (rootedParentPeelFactor G t (k (Fin.succ j))
                  * fixedVertexRootedParentActivePeelBound G root par (A.erase j)
                    (Function.update k (par j) (k (par j) + 1)) t) := by
              rw [hcard, pow_succ]
              ring
        _ = rr ^ A.card * fixedVertexRootedParentActivePeelBound G root par A k t := by
              rw [fixedVertexRootedParentActivePeelBound_erase_update G root hleaf k t]

/-- The univ fixed-root active sum in `Fin (n+1)` labelling form. -/
theorem fixedVertexRootedParentActiveSum_univ_zero_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (root : ι) (par : Fin n → Fin (n + 1)) (t : ℝ) :
    fixedVertexRootedParentActiveSum G root par (Finset.univ : Finset (Fin n))
        (rootedParentActiveClosed_univ par) (fun _ => 0) t
      = ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => root ∈ polymerSupport (ω 0)),
          if ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i)) (ω (par i)) then
            ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card
          else 0 := by
  rw [fixedVertexRootedParentActiveSum,
    sum_piFinset_const_domEquiv rootedParentActiveUnivEquiv (allPolymers G)]
  calc
    (∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G),
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
        = ∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G),
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
    _ = ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => root ∈ polymerSupport (ω 0)),
          if ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i)) (ω (par i)) then
            ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card
          else 0 := by
          rw [Finset.sum_filter]

/-- The complete-tree fixed-root active sum is bounded by the weighted fixed-root peel bound. -/
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
  have h := fixedVertexRootedParentActiveSum_le_pow_mul_childCount_bound G root
    (fun hB => completeGraphTreeParentCode_exists_active_leaf hB T)
    (Finset.univ : Finset (Fin n))
    (rootedParentActiveClosed_univ (Penrose.completeGraphTreeParentCode n T)) (fun _ => 0) hkp
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- Fubini swap of the fixed-root Penrose tree sum, retaining the root filter. -/
theorem fixedVertexRoot_penroseTreeSum_le_subtype_parentConstraint
    (G : SimpleGraph ι) [Fintype G.edgeSet] (v : ι) (n : ℕ)
    (W : (Fin (n + 1) → Finset (Sym2 ι)) → ℝ) (hW : ∀ ω, 0 ≤ W ω) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => v ∈ polymerSupport (ω 0)),
        ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω), W ω)
      ≤ ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ∑ ω ∈ ((Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
              (fun ω => v ∈ polymerSupport (ω 0))).filter
            (fun ω => ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
              (ω (Penrose.completeGraphTreeParentCode n T i))), W ω := by
  classical
  set P := (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
    (fun ω => v ∈ polymerSupport (ω 0)) with hP
  have hinner : ∀ ω, (∑ _T ∈ Penrose.spanningTreeEdgeSubsets
        (polymerSeqIncompatibilityGraph ω), W ω)
      = ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          (if T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω) then
            W ω else 0) := by
    intro ω
    rw [Finset.sum_coe_sort
      (Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1))))
      (fun S => if S ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω) then
        W ω else 0),
      ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (Penrose.spanningTreeEdgeSubsets_mono le_top)]
  calc
    (∑ ω ∈ P,
        ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω), W ω)
        = ∑ ω ∈ P, ∑ T : {S // S ∈ Penrose.spanningTreeEdgeSubsets
              (⊤ : SimpleGraph (Fin (n + 1)))},
            (if T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω) then
              W ω else 0) := Finset.sum_congr rfl fun ω _ => hinner ω
    _ = ∑ T : {S // S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ∑ ω ∈ P,
            (if T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω) then
              W ω else 0) := Finset.sum_comm
    _ = ∑ T : {S // S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ∑ ω ∈ P.filter (fun ω =>
            T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω)), W ω :=
          Finset.sum_congr rfl fun T _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ T : {S // S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ∑ ω ∈ P.filter (fun ω => ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
            (ω (Penrose.completeGraphTreeParentCode n T i))), W ω :=
          Finset.sum_le_sum fun T _ =>
            sum_filter_treeIncompat_le_filter_parentConstraint n T P W hW

/-- The fixed-root Penrose tree sum is bounded by the weighted fixed-root peel bound. -/
theorem fixedVertexRoot_penroseTreeSum_le_sum_pow_fixedVertexPeelBound
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) (n : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => v ∈ polymerSupport (ω 0)),
        ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
          |t| ^ (ω 0).card
            * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card
              * |t| ^ (ω (Fin.succ i)).card)
      ≤ ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
            * fixedVertexRootedParentActivePeelBound G v
                (Penrose.completeGraphTreeParentCode n T) (Finset.univ : Finset (Fin n))
                (fun _ => 0) t := by
  have hWle : ∀ ω : Fin (n + 1) → Finset (Sym2 ι),
      |t| ^ (ω 0).card
          * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card
            * |t| ^ (ω (Fin.succ i)).card
        ≤ ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card := by
    intro ω
    rw [Fin.prod_univ_succ,
      Finset.prod_congr rfl
        (g := fun i : Fin n => (Real.exp 1 * |t|) ^ (ω (Fin.succ i)).card)
        fun i _ => (mul_pow _ _ _).symm]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine pow_le_pow_left₀ (abs_nonneg t) ?_ _
    exact le_mul_of_one_le_left (abs_nonneg t) (Real.one_le_exp_iff.mpr zero_le_one)
  refine (fixedVertexRoot_penroseTreeSum_le_subtype_parentConstraint G v n
    (fun ω => |t| ^ (ω 0).card
      * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card
        * |t| ^ (ω (Fin.succ i)).card)
    (fun ω => by positivity)).trans ?_
  refine Finset.sum_le_sum fun T _ => ?_
  calc
    (∑ ω ∈ ((Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
        (fun ω => v ∈ polymerSupport (ω 0))).filter
        (fun ω => ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
          (ω (Penrose.completeGraphTreeParentCode n T i))),
        |t| ^ (ω 0).card
          * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card
            * |t| ^ (ω (Fin.succ i)).card)
        ≤ ∑ ω ∈ ((Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
            (fun ω => v ∈ polymerSupport (ω 0))).filter
            (fun ω => ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
              (ω (Penrose.completeGraphTreeParentCode n T i))),
            ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card :=
          Finset.sum_le_sum fun ω _ => hWle ω
    _ = ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
            (fun ω => v ∈ polymerSupport (ω 0)),
          if ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
              (ω (Penrose.completeGraphTreeParentCode n T i)) then
            ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card
          else 0 := by
          rw [Finset.sum_filter]
    _ = fixedVertexRootedParentActiveSum G v (Penrose.completeGraphTreeParentCode n T)
          (Finset.univ : Finset (Fin n))
          (rootedParentActiveClosed_univ (Penrose.completeGraphTreeParentCode n T))
          (fun _ => 0) t :=
          (fixedVertexRootedParentActiveSum_univ_zero_eq G v
            (Penrose.completeGraphTreeParentCode n T) t).symm
    _ ≤ ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
          * fixedVertexRootedParentActivePeelBound G v
              (Penrose.completeGraphTreeParentCode n T)
              (Finset.univ : Finset (Fin n)) (fun _ => 0) t := by
      exact
        fixedVertexRootedParentActiveSum_completeGraphTreeParentCode_univ_zero_le_pow_mul_peelBound
          G v n T hkp

/-- Fixed-root per-order geometric bound for the root-at-`0` term-absolute sum. -/
theorem fixedVertexRoot_termAbsSum_succ_le_div_mul_geometric
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t)
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => v ∈ polymerSupport (ω 0)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ (1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)))
        * (4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2) ^ n := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  have hrr0 : 0 ≤ rr := by rw [hrr]; positivity
  refine (fixedVertexRoot_termAbsSum_succ_le_treeSum_rootedExpActivity G v n ht).trans ?_
  refine (mul_le_mul_of_nonneg_left
    (fixedVertexRoot_penroseTreeSum_le_sum_pow_fixedVertexPeelBound G v n hkp)
    (by positivity)).trans ?_
  refine (mul_le_mul_of_nonneg_left
    (sum_pow_fixedVertexRootedParentActivePeelBound_le G v n hkp) (by positivity)).trans ?_
  have hfact : ((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ) ≤ 1 := by
    rw [← div_eq_inv_mul, div_le_one (by positivity)]
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  have hq2 : q ^ (2 * n + 1) = (q ^ 2) ^ n * q := by
    rw [pow_succ, pow_mul]
  have hgoal_nonneg : (0 : ℝ) ≤ (1 / q) * (4 * rr / q ^ 2) ^ n := by positivity
  have hLHS : ((n + 1).factorial : ℝ)⁻¹
        * ((rr ^ n * (4 : ℝ) ^ n * (n.factorial : ℝ)) / q ^ (2 * n + 1))
      = (((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ))
          * ((1 : ℝ) / q * (4 * rr / q ^ 2) ^ n) := by
    rw [div_pow, mul_pow, hq2]
    field_simp
    ring
  rw [hLHS]
  calc
    (((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ))
        * ((1 : ℝ) / q * (4 * rr / q ^ 2) ^ n)
        ≤ 1 * ((1 : ℝ) / q * (4 * rr / q ^ 2) ^ n) :=
          mul_le_mul_of_nonneg_right hfact hgoal_nonneg
    _ = (1 : ℝ) / q * (4 * rr / q ^ 2) ^ n := one_mul _

end IsingModel
