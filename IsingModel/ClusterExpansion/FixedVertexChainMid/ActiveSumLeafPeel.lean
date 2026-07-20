import IsingModel.ClusterExpansion.FixedVertexPeelBound
import IsingModel.ClusterExpansion.RootedParentActiveLeafInner

/-!
# Fixed-vertex middle chain (1/3): the fixed-root active sum and its leaf peel

Structural split (1/3) of `FixedVertexChainMid`.  This child holds the root active vertex
`rootedParentActiveRoot`, the fixed-root-filtered active gas sum
`fixedVertexRootedGasParentActiveSum` with its empty-active-set base case, the erase/update
recursion of the fixed-root peel bound, and the per-labelling leaf isolation and leaf-peel
decomposition.  The tail induction lives in the sibling `...TailInductionCompleteTree`, and
the Penrose tree / geometric bounds in `...PenroseTreeGeometric`.  See the
`FixedVertexChainMid` facade module for the full contents overview.
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

/-- The fixed-root-filtered active gas sum.  It is the usual active gas sum (labellings by
polymers of `𝓟`) with the additional condition that the root active coordinate contains the
prescribed vertex `root`.  The even gas (`allPolymers G`) is recovered by
`fixedVertexRootedParentActiveSum`. -/
noncomputable def fixedVertexRootedGasParentActiveSum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (𝓟 : Finset (Finset (Sym2 ι))) (root : ι) (par : Fin n → Fin (n + 1)) (A : Finset (Fin n))
    (hclosed : RootedParentActiveClosed par A) (k : Fin (n + 1) → ℕ) (t : ℝ) : ℝ :=
  ∑ ω ∈ Fintype.piFinset (fun _ : RootedParentActive A => 𝓟),
    (if root ∈ polymerSupport (ω (rootedParentActiveRoot A)) ∧
        ∀ j : Fin n, ∀ hj : j ∈ A,
          PolymersIncompatible (ω (rootedParentActiveChild hj))
            (ω (rootedParentActiveParent hclosed hj)) then
      ∏ v : RootedParentActive A,
        ((ω v).card : ℝ) ^ k v.1 * (Real.exp 1 * |t|) ^ (ω v).card
    else 0)

/-- The fixed-root-filtered active sum.  Even-gas (`allPolymers G`) instance of
`fixedVertexRootedGasParentActiveSum`. -/
noncomputable def fixedVertexRootedParentActiveSum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (root : ι) (par : Fin n → Fin (n + 1)) (A : Finset (Fin n))
    (hclosed : RootedParentActiveClosed par A) (k : Fin (n + 1) → ℕ) (t : ℝ) : ℝ :=
  fixedVertexRootedGasParentActiveSum G (allPolymers G) root par A hclosed k t

/-- Empty-active-set base case for the fixed-root active gas sum. -/
theorem fixedVertexRootedGasParentActiveSum_empty (G : SimpleGraph ι) [Fintype G.edgeSet]
    (𝓟 : Finset (Finset (Sym2 ι))) (root : ι) (par : Fin n → Fin (n + 1))
    (hclosed : RootedParentActiveClosed par (∅ : Finset (Fin n)))
    (k : Fin (n + 1) → ℕ) (t : ℝ) :
    fixedVertexRootedGasParentActiveSum G 𝓟 root par ∅ hclosed k t
      = ∑ P ∈ rootedGasPolymers 𝓟 root,
          (P.card : ℝ) ^ k 0 * (Real.exp 1 * |t|) ^ P.card := by
  rw [fixedVertexRootedGasParentActiveSum]
  calc
    (∑ ω ∈ Fintype.piFinset (fun _ : RootedParentActive (∅ : Finset (Fin n)) => 𝓟),
        (if root ∈ polymerSupport (ω (rootedParentActiveRoot ∅)) ∧
            ∀ j : Fin n, ∀ hj : j ∈ (∅ : Finset (Fin n)),
              PolymersIncompatible (ω (rootedParentActiveChild hj))
                (ω (rootedParentActiveParent hclosed hj)) then
          ∏ v : RootedParentActive (∅ : Finset (Fin n)),
            ((ω v).card : ℝ) ^ k v.1 * (Real.exp 1 * |t|) ^ (ω v).card
        else 0))
        = ∑ P ∈ 𝓟,
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
    _ = ∑ P ∈ rootedGasPolymers 𝓟 root,
          (P.card : ℝ) ^ k 0 * (Real.exp 1 * |t|) ^ P.card := by
          rw [rootedGasPolymers, Finset.sum_filter]

/-- Empty-active-set base case for the fixed-root active sum.  Even-gas instance of
`fixedVertexRootedGasParentActiveSum_empty`. -/
theorem fixedVertexRootedParentActiveSum_empty (G : SimpleGraph ι) [Fintype G.edgeSet]
    (root : ι) (par : Fin n → Fin (n + 1))
    (hclosed : RootedParentActiveClosed par (∅ : Finset (Fin n)))
    (k : Fin (n + 1) → ℕ) (t : ℝ) :
    fixedVertexRootedParentActiveSum G root par ∅ hclosed k t
      = ∑ P ∈ rootedPolymers G root,
          (P.card : ℝ) ^ k 0 * (Real.exp 1 * |t|) ^ P.card :=
  fixedVertexRootedGasParentActiveSum_empty G (allPolymers G) root par hclosed k t

/-- The fixed-root gas peel bound satisfies the same erase/update recursion as the
unfiltered gas peel bound. -/
theorem fixedVertexRootedGasParentActivePeelBound_erase_update
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (𝓟 : Finset (Finset (Sym2 ι))) (c : ℝ) (root : ι)
    {par : Fin n → Fin (n + 1)} {A : Finset (Fin n)} {j : Fin n}
    (hleaf : RootedParentLeaf par A j) (k : Fin (n + 1) → ℕ) (t : ℝ) :
    c * rootedParentPeelFactor G t (k (Fin.succ j))
        * fixedVertexRootedGasParentActivePeelBound G 𝓟 c root par (A.erase j)
            (Function.update k (par j) (k (par j) + 1)) t
      = fixedVertexRootedGasParentActivePeelBound G 𝓟 c root par A k t := by
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
  rw [fixedVertexRootedGasParentActivePeelBound, fixedVertexRootedGasParentActivePeelBound,
    Finset.prod_congr rfl (fun j' _ => by rw [hexp (Fin.succ j')]),
    Finset.sum_congr rfl (fun P _ => by rw [hexp 0])]
  rw [← mul_assoc, ← Finset.mul_prod_erase A _ hleaf.1]
  congr 2
  rw [rootedParentChildCount_leaf_succ hleaf, add_zero]

/-- The fixed-root peel bound satisfies the same erase/update recursion as the unfiltered
peel bound.  Even-gas (`c = 1`) instance of
`fixedVertexRootedGasParentActivePeelBound_erase_update`. -/
theorem fixedVertexRootedParentActivePeelBound_erase_update
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (root : ι)
    {par : Fin n → Fin (n + 1)} {A : Finset (Fin n)} {j : Fin n}
    (hleaf : RootedParentLeaf par A j) (k : Fin (n + 1) → ℕ) (t : ℝ) :
    rootedParentPeelFactor G t (k (Fin.succ j))
        * fixedVertexRootedParentActivePeelBound G root par (A.erase j)
            (Function.update k (par j) (k (par j) + 1)) t
      = fixedVertexRootedParentActivePeelBound G root par A k t := by
  rw [fixedVertexRootedParentActivePeelBound, fixedVertexRootedParentActivePeelBound,
    ← fixedVertexRootedGasParentActivePeelBound_erase_update G (allPolymers G) 1 root hleaf k t,
    one_mul]

/-- Per-labelling leaf isolation with the fixed root filter threaded through the remainder
(gas form). -/
theorem fixedVertexRootedGasParentActiveSum_leaf_inner
    (𝓟 : Finset (Finset (Sym2 ι))) {par : Fin n → Fin (n + 1)}
    {A : Finset (Fin n)} {j : Fin n} (root : ι)
    (hclosed : RootedParentActiveClosed par A) (hleaf : RootedParentLeaf par A j)
    (k : Fin (n + 1) → ℕ) (t : ℝ)
    (η : RootedParentActive (A.erase j) → Finset (Sym2 ι)) :
    (∑ x ∈ 𝓟,
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
        * leafGasColumnSum 𝓟 (η ⟨par j, hleaf.parent_mem_erase hclosed⟩)
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
      rootedGasParentActiveSum_leaf_inner 𝓟 hclosed hleaf k t η
  · simp [hrootRecon, hroot]

/-- Per-labelling leaf isolation with the fixed root filter threaded through the remainder.
Even-gas (`allPolymers G`) instance of `fixedVertexRootedGasParentActiveSum_leaf_inner`. -/
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
            (k (Fin.succ j)) t :=
  fixedVertexRootedGasParentActiveSum_leaf_inner (allPolymers G) root hclosed hleaf k t η

/-- Leaf-peel decomposition for the fixed-root active gas sum. -/
theorem fixedVertexRootedGasParentActiveSum_leaf_peel
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (𝓟 : Finset (Finset (Sym2 ι))) {par : Fin n → Fin (n + 1)}
    {A : Finset (Fin n)} {j : Fin n} (root : ι)
    (hclosed : RootedParentActiveClosed par A) (hleaf : RootedParentLeaf par A j)
    (k : Fin (n + 1) → ℕ) (t : ℝ) :
    fixedVertexRootedGasParentActiveSum G 𝓟 root par A hclosed k t
      = ∑ η ∈ Fintype.piFinset (fun _ : RootedParentActive (A.erase j) => 𝓟),
          (if root ∈ polymerSupport (η (rootedParentActiveRoot (A.erase j))) ∧
              ∀ i, ∀ hi : i ∈ A.erase j,
                PolymersIncompatible (η (rootedParentActiveChild hi))
                  (η (rootedParentActiveParent (hclosed.erase_leaf hleaf) hi)) then
            ∏ w : RootedParentActive (A.erase j),
              ((η w).card : ℝ) ^ k w.1 * (Real.exp 1 * |t|) ^ (η w).card
          else 0)
          * leafGasColumnSum 𝓟 (η ⟨par j, hleaf.parent_mem_erase hclosed⟩)
              (k (Fin.succ j)) t := by
  rw [fixedVertexRootedGasParentActiveSum,
    sum_piFinset_const_optionEquiv (rootedParentActiveSplitEquiv hleaf.1) 𝓟,
    Finset.sum_comm]
  exact Finset.sum_congr rfl fun η _ =>
    fixedVertexRootedGasParentActiveSum_leaf_inner 𝓟 root hclosed hleaf k t η

/-- Leaf-peel decomposition for the fixed-root active sum.  Even-gas instance of
`fixedVertexRootedGasParentActiveSum_leaf_peel`. -/
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
              (k (Fin.succ j)) t :=
  fixedVertexRootedGasParentActiveSum_leaf_peel G (allPolymers G) root hclosed hleaf k t

end IsingModel
