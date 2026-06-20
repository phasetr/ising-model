import IsingModel.ClusterExpansion.RootedParentActiveSplitApply
import IsingModel.ClusterExpansion.RootedParentActiveLeafPeel
import IsingModel.ClusterExpansion.RootedParentActiveLeafColumn

/-!
# Per-labelling leaf isolation (GJ §18.5)

The leaf-peel inductive step peels the leaf coordinate out of `rootedParentActiveSum`.
Applying `sum_piFinset_const_optionEquiv` rewrites a labelling `ω` of the active
vertices of `A` as `ω = fun a => (rootedParentActiveSplitEquiv hj a).elim x η`, with a
leaf value `x ∈ allPolymers G` and a remainder labelling `η` of the active vertices of
`A.erase j`.  This file performs the per-`η` isolation: summing the reconstructed
summand over the leaf value `x` factors as the remainder summand (the summand of
`rootedParentActiveSum` for `A.erase j` at `η`) times the leaf column sum at the
remainder value `η ⟨par j, _⟩` assigned to the leaf's parent vertex.

* `rootedParentActiveSum_leaf_inner`: for a leaf `j`, `∑_{x} (reconstructed summand)`
  `= (remainder summand) · leafColumnSum G (η ⟨par j, _⟩) (k (succ j)) t`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **Per-labelling leaf isolation.**  For a leaf `j` of an active-closed set `A`, a
remainder labelling `η` of the active vertices of `A.erase j`, and a leaf value `x`
ranging over `allPolymers G`, the reconstructed summand
`fun a => (rootedParentActiveSplitEquiv hleaf.1 a).elim x η` summed over `x` factors as
the remainder summand (the summand of `rootedParentActiveSum` for `A.erase j` at `η`)
times the leaf column sum at the remainder value `η ⟨par j, _⟩` assigned to the
leaf's parent vertex.  The leaf value
contributes its own constraint and weight factor (collected into `leafColumnSum`); the
remaining constraints and weights pass through to the remainder. -/
theorem rootedParentActiveSum_leaf_inner (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {par : Fin n → Fin (n + 1)} {A : Finset (Fin n)} {j : Fin n}
    (hclosed : RootedParentActiveClosed par A) (hleaf : RootedParentLeaf par A j)
    (k : Fin (n + 1) → ℕ) (t : ℝ) (η : RootedParentActive (A.erase j) → Finset (Sym2 ι)) :
    (∑ x ∈ allPolymers G,
        (if ∀ i, ∀ hi : i ∈ A,
            PolymersIncompatible
              ((rootedParentActiveSplitEquiv hleaf.1 (rootedParentActiveChild hi)).elim x η)
              ((rootedParentActiveSplitEquiv hleaf.1
                (rootedParentActiveParent hclosed hi)).elim x η) then
          ∏ v : RootedParentActive A,
            (((rootedParentActiveSplitEquiv hleaf.1 v).elim x η).card : ℝ) ^ k v.1
              * (Real.exp 1 * |t|) ^ ((rootedParentActiveSplitEquiv hleaf.1 v).elim x η).card
        else 0))
      = (if ∀ i, ∀ hi : i ∈ A.erase j,
            PolymersIncompatible (η (rootedParentActiveChild hi))
              (η (rootedParentActiveParent (hclosed.erase_leaf hleaf) hi)) then
          ∏ w : RootedParentActive (A.erase j),
            ((η w).card : ℝ) ^ k w.1 * (Real.exp 1 * |t|) ^ (η w).card
        else 0)
        * leafColumnSum G (η ⟨par j, hleaf.parent_mem_erase hclosed⟩) (k (Fin.succ j)) t := by
  classical
  set hj : j ∈ A := hleaf.1 with hhj
  set hclosed' : RootedParentActiveClosed par (A.erase j) := hclosed.erase_leaf hleaf with hhc'
  set q : ℝ := Real.exp 1 * |t| with hq
  set P : Finset (Sym2 ι) := η ⟨par j, hleaf.parent_mem_erase hclosed⟩ with hP
  set leafW : Finset (Sym2 ι) → ℝ :=
    fun x => (x.card : ℝ) ^ k (Fin.succ j) * q ^ x.card with hleafW
  set Prest : ℝ :=
    ∏ w : RootedParentActive (A.erase j), ((η w).card : ℝ) ^ k w.1 * q ^ (η w).card with hPrest
  set Cleaf : Finset (Sym2 ι) → Prop := fun x => PolymersIncompatible x P with hCleaf
  set Crest : Prop :=
    ∀ i, ∀ hi : i ∈ A.erase j,
      PolymersIncompatible (η (rootedParentActiveChild hi))
        (η (rootedParentActiveParent hclosed' hi)) with hCrest
  set recon : Finset (Sym2 ι) → RootedParentActive A → Finset (Sym2 ι) :=
    fun x a => (rootedParentActiveSplitEquiv hj a).elim x η with hrecon
  -- The product factors as the leaf weight times the remainder product.
  have hprod : ∀ x : Finset (Sym2 ι),
      (∏ v : RootedParentActive A,
        ((recon x v).card : ℝ) ^ k v.1 * q ^ (recon x v).card) = leafW x * Prest := by
    intro x
    rw [prod_rootedParentActive_eq_mul hj
      (fun v => ((recon x v).card : ℝ) ^ k v.1 * q ^ (recon x v).card)]
    congr 1
    · simp [hrecon, hleafW, rootedParentActiveSplitEquiv_recon_child]
    · refine Finset.prod_congr rfl fun w _ => ?_
      simp [hrecon, rootedParentActiveSplitEquiv_symm_some_coe, Equiv.apply_symm_apply]
  -- The constraint factors as the leaf constraint and the remainder constraints.
  have hcond : ∀ x : Finset (Sym2 ι),
      (∀ i, ∀ hi : i ∈ A,
        PolymersIncompatible (recon x (rootedParentActiveChild hi))
          (recon x (rootedParentActiveParent hclosed hi)))
        ↔ Cleaf x ∧ Crest := by
    intro x
    rw [forall_mem_constraint_iff_erase hclosed hj (recon x)]
    refine and_congr ?_ ?_
    · have hp : ((rootedParentActiveParent hclosed hj : RootedParentActive A) : Fin (n + 1))
          ∈ rootedParentActiveVertices (A.erase j) := by
        simpa [rootedParentActiveParent_coe] using hleaf.parent_mem_erase hclosed
      simp only [hrecon, hCleaf, rootedParentActiveSplitEquiv_recon_child]
      rw [rootedParentActiveSplitEquiv_recon_some hj x η hp,
        show (η ⟨(rootedParentActiveParent hclosed hj : RootedParentActive A), hp⟩
            : Finset (Sym2 ι)) = P from congrArg η (Subtype.ext rfl)]
    · refine forall_congr' fun i => forall_congr' fun hi => ?_
      have hc : ((rootedParentActiveChild (Finset.mem_of_mem_erase hi) : RootedParentActive A)
          : Fin (n + 1)) ∈ rootedParentActiveVertices (A.erase j) := by
        simpa [rootedParentActiveChild_coe] using succ_mem_rootedParentActiveVertices.mpr hi
      have hp : ((rootedParentActiveParent hclosed (Finset.mem_of_mem_erase hi)
          : RootedParentActive A) : Fin (n + 1))
          ∈ rootedParentActiveVertices (A.erase j) := by
        simpa [rootedParentActiveParent_coe] using hclosed' i hi
      simp only [hrecon]
      rw [rootedParentActiveSplitEquiv_recon_some hj x η hc,
        rootedParentActiveSplitEquiv_recon_some hj x η hp,
        show (η ⟨(rootedParentActiveChild (Finset.mem_of_mem_erase hi) : RootedParentActive A), hc⟩
            : Finset (Sym2 ι)) = η (rootedParentActiveChild hi) from congrArg η (Subtype.ext rfl),
        show (η ⟨(rootedParentActiveParent hclosed (Finset.mem_of_mem_erase hi)
              : RootedParentActive A), hp⟩ : Finset (Sym2 ι))
            = η (rootedParentActiveParent hclosed' hi) from congrArg η (Subtype.ext rfl)]
  -- Per-leaf-value summand factoring.
  have hsummand : ∀ x : Finset (Sym2 ι),
      (if ∀ i, ∀ hi : i ∈ A,
          PolymersIncompatible (recon x (rootedParentActiveChild hi))
            (recon x (rootedParentActiveParent hclosed hi)) then
        ∏ v : RootedParentActive A,
          ((recon x v).card : ℝ) ^ k v.1 * q ^ (recon x v).card else 0)
        = (if Crest then Prest else 0) * (if Cleaf x then leafW x else 0) := by
    intro x
    rw [if_congr (hcond x) rfl rfl, hprod x]
    by_cases hC : Crest <;> by_cases hL : Cleaf x <;>
      simp [hC, hL, mul_comm]
  calc
    (∑ x ∈ allPolymers G,
        (if ∀ i, ∀ hi : i ∈ A,
            PolymersIncompatible (recon x (rootedParentActiveChild hi))
              (recon x (rootedParentActiveParent hclosed hi)) then
          ∏ v : RootedParentActive A,
            ((recon x v).card : ℝ) ^ k v.1 * q ^ (recon x v).card else 0))
        = ∑ x ∈ allPolymers G,
            (if Crest then Prest else 0) * (if Cleaf x then leafW x else 0) :=
          Finset.sum_congr rfl fun x _ => hsummand x
    _ = (if Crest then Prest else 0)
          * ∑ x ∈ allPolymers G, (if Cleaf x then leafW x else 0) := by
        rw [Finset.mul_sum]
    _ = (if Crest then Prest else 0) * leafColumnSum G P (k (Fin.succ j)) t := by
        rfl

end IsingModel
