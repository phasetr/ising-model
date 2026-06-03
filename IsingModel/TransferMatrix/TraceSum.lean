import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Closed-walk trace identity for matrix powers (GJ §17.1 transfer-matrix `Z_N = Tr Tᴺ`)

The transfer-matrix method of Glimm–Jaffe §17.1 expresses the partition function
of the cyclic `N`-site chain as a matrix trace, `Z_N = Tr(Tᴺ)`.  The combinatorial
core, valid for any finite matrix `M : Matrix ι ι R` over a commutative semiring, is
the **closed-walk trace identity**, proved here in the open-path return-to-start form

  `Tr(Mⁿ) = ∑_{σ : Fin (n+1) → ι, σ 0 = σ (last n)} pathWeight M σ`   (`trace_pow_eq_sum`),

where `pathWeight M σ = ∏_{i : Fin n} M (σ i.castSucc) (σ i.succ)` is the product of
edge weights along the path `σ`.  Mathlib has no such lemma (only
`adjMatrix_pow_apply_eq_card_walk` for `0/1` matrices), so it is proved from the
open-path entry formula

  `(Mⁿ) a b = ∑_{σ : Fin (n+1) → ι, σ 0 = a, σ last = b} pathWeight M σ`   (`pow_apply_eq_sum`),

obtained by induction peeling the last edge with `Fin.snoc`, then specialised to the
diagonal (`b = a`) and summed.  The genuinely cyclic weight
`closedWalkWeight M σ = ∏_{i : Fin n} M (σ i) (σ (i+1))` (cyclic `i+1` in `Fin n`) is
given with its factorization `closedWalkWeight_succ` into `pathWeight` times the
wrap-around edge; the reindexing of `trace_pow_eq_sum` into this purely cyclic
`∑_{σ : Fin N → ι} closedWalkWeight M σ` form is left for a subsequent step.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators
open Matrix Fin

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- The **open-path weight** of a vertex sequence `σ : Fin (n+1) → ι`: the product
of the matrix entries over its `n` consecutive edges,
`∏_{i : Fin n} M (σ i.castSucc) (σ i.succ)`. -/
def pathWeight (M : Matrix ι ι R) {n : ℕ} (σ : Fin (n + 1) → ι) : R :=
  ∏ i : Fin n, M (σ i.castSucc) (σ i.succ)

omit [Fintype ι] [DecidableEq ι] in
/-- Appending a vertex `x` to a path multiplies its weight by the new final edge:
`pathWeight M (snoc σ x) = pathWeight M σ · M (σ (last n)) x`. -/
theorem pathWeight_snoc (M : Matrix ι ι R) {n : ℕ} (σ : Fin (n + 1) → ι) (x : ι) :
    pathWeight M (Fin.snoc σ x) = pathWeight M σ * M (σ (Fin.last n)) x := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
  · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

/-- **Open-path entry formula**: the `(a, b)` entry of `Mⁿ` is the sum over all
vertex sequences `σ : Fin (n+1) → ι` with `σ 0 = a` and `σ (last n) = b` of the
open-path weight, by induction on `n` peeling the last edge. -/
theorem pow_apply_eq_sum (M : Matrix ι ι R) (n : ℕ) (a b : ι) :
    (M ^ n) a b
      = ∑ σ : Fin (n + 1) → ι,
          if σ 0 = a ∧ σ (Fin.last n) = b then pathWeight M σ else 0 := by
  induction n generalizing b with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι)
        (fun σ : Fin 1 → ι => if σ 0 = a ∧ σ (Fin.last 0) = b then pathWeight M σ else 0)
        (fun v : ι => if v = a ∧ v = b then (1 : R) else 0)]
    · by_cases hab : a = b
      · subst hab; simp
      · rw [if_neg hab, eq_comm]
        exact Finset.sum_eq_zero
          (fun v _ => if_neg (by rintro ⟨rfl, rfl⟩; exact hab rfl))
    · intro σ
      simp [pathWeight, Fin.last_zero, Equiv.funUnique_apply]
  | succ n ih =>
    have hL : (M ^ (n + 1)) a b
        = ∑ σ : Fin (n + 1) → ι,
            if σ 0 = a then pathWeight M σ * M (σ (Fin.last n)) b else 0 := by
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [ih, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      by_cases h0 : σ 0 = a
      · simp only [h0, true_and]
        rw [Finset.sum_eq_single (σ (Fin.last n))]
        · simp
        · intro c _ hc; rw [if_neg (by exact fun h => hc h.symm), zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp only [h0, false_and, if_false, zero_mul, Finset.sum_const_zero]
    have hR : (∑ τ : Fin (n + 1 + 1) → ι,
          if τ 0 = a ∧ τ (Fin.last (n + 1)) = b then pathWeight M τ else 0)
        = ∑ σ : Fin (n + 1) → ι,
            if σ 0 = a then pathWeight M σ * M (σ (Fin.last n)) b else 0 := by
      rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1 + 1) => ι)),
        Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
      rw [Finset.sum_eq_single b]
      · have h0 : (Fin.snoc σ b : Fin (n + 1 + 1) → ι) 0 = σ 0 := by
          rw [← Fin.castSucc_zero, Fin.snoc_castSucc]
        rw [h0, Fin.snoc_last, pathWeight_snoc]
        simp
      · intro x _ hx
        rw [Fin.snoc_last, if_neg]
        rintro ⟨_, rfl⟩; exact hx rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hL, hR]

/-- **Trace of a matrix power as a sum over closed walks** (the open-path form):
`Tr(Mⁿ) = ∑_{σ : Fin (n+1) → ι, σ 0 = σ (last n)} pathWeight M σ`, a sum over
vertex sequences whose endpoint returns to the start.  Obtained from
`pow_apply_eq_sum` on the diagonal (`b = a`), summed over `a`. -/
theorem trace_pow_eq_sum (M : Matrix ι ι R) (n : ℕ) :
    (M ^ n).trace
      = ∑ σ : Fin (n + 1) → ι, if σ 0 = σ (Fin.last n) then pathWeight M σ else 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, pow_apply_eq_sum M n]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  by_cases h : σ 0 = σ (Fin.last n)
  · rw [if_pos h, Finset.sum_eq_single (σ 0)]
    · rw [if_pos ⟨rfl, h.symm⟩]
    · intro a _ ha; rw [if_neg]; rintro ⟨rfl, _⟩; exact ha rfl
    · intro hni; exact absurd (Finset.mem_univ _) hni
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [if_neg]; rintro ⟨rfl, h2⟩; exact h h2.symm

/-- The **closed-walk weight** of a cyclic vertex sequence `σ : Fin n → ι`: the
product of the matrix entries over its `n` cyclic edges,
`∏_{i : Fin n} M (σ i) (σ (i + 1))` with `i + 1` taken cyclically in `Fin n`. -/
def closedWalkWeight (M : Matrix ι ι R) {n : ℕ} [NeZero n] (σ : Fin n → ι) : R :=
  ∏ i : Fin n, M (σ i) (σ (i + 1))

omit [Fintype ι] [DecidableEq ι] in
/-- The cyclic closed-walk weight factors as the open-path weight times the
wrap-around edge: `closedWalkWeight M τ = pathWeight M τ · M (τ (last m)) (τ 0)`. -/
theorem closedWalkWeight_succ (M : Matrix ι ι R) {m : ℕ} (τ : Fin (m + 1) → ι) :
    closedWalkWeight M τ = pathWeight M τ * M (τ (Fin.last m)) (τ 0) := by
  unfold closedWalkWeight pathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    have hi : (Fin.castSucc i + 1 : Fin (m + 1)) = i.succ := by
      ext; rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last i), Fin.val_succ, Fin.val_castSucc]
    rw [hi]
  · have hl : (Fin.last m + 1 : Fin (m + 1)) = 0 := by
      ext; rw [Fin.val_add_one, if_pos rfl]; rfl
    rw [hl]

end TransferMatrix

end IsingModel
