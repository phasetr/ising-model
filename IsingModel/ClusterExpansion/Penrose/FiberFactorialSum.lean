import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Central

/-!
# The parent-function fiber-factorial sum equals a rising factorial (GJ §18.5)

The Prüfer-free cluster-expansion closing relaxes the sum of child-count factorials over
spanning trees to the sum over *all* parent functions `Fin n → Fin m` of the product of
fiber-size factorials (that relaxation is `ParentCodeFactorialSum.lean`, #4124).  This
file evaluates the parent-function sum in closed form:

`∑_{p : Fin n → Fin m} ∏_v (#{i | p i = v})! = ascFactorial m n = m·(m+1)···(m+n-1)`.

The proof is an induction on `n`: a function `Fin (n+1) → Fin m` splits (via
`Fin.snocEquiv`) into a last value `a` and an initial tuple `p'`, the fiber at `v` gains
`+1` iff `v = a`, the product picks up a factor `fiber(a) + 1`, and summing over `a`
multiplies by `∑_a (fiber(a) + 1) = n + m`, matching `ascFactorial_succ`.

Specialising to `m = n + 1` gives `(2n)!/n! = n!·\binom{2n}{n} ≤ 4^n·n!`
(`Nat.factorial_mul_ascFactorial`, `Nat.centralBinom_le_four_pow`).

* `parentFiberFactorialSum_eq_ascFactorial`.
* `parentFiberFactorialSum_succ_le_four_pow_mul_factorial`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

/-- The fiber size of a function `p : Fin n → Fin m` at `v`: `#{i | p i = v}`. -/
def fiberCount (n m : ℕ) (p : Fin n → Fin m) (v : Fin m) : ℕ :=
  (Finset.univ.filter fun i => p i = v).card

/-- **Fiber recurrence under `Fin.snoc`.**  Appending a value `a` to the tuple adds one
to the fiber at `v` iff `a = v`. -/
theorem fiberCount_snoc (n m : ℕ) (p : Fin n → Fin m) (a v : Fin m) :
    fiberCount (n + 1) m (Fin.snoc p a) v
      = fiberCount n m p v + (if a = v then 1 else 0) := by
  classical
  unfold fiberCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, eq_comm]

/-- **The fiber sizes of `p : Fin n → Fin m` sum to `n`.** -/
theorem sum_fiberCount (n m : ℕ) (p : Fin n → Fin m) :
    (∑ v : Fin m, fiberCount n m p v) = n := by
  classical
  unfold fiberCount
  rw [← Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin m))) (f := p) (fun i _ => by simp)]
  simp

/-- **Product factorisation under `Fin.snoc`.**  The product of fiber factorials over the
appended tuple is `(fiber(a) + 1)` times the original product. -/
theorem prod_fiberCount_factorial_snoc (n m : ℕ) (p : Fin n → Fin m) (a : Fin m) :
    (∏ v : Fin m, (fiberCount (n + 1) m (Fin.snoc p a) v).factorial)
      = (fiberCount n m p a + 1) * ∏ v : Fin m, (fiberCount n m p v).factorial := by
  classical
  simp_rw [fiberCount_snoc]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun v : Fin m => (fiberCount n m p v + if a = v then 1 else 0).factorial)
    (Finset.mem_univ a),
    ← Finset.mul_prod_erase Finset.univ
    (fun v : Fin m => (fiberCount n m p v).factorial) (Finset.mem_univ a)]
  have hrest : ∏ x ∈ Finset.univ.erase a,
      (fiberCount n m p x + if a = x then 1 else 0).factorial
      = ∏ x ∈ Finset.univ.erase a, (fiberCount n m p x).factorial := by
    refine Finset.prod_congr rfl fun v hv => ?_
    have hav : a ≠ v := by simpa [Finset.mem_erase, eq_comm] using hv
    simp [hav]
  rw [hrest]
  simp [Nat.factorial_succ, mul_assoc]

/-- **The parent-function fiber-factorial sum.**  `∑_{p : Fin n → Fin m} ∏_v (fiber)!`. -/
def parentFiberFactorialSum (n m : ℕ) : ℕ :=
  ∑ p : Fin n → Fin m, ∏ v : Fin m, (fiberCount n m p v).factorial

/-- **The parent-function fiber-factorial sum is a rising factorial.**
`∑_{p : Fin n → Fin m} ∏_v (#{i | p i = v})! = ascFactorial m n`.  By induction on `n`
via `Fin.snocEquiv`: appending a value multiplies the sum by `n + m`. -/
theorem parentFiberFactorialSum_eq_ascFactorial (n m : ℕ) :
    parentFiberFactorialSum n m = m.ascFactorial n := by
  classical
  induction n with
  | zero =>
    have hone : ∀ p : Fin 0 → Fin m,
        (∏ v : Fin m, (fiberCount 0 m p v).factorial) = 1 := by
      intro p
      refine Finset.prod_eq_one fun v _ => ?_
      simp [fiberCount]
    simp [parentFiberFactorialSum, Nat.ascFactorial_zero, hone]
  | succ n ih =>
    rw [parentFiberFactorialSum, Nat.ascFactorial_succ, ← ih, parentFiberFactorialSum]
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin m)).sum_comp
      (fun p => ∏ v : Fin m, (fiberCount (n + 1) m p v).factorial),
      Fintype.sum_prod_type]
    -- ∑_a ∑_{p'} ∏_v (fiber (snoc p' a))! = ∑_a ∑_{p'} (fiber p' a + 1)·∏_v (fiber p')!
    have hsnoc : ∀ (a : Fin m) (p : Fin n → Fin m),
        (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin m)) (a, p) = Fin.snoc p a := fun _ _ => rfl
    have hbody : ∀ a : Fin m, ∀ p : Fin n → Fin m,
        (∏ v : Fin m, (fiberCount (n + 1) m (Fin.snoc p a) v).factorial)
          = (fiberCount n m p a + 1) * ∏ v : Fin m, (fiberCount n m p v).factorial :=
      fun a p => prod_fiberCount_factorial_snoc n m p a
    simp_rw [hsnoc, hbody]
    rw [Finset.sum_comm]
    -- ∑_{p'} ∑_a (fiber p' a + 1)·∏_v(...) = ∑_{p'} (n+m)·∏_v(...)
    have hinner : ∀ p : Fin n → Fin m,
        (∑ a : Fin m, (fiberCount n m p a + 1) * ∏ v : Fin m, (fiberCount n m p v).factorial)
          = (n + m) * ∏ v : Fin m, (fiberCount n m p v).factorial := by
      intro p
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_add_distrib, sum_fiberCount, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
    simp_rw [hinner]
    rw [← Finset.mul_sum, Nat.add_comm n m]

/-- **The `m = n + 1` parent-function fiber-factorial sum is `≤ 4^n·n!`.**
`∑_{p : Fin n → Fin (n+1)} ∏_v (#{i | p i = v})! = (2n)!/n! = n!·\binom{2n}{n} ≤ 4^n·n!`.
-/
theorem parentFiberFactorialSum_succ_le_four_pow_mul_factorial (n : ℕ) :
    parentFiberFactorialSum n (n + 1) ≤ 4 ^ n * n.factorial := by
  rw [parentFiberFactorialSum_eq_ascFactorial]
  -- (n+1).ascFactorial n = centralBinom n · n!, since
  -- n!·(n+1).ascFactorial n = (2n)! = centralBinom n·n!·n!.
  have hasc : (n + 1).ascFactorial n = n.centralBinom * n.factorial := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos n) ?_
    rw [Nat.factorial_mul_ascFactorial]
    have hcmf : n.centralBinom * n.factorial * n.factorial = (n + n).factorial := by
      rw [Nat.centralBinom_eq_two_mul_choose, show n + n = 2 * n by omega]
      have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
      rw [show 2 * n - n = n by omega] at h
      exact h
    rw [← hcmf]; ring
  rw [hasc]
  exact Nat.mul_le_mul_right _ (Nat.centralBinom_le_four_pow n)

end IsingModel
