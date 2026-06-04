import IsingModel.Inequalities.SimonLiebIterate
import IsingModel.Inequalities.WalkSum

/-!
# Walk-sum representation of the two-point function (FFS Ch 12 / GJ §18)

The iterated Simon-Lieb kernel (`simonLiebIterate`) is dominated by the
**walk sum** plus a geometric remainder: for every `n`,

  `simonLiebIterate ⟨J,0,β⟩ j n i
     ≤ ∑_{k=0}^{n} walkSum (β J) i j k + (β J · D)^n`,

with `D` a vertex-degree bound.  The diagonal value `K(j, j) = 1` is exactly the
length-`0` walk `walkSum 0 j j = 1`, and the one-step transfer matches the walk
recurrence `walkSum_succ`, so the iterate is bounded by the partial walk sum and a
remainder controlled by the high-temperature factor `β J · D`.  For `i ≠ j` the
length-`0` walk vanishes, giving the **walk-sum bound on the correlation**

  `⟨σ_i σ_j⟩ ≤ ∑_{k=1}^{n} walkSum (β J) i j k + (β J · D)^n`,

the finite-horizon form of the random-walk representation
`⟨σ_i σ_j⟩ ≤ ∑_{k≥1} walkSum (β J) i j k` (the remainder vanishing for
`β J · D < 1` is the next PR).

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Ch 12.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel

open Finset

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **The iterated kernel is `1` on the diagonal**: `simonLiebIterate p j n j = 1`
for all `n` (the kernel value `K(j, j) = 1`, preserved by the diagonal-absorbing
step). -/
theorem simonLiebIterate_self (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    (p : IsingParams ℝ) (j : ↑Λ) (n : ℕ) :
    simonLiebIterate G Λ p j n j = 1 := by
  cases n with
  | zero => rw [simonLiebIterate_zero, simonLiebKernel_self]
  | succ n => rw [simonLiebIterate_succ, if_pos rfl]

omit [DecidableEq V] in
/-- **Walk-sum domination of the iterated kernel** (FFS Ch 12 / GJ §18): for every
`n` and `i`,

`simonLiebIterate ⟨J,0,β⟩ j n i ≤ ∑_{k=0}^{n} walkSum (β J) i j k + (β J · D)^n`,

with `D` a vertex-degree bound.  Induction on `n` (uniform in `i`): the base uses
`K(j, i) ≤ 1`; for `i = j` the length-`0` walk `walkSum 0 j j = 1` already
dominates the value `1`; for `i ≠ j` the one-step transfer, the induction
hypothesis at every neighbour, the walk recurrence `walkSum_succ`, and the degree
bound assemble the partial walk sum and the geometric remainder. -/
theorem simonLiebIterate_le_sum_walkSum_add_pow (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    {D : ℕ} (hD : ∀ v : ↑Λ, ((inducedGraph G Λ).neighborFinset v).card ≤ D)
    (j : ↑Λ) (n : ℕ) (i : ↑Λ) :
    simonLiebIterate G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j n i
      ≤ (∑ k ∈ Finset.range (n + 1),
          walkSum (inducedGraph G Λ) (β * J) i j k) + (β * J * (D : ℝ)) ^ n := by
  have hβJ : 0 ≤ β * J := mul_nonneg hf.hβ.le hf.hJ
  have hβJD : 0 ≤ β * J * (D : ℝ) := mul_nonneg hβJ (Nat.cast_nonneg D)
  induction n generalizing i with
  | zero =>
    rw [simonLiebIterate_zero, Finset.sum_range_one, pow_zero]
    have h1 : simonLiebKernel G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j i ≤ 1 :=
      simonLiebKernel_le_one G Λ _ j i
    have h2 : 0 ≤ walkSum (inducedGraph G Λ) (β * J) i j 0 :=
      walkSum_nonneg (inducedGraph G Λ) hβJ i j 0
    linarith
  | succ n ih =>
    by_cases hij : i = j
    · subst hij
      rw [simonLiebIterate_succ, if_pos rfl]
      have hw0 : walkSum (inducedGraph G Λ) (β * J) i i 0 = 1 := by
        rw [walkSum_zero]; simp
      have hmem : (0 : ℕ) ∈ Finset.range (n + 2) := by simp
      have hsum_ge : (1 : ℝ) ≤ ∑ k ∈ Finset.range (n + 2),
          walkSum (inducedGraph G Λ) (β * J) i i k := by
        rw [← hw0]
        exact Finset.single_le_sum
          (fun k _ => walkSum_nonneg (inducedGraph G Λ) hβJ i i k) hmem
      have hrem : 0 ≤ (β * J * (D : ℝ)) ^ (n + 1) := pow_nonneg hβJD _
      linarith
    · rw [simonLiebIterate_succ, if_neg hij]
      have hw0 : walkSum (inducedGraph G Λ) (β * J) i j 0 = 0 := by
        rw [walkSum_zero, if_neg hij]
      -- swap-and-fold of the neighbour double sum into the shifted walk sum
      have hpart1 : β * J * ∑ u ∈ (inducedGraph G Λ).neighborFinset i,
            ∑ k ∈ Finset.range (n + 1), walkSum (inducedGraph G Λ) (β * J) u j k
          = ∑ k ∈ Finset.range (n + 1),
              walkSum (inducedGraph G Λ) (β * J) i j (k + 1) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [walkSum_succ]
      have hshift : ∑ k ∈ Finset.range (n + 1),
            walkSum (inducedGraph G Λ) (β * J) i j (k + 1)
          ≤ ∑ k ∈ Finset.range (n + 2),
              walkSum (inducedGraph G Λ) (β * J) i j k := by
        rw [Finset.sum_range_succ' (fun k => walkSum (inducedGraph G Λ) (β * J) i j k) (n + 1)]
        have : 0 ≤ walkSum (inducedGraph G Λ) (β * J) i j 0 :=
          walkSum_nonneg (inducedGraph G Λ) hβJ i j 0
        linarith
      have hrem : β * J * ∑ _u ∈ (inducedGraph G Λ).neighborFinset i, (β * J * (D : ℝ)) ^ n
          ≤ (β * J * (D : ℝ)) ^ (n + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        calc β * J * (((inducedGraph G Λ).neighborFinset i).card * (β * J * (D : ℝ)) ^ n)
            ≤ β * J * ((D : ℝ) * (β * J * (D : ℝ)) ^ n) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (by exact_mod_cast hD i) (pow_nonneg hβJD n)) hβJ
          _ = (β * J * (D : ℝ)) ^ (n + 1) := by rw [pow_succ]; ring
      calc β * J * ∑ u ∈ (inducedGraph G Λ).neighborFinset i,
              simonLiebIterate G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j n u
          ≤ β * J * ∑ u ∈ (inducedGraph G Λ).neighborFinset i,
              ((∑ k ∈ Finset.range (n + 1),
                  walkSum (inducedGraph G Λ) (β * J) u j k) + (β * J * (D : ℝ)) ^ n) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ih u) hβJ
        _ = (β * J * ∑ u ∈ (inducedGraph G Λ).neighborFinset i,
                ∑ k ∈ Finset.range (n + 1), walkSum (inducedGraph G Λ) (β * J) u j k)
              + β * J * ∑ _u ∈ (inducedGraph G Λ).neighborFinset i, (β * J * (D : ℝ)) ^ n := by
            rw [Finset.sum_add_distrib, mul_add]
        _ ≤ (∑ k ∈ Finset.range (n + 2), walkSum (inducedGraph G Λ) (β * J) i j k)
              + (β * J * (D : ℝ)) ^ (n + 1) := by
            rw [hpart1]; linarith [hshift, hrem]

set_option linter.unusedDecidableInType false in
/-- **Finite-horizon walk-sum bound on the correlation** (FFS Ch 12 / GJ §18): for
distinct `i ≠ j` and every `n`,

`⟨σ_i σ_j⟩ ≤ ∑_{k=1}^{n} walkSum (β J) i j k + (β J · D)^n`.

The length-`0` walk vanishes for `i ≠ j`, so the partial walk sum runs over
positive lengths.  Composes `correlation_inducedGraph_le_simonLiebIterate` with the
walk-sum domination of the iterate. -/
theorem correlation_inducedGraph_le_sum_walkSum_add_pow (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    {D : ℕ} (hD : ∀ v : ↑Λ, ((inducedGraph G Λ).neighborFinset v).card ≤ D)
    {i j : ↑Λ} (hij : i ≠ j) (n : ℕ) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ (∑ k ∈ Finset.range n,
          walkSum (inducedGraph G Λ) (β * J) i j (k + 1)) + (β * J * (D : ℝ)) ^ n := by
  have hβJ : 0 ≤ β * J := mul_nonneg hf.hβ.le hf.hJ
  have h := le_trans (correlation_inducedGraph_le_simonLiebIterate G Λ hf hij n)
    (simonLiebIterate_le_sum_walkSum_add_pow G Λ hf hD j n i)
  -- rewrite ∑_{k∈range(n+1)} walkSum k = walkSum 0 + ∑_{k∈range n} walkSum (k+1), walkSum 0 = 0
  rw [Finset.sum_range_succ' (fun k => walkSum (inducedGraph G Λ) (β * J) i j k) n,
    walkSum_zero, if_neg hij, add_zero] at h
  exact h

end Ambient

end IsingModel
