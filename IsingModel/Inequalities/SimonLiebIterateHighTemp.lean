import IsingModel.Inequalities.SimonLiebIterate

/-!
# High-temperature uniform bound on the iterated Simon-Lieb kernel (FFS Ch 12 / GJ §18)

In the high-temperature regime `β J · D ≤ 1` (with `D` an upper bound on the
vertex degree) the iterated Simon-Lieb transfer kernel
(`simonLiebIterate`, the `n`-step transfer applied to the kernel `K(j, ·)`) stays
uniformly bounded by `1`:

  `simonLiebIterate ⟨J,0,β⟩ j n i ≤ 1`   for all `n, i`.

This is the boundedness input for the random-walk representation: the iterated
upper bound for `⟨σ_i σ_j⟩` does not blow up as the number of transfer steps
grows, which is the prerequisite for passing to the first-passage walk-sum limit.
Combined with `simonLiebKernel_le_simonLiebIterate` it gives the high-temperature
two-point bound `⟨σ_i σ_j⟩ ≤ 1` along the Simon-Lieb iteration.

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
/-- **High-temperature uniform bound on the iterated kernel** (FFS Ch 12 / GJ §18):
if every vertex has at most `D` neighbours and `β J · D ≤ 1` (high temperature),
then `simonLiebIterate ⟨J,0,β⟩ j n i ≤ 1` for all `n, i`.

Induction on `n`: the base is the kernel bound `K(j, i) ≤ 1`; for `i = j` the
value is exactly `1`; for `i ≠ j` the one-step transfer is
`β J ∑_{u ∼ i} simonLiebIterate … n u ≤ β J · D · 1 ≤ 1` using the induction
hypothesis, `β J ≥ 0`, the degree bound, and `β J · D ≤ 1`. -/
theorem simonLiebIterate_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    {D : ℕ} (hD : ∀ v : ↑Λ, ((inducedGraph G Λ).neighborFinset v).card ≤ D)
    (hβJD : β * J * (D : ℝ) ≤ 1) (j : ↑Λ) (n : ℕ) (i : ↑Λ) :
    simonLiebIterate G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j n i ≤ 1 := by
  have hβJ : 0 ≤ β * J := mul_nonneg hf.hβ.le hf.hJ
  induction n generalizing i with
  | zero =>
    rw [simonLiebIterate_zero]
    exact simonLiebKernel_le_one G Λ _ j i
  | succ n ih =>
    rw [simonLiebIterate_succ]
    by_cases hij : i = j
    · exact (if_pos hij).le
    · rw [if_neg hij]
      calc β * J * ∑ u ∈ (inducedGraph G Λ).neighborFinset i,
              simonLiebIterate G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j n u
          ≤ β * J * ∑ _u ∈ (inducedGraph G Λ).neighborFinset i, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ih u) hβJ
        _ = β * J * ((inducedGraph G Λ).neighborFinset i).card := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ β * J * (D : ℝ) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hD i) hβJ
        _ ≤ 1 := hβJD

set_option linter.unusedDecidableInType false in
/-- **High-temperature two-point bound via the Simon-Lieb iteration** (FFS Ch 12 /
GJ §18): for distinct `i ≠ j`, the high-temperature uniform iterate bound gives
`⟨σ_i σ_j⟩ ≤ 1` along the Simon-Lieb iteration (composing
`correlation_inducedGraph_le_simonLiebIterate` with `simonLiebIterate_le_one`). -/
theorem correlation_inducedGraph_le_one_of_high_temp (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    {D : ℕ} (hD : ∀ v : ↑Λ, ((inducedGraph G Λ).neighborFinset v).card ≤ D)
    (hβJD : β * J * (D : ℝ) ≤ 1) {i j : ↑Λ} (hij : i ≠ j) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} ≤ 1 :=
  le_trans (correlation_inducedGraph_le_simonLiebIterate G Λ hf hij 0)
    (simonLiebIterate_le_one G Λ hf hD hβJD j 0 i)

end Ambient

end IsingModel
