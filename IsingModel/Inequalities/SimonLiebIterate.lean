import IsingModel.Inequalities.SimonLiebKernel

/-!
# Iterated Simon-Lieb transfer kernel (FFS Ch 12 / GJ §18)

The one-step neighbour-vertex Simon-Lieb inequality
(`correlation_inducedGraph_simon_lieb_neighbor`) bounds a two-point correlation
by `β J` times a sum of the transfer kernel `K(j, ·)` over the neighbours of one
endpoint.  Iterating this `n` times produces the **iterated Simon-Lieb kernel**

  `simonLiebIterate p j 0 i = K(j, i)`,
  `simonLiebIterate p j (n+1) i = if i = j then 1
      else β J · ∑_{u ∼ i} simonLiebIterate p j n u`,

the `n`-step transfer applied to the kernel, with the diagonal value `K(j, j) = 1`
absorbed at the target `j` (a walk reaching `j` stops, contributing the
`⟨σ_∅⟩ = 1` factor).  The key estimate is the uniform upper bound

  `K(j, i) ≤ simonLiebIterate p j n i`   for all `n, i`,

which for `i ≠ j` reads `⟨σ_i σ_j⟩ ≤ simonLiebIterate p j n i`.  This is the
iteration mechanism of the random-walk representation; a later PR connects the
iterated bound to the walk sum (`walkSum`) and the high-temperature exponential
decay.

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

/-- The **`n`-times iterated Simon-Lieb transfer kernel**: the one-step
neighbour-vertex transfer applied `n` times to the kernel `K(j, ·)`.  The base is
the kernel itself; each step transfers `β J · ∑_{u ∼ i} (·)`, with the diagonal
`i = j` absorbing to the value `1`. -/
noncomputable def simonLiebIterate (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    (p : IsingParams ℝ) (j : ↑Λ) : ℕ → ↑Λ → ℝ
  | 0 => fun i => simonLiebKernel G Λ p j i
  | (n + 1) => fun i =>
      if i = j then 1
      else p.β * p.J *
        ∑ u ∈ (inducedGraph G Λ).neighborFinset i, simonLiebIterate G Λ p j n u

omit [DecidableEq V] in
/-- Unfolding at `0`: the iterated kernel starts at the kernel itself. -/
theorem simonLiebIterate_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    (p : IsingParams ℝ) (j i : ↑Λ) :
    simonLiebIterate G Λ p j 0 i = simonLiebKernel G Λ p j i := rfl

omit [DecidableEq V] in
/-- Unfolding at `n+1`: the one-step neighbour transfer, with the diagonal
absorbed to `1`. -/
theorem simonLiebIterate_succ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    (p : IsingParams ℝ) (j i : ↑Λ) (n : ℕ) :
    simonLiebIterate G Λ p j (n + 1) i
      = if i = j then 1
        else p.β * p.J *
          ∑ u ∈ (inducedGraph G Λ).neighborFinset i, simonLiebIterate G Λ p j n u := rfl

set_option linter.unusedDecidableInType false in
/-- **Iterated Simon-Lieb upper bound** (FFS Ch 12 / GJ §18): for ferromagnetic
`⟨J,0,β⟩` and every `n, i`,

`K(j, i) ≤ simonLiebIterate ⟨J,0,β⟩ j n i`.

The proof is induction on `n`: the base is reflexivity; for `i = j` both sides are
`1`; for `i ≠ j` the one-step kernel `⟨σ_i σ_j⟩ ≤ β J ∑_{u ∼ i} K(j, u)` is
combined with the induction hypothesis `K(j, u) ≤ simonLiebIterate … n u` (using
`β J ≥ 0`). -/
theorem simonLiebKernel_le_simonLiebIterate (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) (j : ↑Λ) (n : ℕ) (i : ↑Λ) :
    simonLiebKernel G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j i
      ≤ simonLiebIterate G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j n i := by
  have hβJ : 0 ≤ β * J := mul_nonneg hf.hβ.le hf.hJ
  induction n generalizing i with
  | zero => rw [simonLiebIterate_zero]
  | succ n ih =>
    rw [simonLiebIterate_succ]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, simonLiebKernel_self]
    · rw [if_neg hij, simonLiebKernel_of_ne G Λ _ hij]
      calc correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
          ≤ β * J * ∑ u ∈ (inducedGraph G Λ).neighborFinset i,
              simonLiebKernel G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j u :=
            correlation_inducedGraph_simon_lieb_neighbor G Λ hf hij
        _ ≤ β * J * ∑ u ∈ (inducedGraph G Λ).neighborFinset i,
              simonLiebIterate G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j n u :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ih u) hβJ

set_option linter.unusedDecidableInType false in
/-- **Two-point corollary**: for distinct `i ≠ j`,
`⟨σ_i σ_j⟩ ≤ simonLiebIterate ⟨J,0,β⟩ j n i`. -/
theorem correlation_inducedGraph_le_simonLiebIterate (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) {i j : ↑Λ} (hij : i ≠ j)
    (n : ℕ) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ simonLiebIterate G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j n i := by
  have h := simonLiebKernel_le_simonLiebIterate G Λ hf j n i
  rwa [simonLiebKernel_of_ne G Λ _ hij] at h

end Ambient

end IsingModel
