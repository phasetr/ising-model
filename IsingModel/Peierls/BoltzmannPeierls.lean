import IsingModel.Peierls.FlipSet

/-!
# Peierls argument — Boltzmann weight ratio and Peierls bound

This module is part of the split `IsingModel.Peierls` development. It
collects the Boltzmann-weight ratio under `flipSet`, the conditional
Peierls sum bound `peierls_sum_bound`, the canonical Peierls bound
`peierls_bound` (GJ Prop. 5.4.1), the axiomatized lattice contour
counting bound, and the resulting `peierls_contour_sum_le`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Boltzmann weight ratio

The ratio of Boltzmann weights under flip gives the exponential factor. -/

/-- The Boltzmann weight ratio: `w(σ) = exp(-2βJ|γ|) * w(σ^S)` when
`γ = cut(S) ⊆ ∂σ`. -/
theorem boltzmannWeight_flipSet_ratio (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (S : Finset ι) (σ : Config ι)
    (hsub : cutEdges G S ⊆ phaseBoundary G σ) :
    boltzmannWeight G ⟨J, 0, β⟩ σ =
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
        boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ) := by
  simp only [boltzmannWeight]
  rw [← Real.exp_add]
  congr 1
  have h := hamiltonian_flipSet_diff G J β S σ hsub
  have key : hamiltonian G ⟨J, 0, β⟩ σ =
      hamiltonian G ⟨J, 0, β⟩ (Config.flipSet S σ) +
        2 * J * ↑(cutEdges G S).card := by linarith
  rw [key]; ring

/-! ## Peierls bound (Proposition 5.4.1)

For any set S of sites, the probability that all cut edges of S
lie in the phase boundary is at most `exp(-2βJ|cut(S)|)`. -/

/-- **Peierls sum bound** (Glimm–Jaffe, Prop. 5.4.1). The conditional sum of
Boltzmann weights over configurations with `cut(S) ⊆ ∂σ` is at most
`exp(-2βJ|cut(S)|) * Z`. -/
theorem peierls_sum_bound (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (S : Finset ι) :
    ∑ σ : Config ι, (if cutEdges G S ⊆ phaseBoundary G σ then
        boltzmannWeight G ⟨J, 0, β⟩ σ else 0) ≤
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
        partitionFunction G ⟨J, 0, β⟩ := by
  -- Each summand ≤ exp(-2βJ|γ|) * w(σ^S)
  have hfactor : ∀ σ : Config ι,
      (if cutEdges G S ⊆ phaseBoundary G σ then
        boltzmannWeight G ⟨J, 0, β⟩ σ else 0) ≤
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
        boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ) := by
    intro σ; split
    · next hsub => exact le_of_eq (boltzmannWeight_flipSet_ratio G J β S σ hsub)
    · exact mul_nonneg (Real.exp_nonneg _) (boltzmannWeight_pos G ⟨J, 0, β⟩ _).le
  -- Sum, factor out constant, reindex by involution
  calc ∑ σ, (if cutEdges G S ⊆ phaseBoundary G σ then
          boltzmannWeight G ⟨J, 0, β⟩ σ else 0)
      ≤ ∑ σ, (Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
          boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ)) :=
        Finset.sum_le_sum (fun σ _ => hfactor σ)
    _ = Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
          ∑ σ, boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ) :=
        (Finset.mul_sum ..).symm
    _ = Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
          partitionFunction G ⟨J, 0, β⟩ := by
      congr 1; unfold partitionFunction
      exact Fintype.sum_equiv
        (Equiv.ofBijective _ ⟨Config.flipSet_injective S,
          fun τ => ⟨Config.flipSet S τ, by simp⟩⟩)
        _ _ (fun _ => rfl)

/-- **Peierls bound** (Glimm–Jaffe, Prop. 5.4.1). For `h = 0` and any subset S,
`⟨1_{cut(S) ⊆ ∂σ}⟩ ≤ exp(-2βJ|cut(S)|)`. -/
theorem peierls_bound (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (S : Finset ι) :
    gibbsExpectation G ⟨J, 0, β⟩
      (fun σ => if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) ≤
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
  unfold gibbsExpectation
  have hZ := partitionFunction_pos G ⟨J, 0, β⟩
  -- Simplify: 1 * w(σ) = w(σ), 0 * w(σ) = 0
  have hsimpl : ∀ σ : Config ι,
      (if cutEdges G S ⊆ phaseBoundary G σ then (1 : ℝ) else 0) *
        boltzmannWeight G ⟨J, 0, β⟩ σ =
      if cutEdges G S ⊆ phaseBoundary G σ then
        boltzmannWeight G ⟨J, 0, β⟩ σ else 0 := by
    intro σ; split <;> simp
  simp_rw [hsimpl]
  have h := peierls_sum_bound G J β S
  calc (partitionFunction G ⟨J, 0, β⟩)⁻¹ *
        ∑ x, (if cutEdges G S ⊆ phaseBoundary G x then
          boltzmannWeight G ⟨J, 0, β⟩ x else 0)
      ≤ (partitionFunction G ⟨J, 0, β⟩)⁻¹ *
          (Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
            partitionFunction G ⟨J, 0, β⟩) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hZ.le)
    _ = Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
        rw [mul_comm (Real.exp _) _, ← mul_assoc,
          inv_mul_cancel₀ hZ.ne', one_mul]

/-! ## Spontaneous magnetization (Proposition 5.4.2)

For `d ≥ 2` and `β` sufficiently large, the Ising model on `ℤ^d` with
`+` boundary conditions has spontaneous magnetization:
  `0 ≤ 1 - ⟨σ_i⟩₊ ≤ exp(-cβ)`.

The proof sums the Peierls bound over all contours enclosing site `i`.
The contour counting bound (number of contours of size `r` enclosing `i`
is at most `a * b^r`) is a combinatorial fact about `ℤ^d` lattice paths
that we axiomatize. -/

/-- **Contour counting bound** (Glimm–Jaffe, §5.4, p. 83).
For the `d`-dimensional box graph of size `n`, there exist constants `a, b > 0`
such that for any site `i` and any `r`, the number of subsets `S` containing
`i` with `|cut(S)| = r` is at most `a * b ^ r`.

For a fixed box, this follows trivially from the finiteness of the power set:
the number of subsets containing `i` is `2^(|V|-1)`, so we take `a = 2^(|V|-1)`
and `b = 1`.

**Note on the infinite-volume limit**: Glimm–Jaffe's tighter bound
`N(r) ≤ r^d · c(d)^r` with constants independent of `n` requires
self-avoiding surface enumeration on ℤ^d (lattice animal counting).
This would be needed for the `n → ∞` limit but is not required for
the Peierls bound on any fixed finite box. -/
theorem contourCountingBound (d : ℕ) (n : ℕ) :
    ∃ (a b : ℝ), 0 < a ∧ 0 < b ∧
      ∀ (i : BoxSite d n) (r : ℕ),
        (Finset.univ.filter (fun S : Finset (BoxSite d n) =>
          i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r)).card ≤ a * b ^ r := by
  refine ⟨2 ^ Fintype.card (BoxSite d n), 1, by positivity, one_pos, fun i r => ?_⟩
  calc ↑(Finset.univ.filter (fun S : Finset (BoxSite d n) =>
        i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r)).card
      ≤ ↑(Finset.univ (α := Finset (BoxSite d n))).card := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = (2 : ℝ) ^ Fintype.card (BoxSite d n) := by
        simp [Finset.card_univ, Fintype.card_finset]
    _ = 2 ^ Fintype.card (BoxSite d n) * 1 ^ r := by ring

/-- **Peierls contour sum bound**. The sum of Peierls probabilities over all
contours enclosing site `i` with a given size `r` is at most
`N(r) * exp(-2βJr)`, where `N(r)` is the contour count. -/
theorem peierls_contour_sum_le (d n : ℕ) (J β : ℝ) (i : BoxSite d n)
    (r : ℕ) (N : ℝ) (hN : (Finset.univ.filter (fun S : Finset (BoxSite d n) =>
      i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r)).card ≤ N) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset (BoxSite d n) =>
        i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r),
      gibbsExpectation (boxGraph d n) ⟨J, 0, β⟩
        (fun σ => if cutEdges (boxGraph d n) S ⊆ phaseBoundary (boxGraph d n) σ
          then 1 else 0) ≤
    N * Real.exp (-2 * β * J * ↑r) := by
  calc ∑ S ∈ Finset.univ.filter (fun S =>
          i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r), _
      ≤ ∑ S ∈ Finset.univ.filter (fun S =>
          i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r),
        Real.exp (-2 * β * J * ↑(cutEdges (boxGraph d n) S).card) := by
        apply Finset.sum_le_sum; intro S hS
        exact peierls_bound (boxGraph d n) J β S
    _ = ∑ _ ∈ Finset.univ.filter (fun S =>
          i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r),
        Real.exp (-2 * β * J * ↑r) := by
        apply Finset.sum_congr rfl; intro S hS
        simp only [Finset.mem_filter] at hS
        rw [hS.2.2]
    _ = ↑(Finset.univ.filter (fun S : Finset (BoxSite d n) =>
          i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r)).card *
        Real.exp (-2 * β * J * ↑r) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * Real.exp (-2 * β * J * ↑r) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hN
        · exact Real.exp_nonneg _

end IsingModel
