import IsingModel.InfiniteVolume

/-!
# GHS inequality

The Griffiths-Hurst-Sherman (GHS) inequality: for the ferromagnetic Ising
model with non-negative external field, the truncated three-point correlation
function is non-positive.

## Main results

* `truncated2` — the truncated 2-point function (connected correlation)
* `truncated3` — the truncated 3-point function (Ursell function)
* `truncated2_nonneg` — `⟨σ_i; σ_j⟩ ≥ 0` (from GKS-II)
* `ghs_inequality` — `⟨σ_i; σ_j; σ_k⟩ ≤ 0` for `h ≥ 0` (sorry)

## Proof approach

The proof follows Ellis–Monroe (1975) via a quadrupled spin system,
as presented in Ellis, *Entropy, Large Deviations, and Statistical
Mechanics*, §V.3, pp. 143–146.

## References

* Ellis, *Entropy, Large Deviations, and Statistical Mechanics*, §V.3
* Griffiths, Hurst, Sherman, *Concavity of magnetization of an Ising
  ferromagnet in a positive external field*, J. Math. Phys. 11 (1970)
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Truncated correlation functions -/

/-- The truncated 2-point function (connected correlation):
`⟨σ_i; σ_j⟩ = ⟨σ_iσ_j⟩ - ⟨σ_i⟩⟨σ_j⟩`.
By GKS-II, this is `≥ 0` for ferromagnetic parameters. -/
noncomputable def truncated2 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i j : ι) : ℝ :=
  correlation G p {i, j} - correlation G p {i} * correlation G p {j}

/-- The truncated 3-point function (Ursell function) for distinct sites:
`⟨σ_i; σ_j; σ_k⟩ = ⟨σ_iσ_jσ_k⟩ - ⟨σ_i⟩⟨σ_jσ_k⟩ - ⟨σ_j⟩⟨σ_iσ_k⟩
  - ⟨σ_k⟩⟨σ_iσ_j⟩ + 2⟨σ_i⟩⟨σ_j⟩⟨σ_k⟩`.

Note: This uses Finset `{i, j, k}`, so `i`, `j`, `k` should be distinct
for the formula to match the physics convention. When indices coincide,
`σ_i² = 1` (Ising) gives different values than the Finset version. -/
noncomputable def truncated3 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i j k : ι) : ℝ :=
  correlation G p {i, j, k}
  - correlation G p {i} * correlation G p {j, k}
  - correlation G p {j} * correlation G p {i, k}
  - correlation G p {k} * correlation G p {i, j}
  + 2 * correlation G p {i} * correlation G p {j} * correlation G p {k}

/-- The truncated 2-point function is non-negative by GKS-II. -/
theorem truncated2_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : ι) :
    0 ≤ truncated2 G p i j := by
  unfold truncated2
  by_cases hij : i = j
  · -- i = j: {i, i} = {i}, so truncated2 = corr{i} - corr{i}² ≥ 0
    subst hij
    have h1 := gks_first G p hf {i}
    have h2 := abs_correlation_le_one G p {i}
    have h3 : correlation G p {i} ≤ 1 := le_trans (le_abs_self _) h2
    have hpair : ({i, i} : Finset ι) = {i} := by simp
    rw [hpair]; nlinarith
  · -- i ≠ j: symmDiff {i} {j} = {i, j}, apply GKS-II
    have h := gks_second G p hf {i} {j}
    have hsym : symmDiff {i} {j} = ({i, j} : Finset ι) := by
      ext x; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      exact ⟨fun h => h.elim (fun ⟨h, _⟩ => Or.inl h) (fun ⟨h, _⟩ => Or.inr h),
        fun h => h.elim (fun h => Or.inl ⟨h, h ▸ hij⟩) (fun h => Or.inr ⟨h, h ▸ Ne.symm hij⟩)⟩
    rw [hsym] at h; linarith

/-- **GHS inequality** (Griffiths–Hurst–Sherman, 1970;
Ellis–Monroe, 1975; Ellis, Theorem V.3, p. 143):
For ferromagnetic parameters with distinct sites,
the truncated 3-point function is non-positive.
`⟨σ_i; σ_j; σ_k⟩ ≤ 0`.

The proof uses a quadrupled spin system `(ω, σ, ω', σ')` with Hadamard
orthogonal transformation `(α, β, γ, δ)`. The truncated 3-point equals
a specific moment in the quadrupled system (Lebowitz, 1974) which is
non-positive by Lemma V.3.2 (Ellis, p. 145). -/
theorem ghs_inequality (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3 G p i j k ≤ 0 := by
  sorry

end IsingModel
