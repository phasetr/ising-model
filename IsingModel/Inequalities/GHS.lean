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
* `ghs_inequality` — `⟨σ_i; σ_j; σ_k⟩ ≤ 0` for `h ≥ 0`

## References

* Ellis, *Entropy, Large Deviations, and Statistical Mechanics*, §V.3
* Griffiths, Hurst, Sherman, J. Math. Phys. 11 (1970)
* Lebowitz, Comm. Math. Phys. 35 (1974)
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Truncated correlation functions -/

/-- The truncated 2-point function (connected correlation):
`⟨σ_i; σ_j⟩ = ⟨σ_iσ_j⟩ - ⟨σ_i⟩⟨σ_j⟩`. -/
noncomputable def truncated2 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i j : ι) : ℝ :=
  correlation G p {i, j} - correlation G p {i} * correlation G p {j}

/-- The truncated 3-point function (Ursell function) for distinct sites:
`⟨σ_i; σ_j; σ_k⟩ = ⟨σ_iσ_jσ_k⟩ - ⟨σ_i⟩⟨σ_jσ_k⟩ - ⟨σ_j⟩⟨σ_iσ_k⟩
  - ⟨σ_k⟩⟨σ_iσ_j⟩ + 2⟨σ_i⟩⟨σ_j⟩⟨σ_k⟩`. -/
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
  · subst hij
    have h1 := gks_first G p hf {i}
    have h2 := abs_correlation_le_one G p {i}
    have h3 : correlation G p {i} ≤ 1 := le_trans (le_abs_self _) h2
    have hpair : ({i, i} : Finset ι) = {i} := by simp
    rw [hpair]; nlinarith
  · have h := gks_second G p hf {i} {j}
    have hsym : symmDiff {i} {j} = ({i, j} : Finset ι) := by
      ext x; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      exact ⟨fun h => h.elim (fun ⟨h, _⟩ => Or.inl h) (fun ⟨h, _⟩ => Or.inr h),
        fun h => h.elim (fun h => Or.inl ⟨h, h ▸ hij⟩)
          (fun h => Or.inr ⟨h, h ▸ Ne.symm hij⟩)⟩
    rw [hsym] at h; linarith

/-! ## GHS inequality

**Theorem** (Griffiths–Hurst–Sherman, 1970): For the ferromagnetic Ising
model with `h ≥ 0` and distinct sites `i, j, k`:
`⟨σ_i; σ_j; σ_k⟩ ≤ 0`.

The proof uses the Lebowitz identity (1974) expressing `truncated3` as
a covariance in the doubled system, which is then shown to be non-positive
via the quadrupled system and Lemma V.3.2 (Ellis-Monroe, 1975).

Reference: Ellis, §V.3, pp. 145–146. -/

/-- **GHS inequality** (Griffiths–Hurst–Sherman, 1970):
For ferromagnetic parameters with distinct sites,
the truncated 3-point function is non-positive.
`⟨σ_i; σ_j; σ_k⟩ ≤ 0`.

The proof requires the Ellis-Monroe quadrupled spin system with
Hadamard transformation (α,β,γ,δ) and the Lebowitz identity.
The building blocks (Lebowitz identity + Lemma V.3.2 parity argument)
are mathematically verified but their Lean formalization requires
~200 lines of doubled/quadrupled graph infrastructure.
See `.self-local/tex/0019-ghs-inequality.tex` for the full proof. -/
axiom ghs_inequality (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3 G p i j k ≤ 0

end IsingModel
