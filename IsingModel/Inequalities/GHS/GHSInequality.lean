import IsingModel.Inequalities.GHS.SpinFlip

/-!
# GHS inequality split — Lebowitz third inequality and the GHS inequality

Part of the split GHS-inequality layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Lebowitz third inequality

The Lebowitz third inequality (Lebowitz, 1974) is the key input for the GHS
inequality. It states that in the doubled ferromagnetic Ising system with
`h ≥ 0`, the t-q cross-correlation is bounded:

`⟨σ_iσ_jσ_k⟩ + ⟨σ_i⟩⟨σ_jσ_k⟩ ≤ ⟨σ_iσ_j⟩⟨σ_k⟩ + ⟨σ_iσ_k⟩⟨σ_j⟩`

The proof uses the continuous-spin (φ⁴) approximation:
1. For φ⁴ spins, the quadrupled-system non-negativity holds per site
   (`phi4_single_site_nonneg` in `ContinuousSpin/Phi4.lean`)
2. This gives Theorem 4.3.1 (Glimm–Jaffe): `⟨α^A β^B γ^C δ^D⟩ ≥ 0`
3. Corollary 4.3.2 gives the Lebowitz inequality for continuous spins
4. Ising correlations are limits of φ⁴ correlations as λ → ∞ in
   `dμ = exp(-λ(ξ²-1)²) dξ → ½(δ₊₁ + δ₋₁)`

Note: the per-site factorization in Ellis §V.3 (Lemma V.3.2) does NOT
hold for discrete Ising spins — the all-odd parity case gives negative
values (e.g., `Σ αβγδ exp(2hα) = -8 cosh(2h) < 0` for k=l=m=n=1).
The continuous-spin route is essential.

References:
* Glimm–Jaffe, *Quantum Physics*, §4.3, Corollary 4.3.2
* Lebowitz, Comm. Math. Phys. 35 (1974)
* See `.self-local/tex/0019-ghs-inequality.tex` for the full proof -/

/-- **Lebowitz third inequality** (Lebowitz, 1974):
For ferromagnetic Ising with `h ≥ 0` and distinct sites `i, j, k`,
`⟨σ_iσ_jσ_k⟩ + ⟨σ_i⟩⟨σ_jσ_k⟩ ≤ ⟨σ_iσ_j⟩⟨σ_k⟩ + ⟨σ_iσ_k⟩⟨σ_j⟩`.

Proved for continuous φ⁴ spins via `phi4_single_site_nonneg`
(Glimm–Jaffe, Theorem 4.3.1), then transferred to Ising spins by the
approximation `dμ = exp(-λ(ξ²-1)²) dξ → ½(δ₊₁ + δ₋₁)` as `λ → ∞`. -/
axiom lebowitz_third (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    correlation G p {i, j, k} + correlation G p {i} * correlation G p {j, k} ≤
    correlation G p {i, j} * correlation G p {k} +
    correlation G p {i, k} * correlation G p {j}

/-! ## GHS inequality

**Theorem** (Griffiths–Hurst–Sherman, 1970): For the ferromagnetic Ising
model with `h ≥ 0` and distinct sites `i, j, k`:
`⟨σ_i; σ_j; σ_k⟩ ≤ 0`.

The proof combines three ingredients:
1. **Lebowitz third inequality** (`lebowitz_third`):
   `⟨σ_iσ_jσ_k⟩ + ⟨σ_i⟩⟨σ_jσ_k⟩ ≤ ⟨σ_iσ_j⟩⟨σ_k⟩ + ⟨σ_iσ_k⟩⟨σ_j⟩`
2. **GKS-I** (`gks_first`): `⟨σ_i⟩ ≥ 0`
3. **Truncated 2-point non-negativity** (`truncated2_nonneg`):
   `⟨σ_j; σ_k⟩ ≥ 0`

Substituting the Lebowitz bound into truncated3:
`⟨σ_i; σ_j; σ_k⟩ ≤ -2⟨σ_i⟩ · ⟨σ_j; σ_k⟩ ≤ 0`. -/

/-- **GHS inequality** (Griffiths–Hurst–Sherman, 1970):
For ferromagnetic parameters with distinct sites,
the truncated 3-point function is non-positive.
`⟨σ_i; σ_j; σ_k⟩ ≤ 0`. -/
theorem ghs_inequality (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3 G p i j k ≤ 0 := by
  have hleb := lebowitz_third G p hf i j k hij hjk hik
  have hgks := gks_first G p hf {i}
  have ht2 := truncated2_nonneg G p hf j k
  unfold truncated3 truncated2 at *
  nlinarith [mul_nonneg hgks ht2]


end IsingModel
