import IsingModel.Inequalities.GHS.SpinFlip
import IsingModel.Inequalities.Lebowitz.Cor434

/-!
# GHS inequality split — GJ Cor 4.3.4 and the GHS inequality

Part of the split GHS-inequality layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The former `lebowitz_third` axiom (deleted — it was false as stated)

This file formerly axiomatised the "Lebowitz third inequality"

`⟨σ_iσ_jσ_k⟩ + ⟨σ_i⟩⟨σ_jσ_k⟩ ≤ ⟨σ_iσ_j⟩⟨σ_k⟩ + ⟨σ_iσ_k⟩⟨σ_j⟩`

for ferromagnetic `h ≥ 0`. That statement is **false**: decoupling site `i`
(`J_{i·} = 0`) with `h > 0`, correlations factorise and the claim becomes
`2⟨σ_i⟩⟨σ_jσ_k⟩ ≤ 2⟨σ_i⟩⟨σ_j⟩⟨σ_k⟩`, i.e. `⟨σ_jσ_k⟩ ≤ ⟨σ_j⟩⟨σ_k⟩`,
contradicting strict GKS-II for a strongly coupled edge `jk`. (Equivalently,
the axiom asserted `u₃ + 2⟨σ_i⟩(⟨σ_jσ_k⟩ − ⟨σ_j⟩⟨σ_k⟩) ≤ 0`, strictly
stronger than GHS.)

The correct statement is GJ Corollary 4.3.4 (`Lebowitz.cor_4_3_4`,
`Inequalities/Lebowitz/Cor434.lean`), proven from the duplicate-variable
machinery; it is exactly `u₃ ≤ 0`, so `ghs_inequality` below now follows
directly with no GKS-I or truncated-two-point input.

References:
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.3, Corollary 4.3.4, p. 61
* Lebowitz, Comm. Math. Phys. 35 (1974) -/

/-! ## GHS inequality

**Theorem** (Griffiths–Hurst–Sherman, 1970): For the ferromagnetic Ising
model with `h ≥ 0` and distinct sites `i, j, k`:
`⟨σ_i; σ_j; σ_k⟩ ≤ 0`.

The proof is a direct rearrangement of GJ Corollary 4.3.4
(`Lebowitz.cor_4_3_4`):
`⟨σ_iσ_jσ_k⟩ − ⟨σ_iσ_j⟩⟨σ_k⟩ − ⟨σ_iσ_k⟩⟨σ_j⟩ + ⟨σ_i⟩⟨σ_jσ_k⟩
 ≤ 2⟨σ_i⟩(⟨σ_jσ_k⟩ − ⟨σ_j⟩⟨σ_k⟩)`
is exactly `u₃ ≤ 0` after moving the right side over. -/

/-- **GHS inequality** (Griffiths–Hurst–Sherman, 1970):
For ferromagnetic parameters with distinct sites,
the truncated 3-point function is non-positive.
`⟨σ_i; σ_j; σ_k⟩ ≤ 0`. -/
theorem ghs_inequality (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3 G p i j k ≤ 0 := by
  have hleb := Lebowitz.cor_4_3_4 G p hf i j k hij hik hjk
  unfold truncated3
  linarith


end IsingModel
