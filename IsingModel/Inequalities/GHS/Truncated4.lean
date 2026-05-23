import IsingModel.Inequalities.GHS.GHSInequality

/-!
# GHS inequality split — Cor 4.3.3 truncated 4-point function nonpositivity

Part of the split GHS-inequality layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Corollary 4.3.3: truncated 4-point function ≤ 0

For h = 0 and four distinct sites, the truncated (connected) 4-point
correlation function is non-positive:
  U₄(i,j,k,l) = ⟨σ_iσ_jσ_kσ_l⟩ - ⟨σ_iσ_j⟩⟨σ_kσ_l⟩
                 - ⟨σ_iσ_k⟩⟨σ_jσ_l⟩ - ⟨σ_iσ_l⟩⟨σ_jσ_k⟩ ≤ 0.

This requires the Lebowitz inequality for 4-point functions (the general
Cor. 4.3.2), which goes beyond our 3-site `lebowitz_third` axiom.
We axiomatize the 4-site Lebowitz inequality as the Ising translation of
`⟨t_{ij}q_{kl}⟩ ≤ ⟨t_{ij}⟩⟨q_{kl}⟩` in the doubled system. -/

/-- The truncated (connected) 4-point function for distinct sites:
`U₄(i,j,k,l) = ⟨σ_iσ_jσ_kσ_l⟩ - ⟨σ_iσ_j⟩⟨σ_kσ_l⟩
               - ⟨σ_iσ_k⟩⟨σ_jσ_l⟩ - ⟨σ_iσ_l⟩⟨σ_jσ_k⟩`. -/
noncomputable def truncated4 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i j k l : ι) : ℝ :=
  correlation G p {i, j, k, l}
  - correlation G p {i, j} * correlation G p {k, l}
  - correlation G p {i, k} * correlation G p {j, l}
  - correlation G p {i, l} * correlation G p {j, k}

/-- **Infinite-temperature (`β = 0`) vanishing of the Lebowitz
4-point (truncated) function**: for any ambient graph `G`, any
`J, h ∈ ℝ`, and any sites `i, j, k, l : ι`,
`truncated4 G ⟨J, h, 0⟩ i j k l = 0`.

At `β = 0`, each of the seven Finset correlations in the Lebowitz
combination is over a nonempty subset (every subset contains at
least one of the supplied sites), so
`correlation_beta_zero_vanish_of_nonempty_A` makes every term zero
and the linear combination vanishes.

Companion to `truncated2_beta_zero` / `truncated3_beta_zero`. No
distinctness hypotheses are needed at `β = 0`. Note: unlike the
`β = 0` case, `truncated4` does *not* vanish at `J = 0` in
general — the Lebowitz 4-point is `-2·t⁴` where `t = tanh(β·h)`
for pairwise distinct sites, which is non-zero when `β·h ≠ 0`.
So this PR adds only the `β = 0` slice.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster property context); §4.3 Cor. 4.3.3 / Lebowitz. -/
theorem truncated4_beta_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i j k l : ι) :
    truncated4 G (⟨J, h, 0⟩ : IsingParams ℝ) i j k l = 0 := by
  unfold truncated4
  rw [correlation_beta_zero_vanish_of_nonempty_A G J h {i, j, k, l}
        ⟨i, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {i, j}
        ⟨i, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {k, l}
        ⟨k, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {i, k}
        ⟨i, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {j, l}
        ⟨j, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {i, l}
        ⟨i, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {j, k}
        ⟨j, by simp⟩]
  ring

/-- **Non-interacting (`J = 0`) closed form for the Lebowitz 4-point
(truncated) function**: for any ambient graph `G`, any `h, β ∈ ℝ`,
and pairwise distinct `i, j, k, l : ι`,
`truncated4 G ⟨0, h, β⟩ i j k l = -2 · tanh(β·h)^4`.

At `J = 0`, `correlation_J_zero` gives
`⟨σ^A⟩ = tanh(β·h)^|A|`. With pairwise distinct
`i, j, k, l` one has `{i,j,k,l}.card = 4`,
`{i,j}.card = {i,k}.card = {i,l}.card = {j,k}.card =
{j,l}.card = {k,l}.card = 2`, so the Lebowitz combination becomes
`t⁴ - t² · t² - t² · t² - t² · t² = t⁴ - 3·t⁴ = -2·t⁴`
with `t = tanh(β·h)`.

This complements `truncated4_beta_zero` (vanishing slice): at
`J = 0` the Lebowitz 4-point does not vanish but has the explicit
closed form `-2·t⁴`. Note `-2·t⁴ ≤ 0` always, consistent with
the `U₄ ≤ 0` statement of Cor. 4.3.3 (though Cor. 4.3.3 itself
is the `h = 0` case; our `J = 0` slice is an independent special
case and not a direct witness of the Cor. 4.3.3 theorem).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster context); §4.3 Cor. 4.3.3 / Lebowitz. -/
theorem truncated4_J_zero_of_pairwise_distinct
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) {i j k l : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4 G (⟨0, h, β⟩ : IsingParams ℝ) i j k l
      = -2 * Real.tanh (β * h) ^ 4 := by
  unfold truncated4
  rw [correlation_J_zero, correlation_J_zero, correlation_J_zero,
      correlation_J_zero, correlation_J_zero, correlation_J_zero,
      correlation_J_zero]
  have hcard_ijkl : ({i, j, k, l} : Finset ι).card = 4 := by
    have h_jkl_card : ({j, k, l} : Finset ι).card = 3 := by
      rw [show ({j, k, l} : Finset ι) = insert j ({k, l} : Finset ι) from rfl,
          Finset.card_insert_of_notMem (by simp [hjk, hjl]),
          Finset.card_pair hkl]
    have h_i_nin : i ∉ ({j, k, l} : Finset ι) := by
      simp [hij, hik, hil]
    rw [show ({i, j, k, l} : Finset ι) = insert i ({j, k, l} : Finset ι)
            from rfl,
        Finset.card_insert_of_notMem h_i_nin, h_jkl_card]
  have hcard_ij : ({i, j} : Finset ι).card = 2 := Finset.card_pair hij
  have hcard_ik : ({i, k} : Finset ι).card = 2 := Finset.card_pair hik
  have hcard_il : ({i, l} : Finset ι).card = 2 := Finset.card_pair hil
  have hcard_jk : ({j, k} : Finset ι).card = 2 := Finset.card_pair hjk
  have hcard_jl : ({j, l} : Finset ι).card = 2 := Finset.card_pair hjl
  have hcard_kl : ({k, l} : Finset ι).card = 2 := Finset.card_pair hkl
  rw [hcard_ijkl, hcard_ij, hcard_kl, hcard_ik, hcard_jl, hcard_il, hcard_jk]
  ring

/-- **Lebowitz 4-site inequality** (Glimm–Jaffe, Cor. 4.3.2 for |A|=|B|=2).
For ferromagnetic Ising with `h ≥ 0` and four distinct sites,
`⟨σ_iσ_jσ_kσ_l⟩ + ⟨σ_iσ_j⟩⟨σ_kσ_l⟩
  ≤ ⟨σ_iσ_k⟩⟨σ_jσ_l⟩ + ⟨σ_iσ_l⟩⟨σ_jσ_k⟩
    + ⟨σ_iσ_kσ_l⟩⟨σ_j⟩ + ⟨σ_jσ_kσ_l⟩⟨σ_i⟩`.

This is the Ising translation of `⟨t_At_Bq_Cq_D⟩ ≤ ⟨t_At_B⟩⟨q_Cq_D⟩`
from Cor. 4.3.2 applied with A = {i,j}, B = {k,l}. Proved via φ⁴
approximation, same route as `lebowitz_third`. -/
axiom lebowitz_four (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    correlation G p {i, j, k, l} + correlation G p {i, j} * correlation G p {k, l} ≤
    correlation G p {i, k} * correlation G p {j, l} +
    correlation G p {i, l} * correlation G p {j, k} +
    correlation G p {i, k, l} * correlation G p {j} +
    correlation G p {j, k, l} * correlation G p {i}

/-- **Cor. 4.3.3** (Glimm–Jaffe, §4.3, p. 61).
For `h = 0` and four distinct sites, the truncated 4-point function
is non-positive: `U₄(i,j,k,l) ≤ 0`.

When `h = 0`, odd-cardinality correlations vanish by spin-flip symmetry,
so `⟨σ_i⟩ = ⟨σ_j⟩ = 0` and `⟨σ_{ijk}⟩ = 0`, reducing the Lebowitz
4-site inequality to `U₄ ≤ 0`. -/
theorem cor_4_3_3 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4 G ⟨J, 0, β⟩ i j k l ≤ 0 := by
  have hleb := lebowitz_four G ⟨J, 0, β⟩ hf i j k l hij hik hil hjk hjl hkl
  -- For h = 0: odd-cardinality correlations vanish.
  -- ⟨σ_i⟩ = 0, ⟨σ_{ijk}⟩ = 0 by spin-flip symmetry.
  -- This is a consequence of hamiltonian_flip_eq: H(flip σ) = H(σ) when h = 0,
  -- combined with spinProduct_flip: σ^A(flip) = (-1)^|A| σ^A,
  -- giving ⟨σ^A⟩ = (-1)^|A| ⟨σ^A⟩, so ⟨σ^A⟩ = 0 when |A| is odd.
  -- For now we use correlation_flip_odd which states this directly.
  -- TODO: prove correlation = 0 for odd |A| when h = 0 from spin-flip symmetry
  have hcorr1 : correlation G ⟨J, 0, β⟩ {i} = 0 :=
    correlation_odd_vanish G J β {i} ⟨0, by simp⟩
  have hcorr3a : correlation G ⟨J, 0, β⟩ {i, k, l} = 0 :=
    correlation_odd_vanish G J β {i, k, l} ⟨1, by simp [Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, hik, hil, hkl]⟩
  have hcorr3b : correlation G ⟨J, 0, β⟩ {j, k, l} = 0 :=
    correlation_odd_vanish G J β {j, k, l} ⟨1, by simp [Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, hjk, hjl, hkl]⟩
  -- Even-cardinality correlations are non-negative by GKS-I.
  have h_ij := gks_first G ⟨J, 0, β⟩ hf {i, j}
  have h_kl := gks_first G ⟨J, 0, β⟩ hf {k, l}
  unfold truncated4
  simp only [hcorr1, hcorr3a, hcorr3b, mul_zero, zero_mul, add_zero] at hleb ⊢
  nlinarith [mul_nonneg h_ij h_kl]


end IsingModel
