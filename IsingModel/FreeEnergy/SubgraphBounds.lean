import IsingModel.FreeEnergy.Analyticity

/-!
# Free energy subgraph bounds

Mechanical child split from `IsingModel.FreeEnergy`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Free energy infinite volume convergence (Proposition 4.6.1)

For a ferromagnetic Ising model on a fixed ambient finite lattice `ι`,
the free energy `f_G = |ι|⁻¹ ln Z_G` is monotone along the subgraph
order and bounded above (by `f_⊤` on the complete ambient graph),
hence converges for any increasing sequence of subgraphs.

This is a *discretized* formalization of Glimm–Jaffe Proposition 4.6.1
(p. 68): "Let Z_Λ denote the partition function for a lattice field
with nearest-neighbor, translation-invariant, ferromagnetic pair
interaction; with single-spin distribution satisfying (4.1.4). As
Λ ↑ ∞, f_Λ = |Λ|⁻¹ ln Z_Λ converges". The original statement is
for an infinite ambient lattice with finite-volume exhaustions; our
formalization uses a fixed finite ambient lattice with growing subgraphs.
The proof mechanism (monotonicity + boundedness) is the same.

Note: GJ's Prop 4.6.1 is a general lattice-spin result, not Ising-only;
the Ising model is a special case where the single-spin distribution
is the symmetric Bernoulli measure on `{±1}`. -/

/-- The partition function is monotone in the subgraph order.
For `G₁ ≤ G₂` and ferromagnetic `p`, `Z_{G₁} ≤ Z_{G₂}`.

Proof: Factor `w_{G₂} = R · w_{G₁}` where
`R(σ) = ∏_{e ∈ E(G₂)\E(G₁)} exp(βJ · edgeSpin σ e)`.
Use `exp(x) ≥ 1 + x` and GKS-I (each `⟨σᵢσⱼ⟩_{G₁} ≥ 0`)
to bound `∑ R · w_{G₁} ≥ Z_{G₁}`. -/
theorem partitionFunction_monotone_subgraph
    {G₁ G₂ : SimpleGraph ι} [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunction G₁ p ≤ partitionFunction G₂ p := by
  have hfact : ∀ σ, boltzmannWeight G₂ p σ =
      (∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
        Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e)) *
      boltzmannWeight G₁ p σ :=
    fun σ => boltzmannWeight_subgraph_factor h₁₂ p σ
  have hZ : partitionFunction G₂ p =
      ∑ σ : Config ι,
        (∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
          Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e)) *
        boltzmannWeight G₁ p σ := by
    unfold partitionFunction
    apply Finset.sum_congr rfl; intro σ _; exact hfact σ
  rw [hZ]
  have hR_lb : ∀ σ : Config ι,
      1 + p.β * p.J * ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
        edgeSpin (K := ℝ) σ e ≤
      (∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
        Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e)) := by
    intro σ
    rw [← Real.exp_sum]
    simp_rw [← Finset.mul_sum]
    linarith [Real.add_one_le_exp (p.β * p.J *
      ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset, edgeSpin (K := ℝ) σ e)]
  have hsum_lb : ∑ σ : Config ι,
      (1 + p.β * p.J * ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
        edgeSpin (K := ℝ) σ e) *
      boltzmannWeight G₁ p σ ≤
    ∑ σ : Config ι,
      (∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
        Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e)) *
      boltzmannWeight G₁ p σ := by
    apply Finset.sum_le_sum; intro σ _
    exact mul_le_mul_of_nonneg_right (hR_lb σ) (boltzmannWeight_pos G₁ p σ).le
  have hexpand : ∑ σ : Config ι,
      (1 + p.β * p.J * ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
        edgeSpin (K := ℝ) σ e) *
      boltzmannWeight G₁ p σ =
    partitionFunction G₁ p +
    p.β * p.J * ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
      ∑ σ : Config ι, edgeSpin (K := ℝ) σ e * boltzmannWeight G₁ p σ := by
    unfold partitionFunction
    simp_rw [add_mul, one_mul, Finset.sum_add_distrib]
    congr 1
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    apply Finset.sum_congr rfl; intro σ _; ring
  have hnum_nonneg : ∀ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
      0 ≤ ∑ σ : Config ι,
        edgeSpin (K := ℝ) σ e * boltzmannWeight G₁ p σ := by
    intro e he
    have he₂ : e ∈ G₂.edgeFinset := (Finset.mem_sdiff.mp he).1
    obtain ⟨⟨i, j⟩, rfl⟩ := Quot.exists_rep e
    have hij : i ≠ j := by
      intro h; subst h
      exact (SimpleGraph.mem_edgeFinset.mp he₂).ne rfl
    have hedge : ∀ σ : Config ι, edgeSpin (K := ℝ) σ (Quot.mk _ (i, j)) =
        spinProduct {i, j} σ := by
      intro σ; simp [edgeSpin, Sym2.lift, spinProduct, Finset.prod_pair hij, Spin.sign]
    simp_rw [hedge]
    exact (boltzmannWeight_hasNonnegCorrelations G₁ p hf) {i, j}
  calc partitionFunction G₁ p
      ≤ partitionFunction G₁ p +
        p.β * p.J * ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
          ∑ σ : Config ι, edgeSpin (K := ℝ) σ e * boltzmannWeight G₁ p σ :=
        le_add_of_nonneg_right (mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
          (Finset.sum_nonneg (fun e he => hnum_nonneg e he)))
    _ = _ := hexpand.symm
    _ ≤ _ := hsum_lb

/-- The logarithm of the partition function is monotone in the subgraph
order: for `G₁ ≤ G₂` and ferromagnetic `p`,
`log Z_{G₁} p ≤ log Z_{G₂} p`. Consolidates the
`Real.log_le_log ∘ partitionFunction_monotone_subgraph` pattern. -/
theorem log_partitionFunction_monotone_subgraph
    {G₁ G₂ : SimpleGraph ι} [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (partitionFunction G₁ p) ≤ Real.log (partitionFunction G₂ p) :=
  Real.log_le_log (partitionFunction_pos G₁ p)
    (partitionFunction_monotone_subgraph h₁₂ p hf)

/-- The free energy is monotone in the subgraph order.
Follows from `log_partitionFunction_monotone_subgraph` after multiplying
by `|ι|⁻¹ ≥ 0`. -/
theorem freeEnergy_monotone_subgraph
    {G₁ G₂ : SimpleGraph ι} [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergy G₁ p ≤ freeEnergy G₂ p := by
  unfold freeEnergy
  exact mul_le_mul_of_nonneg_left
    (log_partitionFunction_monotone_subgraph h₁₂ p hf)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- **Unconditional lower bound `Z_⊥ ≥ 1` on the empty graph.**

Since `partitionFunction_bot` gives `Z_⊥ = (2·cosh(β h))^|ι|` and
`Real.one_le_cosh` is unconditional, we have `2·cosh(β h) ≥ 2 ≥ 1`,
and `(...)^|ι| ≥ 1`. No ferromagnetic hypothesis required. -/
theorem partitionFunction_bot_ge_one (p : IsingParams ℝ) :
    (1 : ℝ) ≤ partitionFunction (⊥ : SimpleGraph ι) p := by
  have h_cosh_ge : 1 ≤ 2 * Real.cosh (p.β * p.h) := by
    have : 1 ≤ Real.cosh (p.β * p.h) := Real.one_le_cosh _
    linarith
  have h_pow : 1 ≤ (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι :=
    one_le_pow₀ h_cosh_ge
  rw [partitionFunction_bot]
  exact h_pow

/-- **Lower bound `Z_G ≥ 1` for ferromagnetic parameters.**

The ferromagnetic hypothesis is used only to transport the
unconditional `⊥`-graph bound to `G` via
`partitionFunction_monotone_subgraph`:
`Z_G ≥ Z_⊥ ≥ 1`. Used downstream as the companion to the §4.6
super-additivity inequality: because `log Z_G ≥ 0` (ferromagnetic),
the disjoint-sum chain
`log Z_{Λ₁} + log Z_{Δ} ≤ log Z_{Λ₁ ∪ Δ}` upgrades to subset-wise
monotonicity `log Z_{Λ₁} ≤ log Z_{Λ₁ ∪ Δ}` for any `Δ` disjoint
from `Λ₁`. -/
theorem partitionFunction_ge_one_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    1 ≤ partitionFunction G p :=
  (partitionFunction_bot_ge_one p).trans
    (partitionFunction_monotone_subgraph bot_le p hf)

/-- Logarithmic form: `log Z_G ≥ 0` for ferromagnetic parameters.

Immediate from `partitionFunction_ge_one_of_ferromagnetic` and
`Real.log_nonneg`. -/
theorem log_partitionFunction_nonneg_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ Real.log (partitionFunction G p) :=
  Real.log_nonneg (partitionFunction_ge_one_of_ferromagnetic G p hf)

/-- **Basic identity** `|ι| · freeEnergy G p = log (partitionFunction G p)`
for `0 < |ι|`.

Unfolds the definition `freeEnergy = |ι|⁻¹ · log Z` and cancels the
`|ι|⁻¹` prefactor against the outer `|ι|` via `field_simp`.
The nonempty hypothesis rules out the `|ι| = 0` degenerate case.

Base-layer analog of PR #119's
`card_mul_freeEnergyΛ_eq_log_partitionFunctionΛ_of_nonempty`. -/
theorem card_mul_freeEnergy_eq_log_partitionFunction
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hne : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) * freeEnergy G p
      = Real.log (partitionFunction G p) := by
  unfold freeEnergy
  have hne_card : (Fintype.card ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hne.ne'
  field_simp

/-- **Unconditional `⊥`-graph bound `Z_⊥ ≥ 2^|ι|`.**

From `partitionFunction_bot = (2 · cosh(βh))^|ι|` and
`Real.one_le_cosh`, hence `2 ≤ 2 · cosh(βh)`, hence
`2^|ι| ≤ (2 · cosh(βh))^|ι|`. No ferromagnetic hypothesis
required. -/
theorem partitionFunction_bot_ge_two_pow_card (p : IsingParams ℝ) :
    (2 : ℝ) ^ Fintype.card ι ≤ partitionFunction (⊥ : SimpleGraph ι) p := by
  have h_cosh_ge : (2 : ℝ) ≤ 2 * Real.cosh (p.β * p.h) := by
    have : 1 ≤ Real.cosh (p.β * p.h) := Real.one_le_cosh _
    linarith
  have h_pow : (2 : ℝ) ^ Fintype.card ι
      ≤ (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι :=
    pow_le_pow_left₀ (by norm_num) h_cosh_ge _
  rw [partitionFunction_bot]
  exact h_pow

/-- **Strong ferromagnetic lower bound `Z_G ≥ 2^|ι|`.**

Combines `partitionFunction_bot_ge_two_pow_card` with
`partitionFunction_monotone_subgraph`: `2^|ι| ≤ Z_⊥ ≤ Z_G`.
Strictly sharper than `partitionFunction_ge_one_of_ferromagnetic`
when `|ι| ≥ 1`. Used to derive `log Z_G ≥ |ι| · log 2` (the
sharp version of `≥ 0`). -/
theorem partitionFunction_ge_two_pow_card_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (2 : ℝ) ^ Fintype.card ι ≤ partitionFunction G p :=
  (partitionFunction_bot_ge_two_pow_card p).trans
    (partitionFunction_monotone_subgraph bot_le p hf)

/-- **Sharp ferromagnetic lower bound (non-log form)**:
`(2·cosh(βh))^|ι| ≤ Z_G(p)`.

Direct from `partitionFunction_bot` (`Z_⊥ = (2·cosh(βh))^|ι|`) and
`partitionFunction_monotone_subgraph` (`bot ≤ G`, ferromagnetic).
Sharpening of `partitionFunction_ge_two_pow_card_of_ferromagnetic`
(since `cosh ≥ 1`); the exp-image of PR #173
`log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic`. -/
theorem partitionFunction_ge_two_cosh_pow_card_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι ≤ partitionFunction G p := by
  calc (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι
      = partitionFunction (⊥ : SimpleGraph ι) p := (partitionFunction_bot p).symm
    _ ≤ partitionFunction G p := partitionFunction_monotone_subgraph bot_le p hf

/-- Logarithmic form: `log Z_G ≥ |ι| · log 2` for ferromagnetic.

Immediate from `partitionFunction_ge_two_pow_card_of_ferromagnetic`
via `Real.log_pow` + `Real.log_le_log`. -/
theorem log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Fintype.card ι : ℝ) * Real.log 2 ≤ Real.log (partitionFunction G p) := by
  have h_two_pow_pos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι :=
    pow_pos (by norm_num) _
  have h_log :=
    Real.log_le_log h_two_pow_pos
      (partitionFunction_ge_two_pow_card_of_ferromagnetic G p hf)
  rw [Real.log_pow] at h_log
  exact h_log

/-- **Sharp ferromagnetic log-Z lower bound**:
`|ι| · log(2·cosh(βh)) ≤ log Z_G(p)`.

Sharpening of `log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic`
via `Z_⊥ = (2·cosh(βh))^|ι|` (from `partitionFunction_bot`) and
`Z_⊥ ≤ Z_G` (ferromagnetic `partitionFunction_monotone_subgraph`);
take `log` + `Real.log_pow`. -/
theorem log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Fintype.card ι : ℝ) * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunction G p) := by
  have h_cosh_pos : (0 : ℝ) < 2 * Real.cosh (p.β * p.h) := by
    have := Real.one_le_cosh (p.β * p.h); linarith
  have h_pow_pos : (0 : ℝ) < (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι :=
    pow_pos h_cosh_pos _
  have h_ge : (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι
      ≤ partitionFunction G p := by
    rw [← partitionFunction_bot (p := p)]
    exact partitionFunction_monotone_subgraph bot_le p hf
  have h_log := Real.log_le_log h_pow_pos h_ge
  rw [Real.log_pow] at h_log
  exact h_log

/-- The free energy rescaling identity in `β`:
`f(J, h, β) = f(βJ, βh, 1)`. Follows from `partitionFunction_beta_rescale`
(after taking `log` and multiplying by `|ι|⁻¹`). -/
private theorem freeEnergy_rescale_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    freeEnergy G ⟨J, h, β⟩ = freeEnergy G ⟨β * J, β * h, 1⟩ := by
  unfold freeEnergy
  congr 1
  have hw : ∀ σ : Config ι,
      boltzmannWeight G ⟨J, h, β⟩ σ = boltzmannWeight G ⟨β * J, β * h, 1⟩ σ := by
    intro σ
    unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
    congr 1; ring
  unfold partitionFunction
  simp_rw [hw]

/-- **Free energy β-monotonicity**: for `J, h ≥ 0`, the free energy per
site is monotone increasing in the inverse temperature `β` on `(0, ∞)`.

Proof: Apply the rescaling identity `freeEnergy_rescale_beta` and
combine `freeEnergy_monotone_J` and `freeEnergy_monotone_h`. -/
theorem freeEnergy_monotone_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) :
    MonotoneOn (fun β : ℝ => freeEnergy G ⟨J, h, β⟩) (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ _ hβ
  change freeEnergy G ⟨J, h, β₁⟩ ≤ freeEnergy G ⟨J, h, β₂⟩
  rw [freeEnergy_rescale_beta G J h β₁, freeEnergy_rescale_beta G J h β₂]
  have hβ₁' : 0 < β₁ := hβ₁
  have hβ₂' : 0 < β₂ := lt_of_lt_of_le hβ₁' hβ
  have hβ₁J : 0 ≤ β₁ * J := mul_nonneg hβ₁'.le hJ
  have hβ₂J : 0 ≤ β₂ * J := mul_nonneg hβ₂'.le hJ
  have hβ₁h : 0 ≤ β₁ * h := mul_nonneg hβ₁'.le hh
  have hβ₂h : 0 ≤ β₂ * h := mul_nonneg hβ₂'.le hh
  calc freeEnergy G ⟨β₁ * J, β₁ * h, 1⟩
      ≤ freeEnergy G ⟨β₂ * J, β₁ * h, 1⟩ := by
        have := freeEnergy_monotone_J G (β₁ * h) 1 hβ₁h one_pos
          (Set.mem_Ici.mpr hβ₁J) (Set.mem_Ici.mpr hβ₂J)
          (mul_le_mul_of_nonneg_right hβ hJ)
        exact this
    _ ≤ freeEnergy G ⟨β₂ * J, β₂ * h, 1⟩ := by
        have := freeEnergy_monotone_h G (β₂ * J) 1 hβ₂J one_pos
          (Set.mem_Ici.mpr hβ₁h) (Set.mem_Ici.mpr hβ₂h)
          (mul_le_mul_of_nonneg_right hβ hh)
        exact this

end IsingModel
