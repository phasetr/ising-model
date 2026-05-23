import IsingModel.FreeEnergy.SubgraphBounds

/-!
# Free energy special values and lower bounds

Mechanical child split from `IsingModel.FreeEnergy`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Proposition 4.6.1** (Glimm–Jaffe, p. 68): The free energy converges
along any increasing sequence of subgraphs on a fixed ambient finite lattice.

The free energy `n ↦ f_{Gₙ}` is monotone (by `freeEnergy_monotone_subgraph`)
and bounded above by `f_⊤` (free energy on the complete graph, via
`le_top`), hence converges to its supremum by `tendsto_atTop_ciSup`. -/
theorem freeEnergy_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => freeEnergy (Gn n) p)
      Filter.atTop (nhds L) := by
  have h_mono : Monotone (fun n : ℕ => freeEnergy (Gn n) p) :=
    fun a b hab => freeEnergy_monotone_subgraph (hmono hab) p hf
  have h_bdd : BddAbove (Set.range (fun n : ℕ => freeEnergy (Gn n) p)) :=
    ⟨freeEnergy (⊤ : SimpleGraph ι) p,
     fun _ ⟨n, hn⟩ => hn ▸ freeEnergy_monotone_subgraph le_top p hf⟩
  exact ⟨_, tendsto_atTop_ciSup h_mono h_bdd⟩

/-- **Free energy at zero parameters**: for nonempty lattice `ι` with
`0 < Fintype.card ι`, `freeEnergy G ⟨0, 0, β⟩ = log 2`.

Combines `partitionFunction_zero_params` (Z = |Config ι|) with
`card_config_eq_two_pow` (|Config ι| = 2^|ι|) and
`Real.log_pow` (log(2^|ι|) = |ι| · log 2); the `|ι|⁻¹` prefix then
cancels to give `log 2`. -/
theorem freeEnergy_zero_params (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (hne : 0 < Fintype.card ι) :
    freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
  unfold freeEnergy
  rw [partitionFunction_zero_params, card_config_eq_two_pow]
  push_cast
  rw [Real.log_pow]
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast hne.ne'
  field_simp

/-- **Free energy on the empty graph** (free-spin / one-body limit):
for nonempty `ι`,
`freeEnergy (⊥ : SimpleGraph ι) p = log (2 · cosh(β · h))`.

Combines `partitionFunction_bot` (`Z = (2 cosh(β h))^|ι|`) with
`Real.log_pow` (`log(a^n) = n · log a`, valid here since
`2 cosh(β h) > 0`); the `|ι|⁻¹` prefix then cancels to give
`log (2 cosh(β h))`.

Complements `freeEnergy_zero_params` (the `J = h = 0` point, where
`cosh 0 = 1` recovers `log 2`) by extending to arbitrary `h` on the
J-less graph. -/
theorem freeEnergy_bot (p : IsingParams ℝ) (hne : 0 < Fintype.card ι) :
    freeEnergy (⊥ : SimpleGraph ι) p
      = Real.log (2 * Real.cosh (p.β * p.h)) := by
  unfold freeEnergy
  rw [partitionFunction_bot, Real.log_pow]
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast hne.ne'
  field_simp

/-- **Free energy h-symmetry**: `freeEnergy G ⟨J, -h, β⟩ = freeEnergy G ⟨J, h, β⟩`.

Immediate from `partitionFunction_neg_h` (spin-flip reindexing) by
taking `log` and dividing by `|ι|`. -/
theorem freeEnergy_neg_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    freeEnergy G (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergy G (⟨J, h, β⟩ : IsingParams ℝ) := by
  unfold freeEnergy
  rw [partitionFunction_neg_h]

/-- **Free energy equals its value at `|h|`**:
`freeEnergy G ⟨J, h, β⟩ = freeEnergy G ⟨J, |h|, β⟩`.

Case-split on `|h| = h ∨ |h| = -h` and apply `freeEnergy_neg_h` when
needed. -/
theorem freeEnergy_eq_abs_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    freeEnergy G (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergy G (⟨J, |h|, β⟩ : IsingParams ℝ) := by
  rcases abs_choice h with habs | habs
  · rw [habs]
  · rw [habs, freeEnergy_neg_h]

/-- **Free energy is monotone in `|h|`** for ferromagnetic parameters:
`|h₁| ≤ |h₂| → freeEnergy G ⟨J, h₁, β⟩ ≤ freeEnergy G ⟨J, h₂, β⟩`.

Combines `freeEnergy_eq_abs_h` (h-even) with `freeEnergy_monotone_h`
on `[0, ∞)`: rewrite both sides as `freeEnergy G ⟨J, |hᵢ|, β⟩` and
apply the `Ici 0` monotonicity using `abs_nonneg`. -/
theorem freeEnergy_monotone_abs_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergy G (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergy G (⟨J, h₂, β⟩ : IsingParams ℝ) := by
  rw [freeEnergy_eq_abs_h G J h₁ β, freeEnergy_eq_abs_h G J h₂ β]
  have := freeEnergy_monotone_h G J β hJ hβ
    (Set.mem_Ici.mpr (abs_nonneg h₁))
    (Set.mem_Ici.mpr (abs_nonneg h₂)) hh
  exact this

/-- **Partition function is monotone in `|h|`** for ferromagnetic parameters:
`|h₁| ≤ |h₂| → Z(J, h₁, β) ≤ Z(J, h₂, β)`.

Combines `partitionFunction_eq_abs_h` (Z even in h) with
`partitionFunction_monotone_h` on `[0, ∞)`. Z-level counterpart of
`freeEnergy_monotone_abs_h`. -/
theorem partitionFunction_monotone_abs_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    partitionFunction G (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ partitionFunction G (⟨J, h₂, β⟩ : IsingParams ℝ) := by
  rw [partitionFunction_eq_abs_h G J h₁ β,
      partitionFunction_eq_abs_h G J h₂ β]
  exact partitionFunction_monotone_h G J β hJ hβ _ _ (abs_nonneg h₁) hh

/-- **Free energy at `β = 0`**: for nonempty `ι` and any `J, h : ℝ`,
`freeEnergy G ⟨J, h, 0⟩ = log 2`.

Corollary of `partitionFunction_beta_zero` (`Z = |Config ι| = 2^|ι|`),
taking `log` and dividing by `|ι|`. β-direction analogue of
`freeEnergy_zero_params` (`J = h = 0`), holds for any ambient `G`. -/
theorem freeEnergy_beta_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (hne : 0 < Fintype.card ι) :
    freeEnergy G (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 := by
  unfold freeEnergy
  rw [partitionFunction_beta_zero, card_config_eq_two_pow]
  push_cast
  rw [Real.log_pow]
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast hne.ne'
  field_simp

/-- **Free energy on the empty graph at zero field**: for nonempty `ι`
and any `J, β : ℝ`,
`freeEnergy (⊥ : SimpleGraph ι) ⟨J, 0, β⟩ = log 2`.

Corollary of `freeEnergy_bot` at `h = 0` (`cosh 0 = 1`, `log(2·1) = log 2`).
Consistent with `freeEnergy_zero_params` (`J = h = 0`) and shows that on
the J-less graph the coupling `J` is dormant. -/
theorem freeEnergy_bot_h_zero (J β : ℝ) (hne : 0 < Fintype.card ι) :
    freeEnergy (⊥ : SimpleGraph ι) (⟨J, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 := by
  rw [freeEnergy_bot _ hne]
  simp [Real.cosh_zero]

/-- **Graph-independent free energy identity at `J = 0`**:
`freeEnergy G ⟨0, h, β⟩ = freeEnergy ⊥ ⟨0, h, β⟩`.

Immediate from `partitionFunction_eq_bot_at_J_zero` after unfolding
`freeEnergy := |ι|⁻¹ · log Z`. -/
theorem freeEnergy_eq_bot_at_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) :
    freeEnergy G (⟨0, h, β⟩ : IsingParams ℝ)
      = freeEnergy (⊥ : SimpleGraph ι) (⟨0, h, β⟩ : IsingParams ℝ) := by
  unfold freeEnergy
  rw [partitionFunction_eq_bot_at_J_zero]

/-- **Free energy at `J = 0`** (graph-independent): for nonempty `ι`,
any `h, β : ℝ`, and any ambient graph `G`,
`freeEnergy G ⟨0, h, β⟩ = log (2·cosh(β·h))`.

Combines `freeEnergy_eq_bot_at_J_zero` (graph independence) with
`freeEnergy_bot` (`⊥` closed form). -/
theorem freeEnergy_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (hne : 0 < Fintype.card ι) :
    freeEnergy G (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  (freeEnergy_eq_bot_at_J_zero G h β).trans (freeEnergy_bot _ hne)

/-- **Sharp ferromagnetic lower bound**: for any graph `G` with
`|ι| > 0` and ferromagnetic parameters, `log(2·cosh(β·h)) ≤ freeEnergy G p`.

Obtained from `freeEnergy_bot` (free-spin closed form) and
`freeEnergy_monotone_subgraph` (ferromagnetic, `⊥ ≤ G` via `bot_le`).
Sharpens `log 2` (since `cosh(β h) ≥ 1`, with equality at `h = 0`). -/
theorem freeEnergy_ge_log_two_cosh (G : SimpleGraph ι) [Fintype G.edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (hne : 0 < Fintype.card ι) :
    Real.log (2 * Real.cosh (β * h)) ≤ freeEnergy G ⟨J, h, β⟩ := by
  have hferm : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ) := ⟨hJ, hh, hβ⟩
  calc Real.log (2 * Real.cosh (β * h))
      = freeEnergy (⊥ : SimpleGraph ι) (⟨J, h, β⟩ : IsingParams ℝ) := by
        rw [freeEnergy_bot _ hne]
    _ ≤ freeEnergy G (⟨J, h, β⟩ : IsingParams ℝ) :=
        freeEnergy_monotone_subgraph bot_le _ hferm

/-- **Free energy lower bound `log 2 ≤ f_G(p)` for ferromagnetic.**

Weaker than `freeEnergy_ge_log_two_cosh` (which uses the sharp
`log (2 · cosh(β h))` bound) but doesn't depend on the specific form of
`p`; takes a `Ferromagnetic p` hypothesis uniformly.

Via `Real.one_le_cosh`, `2 · cosh(β h) ≥ 2`, so
`log 2 ≤ log (2 · cosh(β h))` by log-monotonicity; then compose with
`freeEnergy_ge_log_two_cosh`. -/
theorem freeEnergy_ge_log_two_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hne : 0 < Fintype.card ι) :
    Real.log 2 ≤ freeEnergy G p := by
  obtain ⟨J, h, β⟩ := p
  have h_cosh : 1 ≤ Real.cosh (β * h) := Real.one_le_cosh _
  have h_log : Real.log 2 ≤ Real.log (2 * Real.cosh (β * h)) := by
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    linarith
  exact h_log.trans (freeEnergy_ge_log_two_cosh G hf.hJ hf.hh hf.hβ hne)

/-- **Nonnegativity `0 ≤ f_G(p)` for ferromagnetic parameters** on
nonempty `ι`. Immediate from
`freeEnergy_ge_log_two_of_ferromagnetic` and `Real.log_pos`
(`0 < log 2`). -/
theorem freeEnergy_nonneg_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hne : 0 < Fintype.card ι) :
    0 ≤ freeEnergy G p :=
  (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans
    (freeEnergy_ge_log_two_of_ferromagnetic G p hf hne)
end IsingModel
