import IsingModel.PhaseTransition.Core

/-!
# Magnetization and susceptibility wrappers

This module contains the magnetization and susceptibility layer split from
`IsingModel.PhaseTransition`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Symmetry breaking (§5.3)

Glimm–Jaffe §5.3 discusses symmetry breaking in the context of phase
transitions. The key formalizable content for finite volume:

1. **Z₂ symmetry at h = 0**: already proved as `correlation_odd_vanish`
   in `GHS.lean` — for `h = 0`, odd correlations vanish.

2. **Magnetization as order parameter**: `M = ⟨σ_i⟩` (eq. 5.3.5).

3. **Susceptibility**: `χ = Σ_j ⟨σ_i; σ_j⟩ ≥ 0` (finite-volume sum).
   Non-negativity follows from `truncated2_nonneg`.

4. **Concavity of M(h)**: `d²M/dh² ≤ 0` for `h ≥ 0` follows from
   GHS inequality (Cor. 4.3.4). This is stated conceptually.

References: Glimm–Jaffe, §5.3, pp. 77–80, esp. p. 80. -/

/-- **Magnetization** (order parameter, eq. (5.3.5)):
`M(i) = ⟨σ_i⟩ = correlation G p {i}`. -/
noncomputable def magnetization (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i : ι) : ℝ :=
  correlation G p {i}

/-- **Unfolding of `magnetization`**: `magnetization G p i = correlation G p {i}`. -/
theorem magnetization_apply (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i : ι) :
    magnetization G p i = correlation G p {i} := rfl

/-- **`|magnetization| ≤ 1`** for any parameters and any site `i`.
Direct from `abs_correlation_le_one` at `A = {i}`. -/
theorem abs_magnetization_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i : ι) :
    |magnetization G p i| ≤ 1 :=
  abs_correlation_le_one G p {i}

/-- **`magnetization ≤ 1`** unconditionally. Direct from
`correlation_le_one` at `A = {i}`. -/
theorem magnetization_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i : ι) :
    magnetization G p i ≤ 1 :=
  correlation_le_one G p {i}

/-- **`-1 ≤ magnetization`** unconditionally. Direct from
`neg_one_le_correlation` at `A = {i}`. -/
theorem neg_one_le_magnetization (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i : ι) :
    -1 ≤ magnetization G p i :=
  neg_one_le_correlation G p {i}

/-- **`0 ≤ magnetization`** for ferromagnetic `p`. Direct from
`gks_first` at `A = {i}` (GKS-I). -/
theorem magnetization_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ι) :
    0 ≤ magnetization G p i :=
  gks_first G p hf {i}

/-- **`magnetization² ≤ 1`** unconditionally. Immediate from
`abs_magnetization_le_one` via `sq_le_one'`. -/
theorem magnetization_sq_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i : ι) :
    magnetization G p i ^ 2 ≤ 1 := by
  have h := abs_magnetization_le_one G p i
  have : |magnetization G p i| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **Susceptibility** (per site `i`):
`χ(i) = Σ_j ⟨σ_i; σ_j⟩ = Σ_j truncated2(i, j)`.

The susceptibility measures the response of the magnetization to the
external field. It equals `dM/dh` in the thermodynamic limit. -/
noncomputable def susceptibility (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i : ι) : ℝ :=
  ∑ j : ι, truncated2 G p i j

/-- **Unfolding of `susceptibility`**:
`susceptibility G p i = ∑ j, truncated2 G p i j`. -/
theorem susceptibility_apply (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i : ι) :
    susceptibility G p i = ∑ j : ι, truncated2 G p i j := rfl

/-- The susceptibility is non-negative for ferromagnetic parameters.
Follows from `truncated2_nonneg`: each term `⟨σ_i; σ_j⟩ ≥ 0`. -/
theorem susceptibility_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ι) :
    0 ≤ susceptibility G p i := by
  unfold susceptibility
  exact Finset.sum_nonneg (fun j _ => truncated2_nonneg G p hf i j)

/-- **Susceptibility closed form at `J = 0`** (Finset-based): for any
ambient graph `G`, any `h, β`, and any site `i`,

`susceptibility G ⟨0, h, β⟩ i = tanh(β·h) · (1 − tanh(β·h))`.

Caveat: this is the repo-level `susceptibility` built from
`truncated2` which uses the Finset `{i, j}` — at `j = i` this
collapses to `{i}` and yields `⟨σ_i⟩ − ⟨σ_i⟩² = t − t²`, not the
physics `⟨σ_i σ_i⟩ − ⟨σ_i⟩² = 1 − ⟨σ_i⟩²` (which would use
`σ_i² = 1`). Accordingly this formula differs from the physics
response-function identity `dM/dh = β·(1 − t²)` at the diagonal.

Proof: `susceptibility i = ∑_j truncated2 i j`. For `j ≠ i`,
`truncated2_J_zero_of_ne` makes the summand 0. For `j = i`,
`{i, i} = {i}` as Finset, so the term reduces to
`correlation {i} − (correlation {i})² = t − t²` with
`t = tanh(β·h)` (via `correlation_J_zero`). Factor to `t · (1 − t)`.

Complements the trivial-slice sweep of PRs #207-#215, #218-#219.
Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.1
(non-interacting `J = 0` slice); §5.1 pp. 76–77 (susceptibility). -/
theorem susceptibility_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i : ι) :
    susceptibility G (⟨0, h, β⟩ : IsingParams ℝ) i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h)) := by
  unfold susceptibility
  rw [Finset.sum_eq_single i]
  · -- Diagonal term at j = i: truncated2 i i = t - t^2
    unfold truncated2
    have hsingleton : ({i, i} : Finset ι) = {i} := by simp
    rw [hsingleton, correlation_J_zero, Finset.card_singleton, pow_one]
    ring
  · -- Off-diagonal: truncated2 i j = 0 for j ≠ i
    intro j _ hji
    exact truncated2_J_zero_of_ne G h β hji.symm
  · -- j ∉ univ is vacuous
    intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **Susceptibility vanishes at `β = 0`**: for any ambient graph
`G`, any `J, h`, and any site `i`, `susceptibility G ⟨J, h, 0⟩ i = 0`.

Proof: every summand in `∑_j truncated2 G ⟨J, h, 0⟩ i j` vanishes
by `truncated2_beta_zero` (PR #208). Companion to
`susceptibility_J_zero`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.1
infinite-temperature slice; §5.1 pp. 76–77. -/
theorem susceptibility_beta_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i : ι) :
    susceptibility G (⟨J, h, 0⟩ : IsingParams ℝ) i = 0 := by
  unfold susceptibility
  refine Finset.sum_eq_zero ?_
  intro j _
  exact truncated2_beta_zero G J h i j

/-- **Susceptibility under `h → -h`**:
`susceptibility G ⟨J,-h,β⟩ i = susceptibility G ⟨J,h,β⟩ i - 2·magnetization G ⟨J,h,β⟩ i`.

The off-diagonal `j ≠ i` terms are invariant by `truncated2_neg_h`.
The diagonal `j = i` term, via the Finset collapse `{i,i} = {i}`,
contributes:
`truncated2(-h, i, i) − truncated2(h, i, i) = −2·correlation(h, {i}) = −2·M(h)`
where `M = magnetization`, i.e. the odd-symmetry of the singleton
`correlation(h, {i})` (`correlation_neg_h` at card 1). Summing gives
the total shift `−2·M(h)`.

At `h = 0`: `M = 0` by Z₂, so `χ(-0) = χ(0)` (consistent with
`susceptibility_h_zero`).

Reference: Glimm–Jaffe §5.3. -/
theorem susceptibility_neg_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i : ι) :
    susceptibility G (⟨J, -h, β⟩ : IsingParams ℝ) i
      = susceptibility G (⟨J, h, β⟩ : IsingParams ℝ) i
          - 2 * magnetization G (⟨J, h, β⟩ : IsingParams ℝ) i := by
  unfold susceptibility magnetization
  -- Split each side into j ≠ i and j = i contributions.
  have hmem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hsplit_neg :
      (∑ j, truncated2 G (⟨J, -h, β⟩ : IsingParams ℝ) i j)
        = (∑ j ∈ Finset.univ \ {i},
              truncated2 G (⟨J, -h, β⟩ : IsingParams ℝ) i j)
          + truncated2 G (⟨J, -h, β⟩ : IsingParams ℝ) i i :=
    Finset.sum_eq_sum_diff_singleton_add hmem _
  have hsplit_pos :
      (∑ j, truncated2 G (⟨J, h, β⟩ : IsingParams ℝ) i j)
        = (∑ j ∈ Finset.univ \ {i},
              truncated2 G (⟨J, h, β⟩ : IsingParams ℝ) i j)
          + truncated2 G (⟨J, h, β⟩ : IsingParams ℝ) i i :=
    Finset.sum_eq_sum_diff_singleton_add hmem _
  rw [hsplit_neg, hsplit_pos]
  -- Off-diagonal: pointwise invariance via truncated2_neg_h
  have hoff : ∑ j ∈ Finset.univ \ {i},
        truncated2 G (⟨J, -h, β⟩ : IsingParams ℝ) i j
      = ∑ j ∈ Finset.univ \ {i},
          truncated2 G (⟨J, h, β⟩ : IsingParams ℝ) i j := by
    refine Finset.sum_congr rfl ?_
    intros j hj
    have hji : j ≠ i := by simpa using (Finset.mem_sdiff.mp hj).2
    exact truncated2_neg_h G J h β (Ne.symm hji)
  rw [hoff]
  -- Diagonal: compute truncated2(-h, i, i) - truncated2(h, i, i) = -2 M(h)
  unfold truncated2
  have hii : ({i, i} : Finset ι) = {i} := by simp
  rw [hii, correlation_neg_h G J h β {i}]
  simp only [Finset.card_singleton, pow_one]
  ring

/-- **Truncated 2-point at `h = 0`** (finite volume): for any `J, β`
and any sites `i, j`,
`truncated2 G ⟨J, 0, β⟩ i j = correlation G ⟨J, 0, β⟩ {i, j}`.

At `h = 0` the singleton correlations `⟨σ_i⟩ = ⟨σ_j⟩ = 0` vanish by
Z₂ (`correlation_odd_vanish`), so the Ursell 2-point reduces to the
2-point correlation. Finite-volume counterpart of
`truncated2Infinite_h_zero`.

Reference: Glimm–Jaffe §5.1 pp. 72–74. -/
theorem truncated2_h_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    truncated2 G (⟨J, 0, β⟩ : IsingParams ℝ) i j
      = correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} := by
  unfold truncated2
  have h_i : Odd ({i} : Finset ι).card := by simp
  have h_j : Odd ({j} : Finset ι).card := by simp
  rw [correlation_odd_vanish G J β _ h_i,
      correlation_odd_vanish G J β _ h_j]
  ring

/-- **Susceptibility closed form at `h = 0`** (finite volume):
`susceptibility G ⟨J, 0, β⟩ i = ∑_j correlation G ⟨J, 0, β⟩ {i, j}`.

At `h = 0` each `truncated2 i j` reduces to `correlation {i, j}` by
`truncated2_h_zero` (Z₂ kills the `⟨σ_i⟩⟨σ_j⟩` piece). Companion to
`susceptibility_J_zero` / `susceptibility_beta_zero`.

Reference: Glimm–Jaffe §5.3 pp. 77–80. -/
theorem susceptibility_h_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    susceptibility G (⟨J, 0, β⟩ : IsingParams ℝ) i
      = ∑ j : ι, correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} := by
  unfold susceptibility
  exact Finset.sum_congr rfl (fun j _ => truncated2_h_zero G J β i j)

/-- **Magnetization Z₂ odd-symmetry under `h → -h`**:
`magnetization G ⟨J, -h, β⟩ i = -magnetization G ⟨J, h, β⟩ i`.

Direct consequence of `correlation_neg_h` at `A = {i}` (card 1, so
`(-1)^1 = -1`).

Reference: Glimm–Jaffe §5.3 pp. 77–80. -/
theorem magnetization_neg_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i : ι) :
    magnetization G (⟨J, -h, β⟩ : IsingParams ℝ) i
      = -magnetization G (⟨J, h, β⟩ : IsingParams ℝ) i := by
  unfold magnetization
  rw [correlation_neg_h G J h β {i}, Finset.card_singleton, pow_one]
  ring

/-- **`|magnetization(h)| = magnetization(|h|)`** under ferromagnetic
at `|h|`: requires `0 ≤ J ∧ 0 < β` (so that `Ferromagnetic ⟨J, |h|, β⟩`
holds automatically, since `0 ≤ |h|`). Combines `magnetization_neg_h`
with `magnetization_nonneg` at the absolute-value parameters.

Odd-card counterpart of `correlation_eq_abs_h_of_even_card`: at
`|A|` even the correlation is invariant, at `|A|` odd the magnitude
is invariant modulo sign. At `|A| = 1` (the magnetization case),
this gives `|M(h)| = M(|h|)` under ferromagnetic `|h|`.

Reference: Glimm–Jaffe §5.3. -/
theorem abs_magnetization_eq_magnetization_abs_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : ι) :
    |magnetization G (⟨J, h, β⟩ : IsingParams ℝ) i|
      = magnetization G (⟨J, |h|, β⟩ : IsingParams ℝ) i := by
  have hf_abs : Ferromagnetic (⟨J, |h|, β⟩ : IsingParams ℝ) :=
    ⟨hJ, abs_nonneg _, hβ⟩
  have habs_nonneg : 0 ≤ magnetization G (⟨J, |h|, β⟩ : IsingParams ℝ) i :=
    magnetization_nonneg G _ hf_abs i
  rcases abs_choice h with habs | habs
  · -- |h| = h (i.e. h ≥ 0)
    have heq : magnetization G (⟨J, |h|, β⟩ : IsingParams ℝ) i
        = magnetization G (⟨J, h, β⟩ : IsingParams ℝ) i := by rw [habs]
    rw [heq]
    apply abs_of_nonneg
    have h_ge : 0 ≤ h := by rw [← habs]; exact abs_nonneg h
    exact magnetization_nonneg G _ ⟨hJ, h_ge, hβ⟩ i
  · -- |h| = -h (i.e. h ≤ 0)
    have hneg : magnetization G (⟨J, |h|, β⟩ : IsingParams ℝ) i
        = -magnetization G (⟨J, h, β⟩ : IsingParams ℝ) i := by
      rw [habs]; exact magnetization_neg_h G J h β i
    rw [hneg]
    apply abs_of_nonpos
    have hne : 0 ≤ -magnetization G (⟨J, h, β⟩ : IsingParams ℝ) i := by
      rw [← hneg]; exact habs_nonneg
    linarith

/-- **Susceptibility at `|h|` in closed form (finite volume)**:
`χ(⟨J, |h|, β⟩) = χ(⟨J, h, β⟩) + M(⟨J, |h|, β⟩) − M(⟨J, h, β⟩)`.

**No ferromagnetic assumption is required** (in that narrow sense the
identity is unconditional in `J, h, β`; it remains a finite-volume
statement with the existing `SimpleGraph ι` / `Fintype G.edgeSet`
ambient typeclass assumptions). Proof by `abs_choice h`:

- If `|h| = h` (i.e. `h ≥ 0`), the correction term
  `M(|h|) − M(h)` vanishes and both sides equal `χ(h)`.
- If `|h| = -h` (i.e. `h ≤ 0`), `susceptibility_neg_h` gives
  `χ(-h) = χ(h) − 2·M(h)` and `magnetization_neg_h` gives
  `M(-h) = −M(h)`, so the RHS equals `χ(h) + (−M(h)) − M(h)
  = χ(h) − 2·M(h)`, matching the LHS.

Companion to `abs_magnetization_eq_magnetization_abs_h` which uses
ferromagnetism to express `|M(h)| = M(|h|)`. Under that same
ferromagnetic hypothesis, this theorem can be combined to yield the
non-negative closed form `χ(|h|) − χ(h) = |M(h)| − M(h)
= 2·max(0, −M(h))`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibility_eq_abs_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i : ι) :
    susceptibility G (⟨J, |h|, β⟩ : IsingParams ℝ) i
      = susceptibility G (⟨J, h, β⟩ : IsingParams ℝ) i
          + magnetization G (⟨J, |h|, β⟩ : IsingParams ℝ) i
          - magnetization G (⟨J, h, β⟩ : IsingParams ℝ) i := by
  rcases abs_choice h with habs | habs
  · rw [habs]; ring
  · rw [habs, susceptibility_neg_h G J h β i, magnetization_neg_h G J h β i]
    ring

/-- The magnetization vanishes at `h = 0` (Z₂ symmetry, finite volume).
This is the finite-volume counterpart of the statement that the Z₂
symmetry is unbroken in finite volume. Symmetry breaking occurs only
in the infinite volume limit. -/
theorem magnetization_zero_at_h_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    magnetization G ⟨J, 0, β⟩ i = 0 := by
  unfold magnetization
  exact correlation_odd_vanish G J β {i} ⟨0, by simp⟩

/-- The magnetization vanishes at `β = 0` (infinite temperature,
finite volume). At `β = 0` the Gibbs measure is uniform and spins
are independent with zero mean (`±1` symmetric distribution), so
every single-site expectation is `0`.

Specialization of `correlation_beta_zero_vanish_of_nonempty_A`
(Inequalities/NonnegCorrelations.lean) at the singleton `{i}`
(automatically nonempty). Finite-volume companion to
`magnetizationInfinite_beta_zero`. -/
theorem magnetization_beta_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i : ι) :
    magnetization G ⟨J, h, 0⟩ i = 0 := by
  unfold magnetization
  exact correlation_beta_zero_vanish_of_nonempty_A G J h {i} ⟨i, by simp⟩

/-- The magnetization at `J = 0` (non-interacting model) has the
closed form `M(i) = tanh(β·h)`.

At `J = 0` the Hamiltonian has no inter-site coupling and the sites
are independent; single-site expectation `⟨σ_i⟩` under an external
field `h` at inverse temperature `β` is the mean of a `±1`-valued
random variable with `P(+1) ∝ exp(βh)` and `P(-1) ∝ exp(-βh)`,
giving `tanh(βh)`.

Specialization of `correlation_J_zero`
(`⟨σ^A⟩ = tanh(βh)^|A|`) at the singleton `{i}`. Finite-volume
companion to `magnetizationInfinite_J_zero` (PR #218). Completes
the three trivial slices of `magnetization`:
`J = 0` (`tanh(βh)`), `β = 0` (`0`), `h = 0` (`0`).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.1
(non-interacting `J = 0` slice); §5.1 pp. 76–77 (magnetization). -/
theorem magnetization_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i : ι) :
    magnetization G (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) := by
  unfold magnetization
  rw [correlation_J_zero, Finset.card_singleton, pow_one]


end IsingModel
