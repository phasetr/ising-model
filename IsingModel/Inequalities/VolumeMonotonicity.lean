import IsingModel.Inequalities.MonotonicityExtremal

/-!
# Volume monotonicity of the `+` boundary state (FV Lemma 3.22)

For a ferromagnetic Ising model, the `+` boundary-condition expectation of a
monotone observable **decreases as the volume grows**:

  `Λ₁ ⊆ Λ₂  ⟹  ⟨φ⟩^+_{Λ₂} ≤ ⟨φ⟩^+_{Λ₁}`   (for nondecreasing `φ`).

Together with the lower bound (the `−` state is monotone increasing in volume),
this gives the `+`/`−` states as monotone limits over an exhaustion — the
construction of the extremal infinite-volume Gibbs states.

The proof uses the conditioning structure of the boundary-condition measures.
In the conditioning picture, the `+` state at `Λ₁` is the `+` state at `Λ₂`
**conditioned on the shell `Λ₂ ∖ Λ₁` being all `+`** (`agreesOff Λ₁ (+) =
agreesOff Λ₂ (+) ∧ "all + on Λ₂ ∖ Λ₁"`).  The shell event `A` is an **up-set**, so
its indicator `1_A` is monotone, and conditioning a measure on an up-set raises
the expectation of every monotone observable:

  `⟨φ⟩^+_{Λ₁} = ⟨φ·1_A⟩^+_{Λ₂} / ⟨1_A⟩^+_{Λ₂} ≥ ⟨φ⟩^+_{Λ₂}`

by the FKG inequality `⟨φ·1_A⟩ ≥ ⟨φ⟩⟨1_A⟩` (`fkg_isingBC_of_monotone`, both `φ`
and `1_A` monotone).

* `upShellIndicator` + `upShellIndicator_monotone` — the shell up-set indicator.
* `boltzmannWeightBC_plus_eq_shell_mul` — the conditioning weight identity.
* `gibbsExpectationBC_plus_volume_antitone` — the volume monotonicity.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
Lemma 3.22 (p. 99) and §6.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The shell up-set indicator -/

/-- **Shell up-set indicator**: `1` iff every spin on the shell `Λ₂ ∖ Λ₁` is `up`.
The shell event is an up-set, so this indicator is monotone. -/
noncomputable def upShellIndicator (Λ₁ Λ₂ : Finset ι) (σ : Config ι) : ℝ :=
  if (∀ i ∈ Λ₂ \ Λ₁, σ i = Spin.up) then 1 else 0

/-- The shell indicator is nonnegative. -/
theorem upShellIndicator_nonneg (Λ₁ Λ₂ : Finset ι) (σ : Config ι) :
    0 ≤ upShellIndicator Λ₁ Λ₂ σ := by
  unfold upShellIndicator; split <;> norm_num

/-- The shell indicator is monotone: the shell event `{σ : σ = + on Λ₂ ∖ Λ₁}` is an
up-set (if `σ ≤ τ` and `σ` is `+` on the shell, then so is `τ`, as `up` is the
maximum). -/
theorem upShellIndicator_monotone (Λ₁ Λ₂ : Finset ι) :
    Monotone (upShellIndicator Λ₁ Λ₂) := by
  intro σ τ hστ
  unfold upShellIndicator
  split
  · split
    · exact le_refl _
    · rename_i hσ hτ
      exact absurd (fun i hi => le_antisymm (Spin.le_up (τ i)) (hσ i hi ▸ hστ i)) hτ
  · split <;> norm_num

/-! ## The conditioning weight identity -/

omit [Fintype ι] in
/-- **Boundary-agreement decomposition**: for `Λ₁ ⊆ Λ₂`, a configuration agrees
with `+` off `Λ₁` iff it agrees with `+` off `Λ₂` and is `+` on the shell
`Λ₂ ∖ Λ₁`. -/
theorem agreesOff_plus_iff_shell {Λ₁ Λ₂ : Finset ι} (hsub : Λ₁ ⊆ Λ₂) (σ : Config ι) :
    agreesOff Λ₁ (plusConfig ι) σ ↔
      (∀ i ∈ Λ₂ \ Λ₁, σ i = Spin.up) ∧ agreesOff Λ₂ (plusConfig ι) σ := by
  constructor
  · intro h
    refine ⟨fun i hi => h i (Finset.mem_sdiff.mp hi).2, fun i hi => h i (fun hi₁ => hi (hsub hi₁))⟩
  · rintro ⟨hshell, h2⟩ i hi
    by_cases hi₂ : i ∈ Λ₂
    · exact hshell i (Finset.mem_sdiff.mpr ⟨hi₂, hi⟩)
    · exact h2 i hi₂

/-- **Conditioning weight identity**: for `Λ₁ ⊆ Λ₂`, the `+` boundary-condition
weight at `Λ₁` equals the shell indicator times the `+` weight at `Λ₂`:

`w^+_{Λ₁}(σ) = 1_A(σ)·w^+_{Λ₂}(σ)`.

This is the measure-level statement that the `Λ₁` `+` state is the `Λ₂` `+` state
conditioned on the shell being all `+`. -/
theorem boltzmannWeightBC_plus_eq_shell_mul (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) {Λ₁ Λ₂ : Finset ι} (hsub : Λ₁ ⊆ Λ₂) (σ : Config ι) :
    boltzmannWeightBC G β J h Λ₁ (plusConfig ι) σ =
      upShellIndicator Λ₁ Λ₂ σ * boltzmannWeightBC G β J h Λ₂ (plusConfig ι) σ := by
  unfold upShellIndicator
  by_cases h1 : agreesOff Λ₁ (plusConfig ι) σ
  · obtain ⟨hshell, h2⟩ := (agreesOff_plus_iff_shell hsub σ).mp h1
    rw [boltzmannWeightBC_of_agrees G β J h h1, if_pos hshell, one_mul,
      boltzmannWeightBC_of_agrees G β J h h2]
  · rw [boltzmannWeightBC_of_not_agrees G β J h h1]
    by_cases hshell : (∀ i ∈ Λ₂ \ Λ₁, σ i = Spin.up)
    · rw [if_pos hshell, one_mul]
      by_cases h2 : agreesOff Λ₂ (plusConfig ι) σ
      · exact absurd ((agreesOff_plus_iff_shell hsub σ).mpr ⟨hshell, h2⟩) h1
      · rw [boltzmannWeightBC_of_not_agrees G β J h h2]
    · rw [if_neg hshell, zero_mul]

/-! ## Volume monotonicity of the + state -/

/-- The shell indicator has strictly positive `+`-state expectation at `Λ₂`
(`plusConfig` itself is `+` on the shell, with positive weight). -/
theorem gibbsExpectationBC_plus_upShell_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (Λ₁ Λ₂ : Finset ι) :
    0 < gibbsExpectationBC G β J h Λ₂ (plusConfig ι) (upShellIndicator Λ₁ Λ₂) := by
  unfold gibbsExpectationBC
  apply mul_pos (inv_pos.mpr (partitionFunctionBC_pos G β J h Λ₂ (plusConfig ι)))
  refine Finset.sum_pos' (fun σ _ => mul_nonneg (upShellIndicator_nonneg Λ₁ Λ₂ σ)
    (boltzmannWeightBC_nonneg G β J h Λ₂ (plusConfig ι) σ)) ⟨plusConfig ι, mem_univ _, ?_⟩
  have hshell : ∀ i ∈ Λ₂ \ Λ₁, (plusConfig ι) i = Spin.up := fun i _ => rfl
  rw [upShellIndicator, if_pos hshell, one_mul,
    boltzmannWeightBC_of_agrees G β J h (agreesOff_self Λ₂ (plusConfig ι))]
  exact boltzmannWeightJ_pos G β J h (plusConfig ι)

/-- **Volume monotonicity of the `+` state** (FV Lemma 3.22): for a ferromagnetic
Ising model (`β ≥ 0`, `J(e) ≥ 0`), `Λ₁ ⊆ Λ₂`, and a monotone nondecreasing
observable `φ`,

`⟨φ⟩^+_{Λ₂} ≤ ⟨φ⟩^+_{Λ₁}`,

i.e. the `+` boundary expectation decreases as the volume grows.  The `Λ₁` `+`
state is the `Λ₂` `+` state conditioned on the shell up-set `A`; conditioning on
the up-set `A` raises the expectation of the monotone `φ` by FKG. -/
theorem gibbsExpectationBC_plus_volume_antitone (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    {Λ₁ Λ₂ : Finset ι} (hsub : Λ₁ ⊆ Λ₂)
    (φ : Config ι → ℝ) (hφ_mono : Monotone φ) :
    gibbsExpectationBC G β J h Λ₂ (plusConfig ι) φ ≤
      gibbsExpectationBC G β J h Λ₁ (plusConfig ι) φ := by
  classical
  set A : Config ι → ℝ := upShellIndicator Λ₁ Λ₂ with hA_def
  have hA_mono : Monotone A := upShellIndicator_monotone Λ₁ Λ₂
  set ZA := gibbsExpectationBC G β J h Λ₂ (plusConfig ι) A with hZA_def
  have hZA_pos : 0 < ZA := gibbsExpectationBC_plus_upShell_pos G Λ₁ Λ₂
  -- Conditioning identity: ⟨φ·A⟩₂ = ⟨φ⟩₁ · ⟨A⟩₂.
  have hkey : gibbsExpectationBC G β J h Λ₂ (plusConfig ι) (φ * A)
      = gibbsExpectationBC G β J h Λ₁ (plusConfig ι) φ * ZA := by
    have hweight : ∀ σ : Config ι, boltzmannWeightBC G β J h Λ₁ (plusConfig ι) σ
        = A σ * boltzmannWeightBC G β J h Λ₂ (plusConfig ι) σ :=
      fun σ => boltzmannWeightBC_plus_eq_shell_mul G β J h hsub σ
    -- Numerator and partition relations from the weight identity.
    have hnum : ∑ σ : Config ι, φ σ * boltzmannWeightBC G β J h Λ₁ (plusConfig ι) σ
        = ∑ σ : Config ι, (φ * A) σ * boltzmannWeightBC G β J h Λ₂ (plusConfig ι) σ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [hweight σ]
      simp only [Pi.mul_apply]
      ring
    have hZ1 : partitionFunctionBC G β J h Λ₁ (plusConfig ι)
        = ∑ σ : Config ι, A σ * boltzmannWeightBC G β J h Λ₂ (plusConfig ι) σ := by
      unfold partitionFunctionBC
      apply Finset.sum_congr rfl
      intro σ _
      exact hweight σ
    have hZ1ne : partitionFunctionBC G β J h Λ₁ (plusConfig ι) ≠ 0 :=
      partitionFunctionBC_ne_zero G β J h Λ₁ (plusConfig ι)
    have hZ2ne : partitionFunctionBC G β J h Λ₂ (plusConfig ι) ≠ 0 :=
      partitionFunctionBC_ne_zero G β J h Λ₂ (plusConfig ι)
    -- `⟨φ⟩₁ = Z₁⁻¹ ∑ (φA)w₂` (numerator identity) and `ZA = Z₂⁻¹ Z₁` (partition identity).
    have hg1 : gibbsExpectationBC G β J h Λ₁ (plusConfig ι) φ
        = (partitionFunctionBC G β J h Λ₁ (plusConfig ι))⁻¹ *
          ∑ σ : Config ι, (φ * A) σ * boltzmannWeightBC G β J h Λ₂ (plusConfig ι) σ := by
      unfold gibbsExpectationBC; rw [hnum]
    have hZA' : ZA = (partitionFunctionBC G β J h Λ₂ (plusConfig ι))⁻¹ *
        partitionFunctionBC G β J h Λ₁ (plusConfig ι) := by
      rw [hZA_def]; unfold gibbsExpectationBC; rw [← hZ1]
    rw [hg1, hZA']
    unfold gibbsExpectationBC
    field_simp
  -- FKG: ⟨φ⟩₂·⟨A⟩₂ ≤ ⟨φ·A⟩₂.
  have hfkg := fkg_isingBC_of_monotone (h := h) G hβ hJ Λ₂ (plusConfig ι) φ A hφ_mono hA_mono
  rw [hkey] at hfkg
  -- ⟨φ⟩₂·ZA ≤ ⟨φ⟩₁·ZA, cancel ZA > 0.
  exact le_of_mul_le_mul_right hfkg hZA_pos

end IsingModel
