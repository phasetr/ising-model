import IsingModel.InfiniteVolume.Lattice

/-!
# Infinite-volume correlations split — monotonicity in beta and convergence as h tends to infinity

Part of the split infinite-volume correlation layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Monotonicity in β (inverse temperature)

The correlation function is monotone increasing in β for ferromagnetic
parameters. Proof uses the rescaling identity
`⟨σ^A⟩_{(J,h,β)} = ⟨σ^A⟩_{(βJ, βh, 1)}`
(analogous to `partitionFunction_beta_rescale` in `Conditioning.lean`)
to reduce to the already-established `correlation_monotone_J`
(Prop 4.2.1) and `correlation_monotone_h` (Prop 4.2.1 at the singleton
couplings).

Reference: Glimm–Jaffe, Proposition 4.2.1, p. 58 (monotonicity in the
couplings `J_A`, which yields the J-direction directly and the h-direction
through the singleton couplings); Glimm–Jaffe do not state the β-direction,
which is a repository extension obtained from the rescaling identity.
Cor. 10.2.3 is the corresponding statement for the partition function `Z`. -/

/-- The rescaling identity for the correlation function:
`⟨σ^A⟩_{(J, h, β)} = ⟨σ^A⟩_{(βJ, βh, 1)}`. Follows from the fact that
the Boltzmann weights `exp(-β H_{J,h}(σ))` and `exp(-1 · H_{βJ,βh}(σ))`
are pointwise equal. -/
private theorem correlation_rescale_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (A : Finset ι) :
    correlation G ⟨J, h, β⟩ A = correlation G ⟨β * J, β * h, 1⟩ A := by
  have hw : ∀ σ : Config ι,
      boltzmannWeight G ⟨J, h, β⟩ σ = boltzmannWeight G ⟨β * J, β * h, 1⟩ σ := by
    intro σ
    unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
    congr 1; ring
  unfold correlation gibbsExpectation partitionFunction
  simp_rw [hw]

/-- **Correlation β-monotonicity**: for ferromagnetic parameters
(`J ≥ 0`, `h ≥ 0`), the correlation function is monotone increasing in
the inverse temperature `β` on `(0, ∞)`.

Proof: Apply the rescaling identity `correlation_rescale_beta` to
reduce to `correlation_monotone_J` and `correlation_monotone_h`:
increasing β from β₁ to β₂ moves `(β₁J, β₁h)` to `(β₂J, β₂h)` with
both components non-decreasing. -/
theorem correlation_monotone_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (A : Finset ι) :
    MonotoneOn (fun β : ℝ => correlation G ⟨J, h, β⟩ A) (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ _ hβ
  change correlation G ⟨J, h, β₁⟩ A ≤ correlation G ⟨J, h, β₂⟩ A
  rw [correlation_rescale_beta G J h β₁ A,
      correlation_rescale_beta G J h β₂ A]
  have hβ₁' : 0 < β₁ := hβ₁
  have hβ₂' : 0 < β₂ := lt_of_lt_of_le hβ₁' hβ
  have hβ₁J : 0 ≤ β₁ * J := mul_nonneg hβ₁'.le hJ
  have hβ₂J : 0 ≤ β₂ * J := mul_nonneg hβ₂'.le hJ
  have hβ₁h : 0 ≤ β₁ * h := mul_nonneg hβ₁'.le hh
  have hβ₂h : 0 ≤ β₂ * h := mul_nonneg hβ₂'.le hh
  calc correlation G ⟨β₁ * J, β₁ * h, 1⟩ A
      ≤ correlation G ⟨β₂ * J, β₁ * h, 1⟩ A :=
        correlation_monotone_J G (β₁ * h) hβ₁h 1 one_pos A
          (Set.mem_Ici.mpr hβ₁J) (Set.mem_Ici.mpr hβ₂J)
          (mul_le_mul_of_nonneg_right hβ hJ)
    _ ≤ correlation G ⟨β₂ * J, β₂ * h, 1⟩ A :=
        correlation_monotone_h G (β₂ * J) hβ₂J 1 one_pos A
          (Set.mem_Ici.mpr hβ₁h) (Set.mem_Ici.mpr hβ₂h)
          (mul_le_mul_of_nonneg_right hβ hh)

/-- **Correlation β-convergence**: for ferromagnetic parameters
(`J ≥ 0`, `h ≥ 0`), the sequence `⟨σ^A⟩_{(J, h, n+1)}` converges as
`n → ∞`. Uses `β = n + 1` to keep `β > 0`.

Proof: Monotone increasing by `correlation_monotone_beta`, bounded above
by `1` via `correlation_le_one`, hence converges by `tendsto_atTop_ciSup`. -/
theorem correlation_convergent_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (A : Finset ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlation G ⟨J, h, (n + 1 : ℝ)⟩ A)
      Filter.atTop (nhds L) := by
  have h_mono : Monotone (fun n : ℕ => correlation G ⟨J, h, (n + 1 : ℝ)⟩ A) := by
    intro a b hab
    have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
    have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
      have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
      linarith
    exact correlation_monotone_beta G J hJ h hh A
      (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) hab'
  have h_bdd : BddAbove (Set.range
      (fun n : ℕ => correlation G ⟨J, h, (n + 1 : ℝ)⟩ A)) :=
    ⟨1, fun _ ⟨n, hn⟩ => hn ▸ correlation_le_one G ⟨J, h, (n + 1 : ℝ)⟩ A⟩
  exact ⟨_, tendsto_atTop_ciSup h_mono h_bdd⟩

/-! ## Convergence as h → ∞

Filling the monotonicity/convergence matrix: we had `J → ∞`
(`correlation_convergent`) and `β → ∞` (`correlation_convergent_beta`);
this section adds `h → ∞` by the same monotone-bounded argument using
`correlation_monotone_h` (Prop 4.2.1 at the singleton couplings). -/

/-- **Correlation h → ∞ convergence**: for ferromagnetic parameters
(`J ≥ 0`, `β > 0`), the sequence `n ↦ ⟨σ^A⟩_{(J, n, β)}` converges as
`n → ∞`.

Proof: Monotone increasing by `correlation_monotone_h`
(Prop 4.2.1 at the singleton couplings),
bounded above by `1` via `correlation_le_one`, hence converges by
`tendsto_atTop_ciSup`. -/
theorem correlation_convergent_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (A : Finset ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlation G ⟨J, (n : ℝ), β⟩ A)
      Filter.atTop (nhds L) := by
  have h_mono : Monotone (fun n : ℕ => correlation G ⟨J, (n : ℝ), β⟩ A) := by
    intro a b hab
    have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    exact correlation_monotone_h G J hJ β hβ A
      (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb) (by exact_mod_cast hab)
  have h_bdd : BddAbove (Set.range
      (fun n : ℕ => correlation G ⟨J, (n : ℝ), β⟩ A)) :=
    ⟨1, fun _ ⟨n, hn⟩ => hn ▸ correlation_le_one G ⟨J, (n : ℝ), β⟩ A⟩
  exact ⟨_, tendsto_atTop_ciSup h_mono h_bdd⟩


end IsingModel
