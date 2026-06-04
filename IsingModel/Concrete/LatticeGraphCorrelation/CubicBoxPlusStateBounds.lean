import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxPlusState

/-!
# Bounded boundary-condition observables and the single-site `+` box spin (Issue #3565)

Towards the monotone-convergence existence of the infinite-volume `+` state, this
file provides:

* generic two-sided bounds for the boundary-condition Gibbs expectation of a
  bounded observable (`gibbsExpectationBC_le_of_forall_le` /
  `gibbsExpectationBC_ge_of_forall_ge`), giving in particular that the expectation
  of a `[-1, 1]`-valued observable lies in `[-1, 1]`;
* the **single-site `+` box spin** `plusBoxSpin d n m J h β x` — the `+` boundary
  expectation of the single spin `s(σ_x)` on the cubic box — together with its
  range bound `plusBoxSpin_mem_Icc` (`∈ [-1, 1]`, hence the bounded-below input for
  the eventual monotone-convergence limit) and the inner-region antitonicity
  `plusBoxSpin_antitone_interior` (the cubic-box / single-site instance of
  FV Lemma 3.22).

The remaining ingredient for the infinite-volume `+` state — the nearest-neighbour
**screening** lemma making `plusBoxSpin` independent of the ambient box size — is
the subject of the next PR of Issue #3565 (see the issue for the full design).

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
§3.6.2, Lemma 3.22, §6.
-/

namespace IsingModel

namespace Ambient

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Two-sided bounds for bounded boundary-condition observables -/

/-- **Upper bound for the BC expectation of a bounded-above observable**: if
`φ σ ≤ c` for all `σ`, then `⟨φ⟩^η_Λ ≤ c`.  The expectation is a weighted average
(by the nonnegative normalised weights), hence bounded by the pointwise bound. -/
theorem gibbsExpectationBC_le_of_forall_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (η : Config ι)
    {φ : Config ι → ℝ} {c : ℝ} (hφ : ∀ σ, φ σ ≤ c) :
    gibbsExpectationBC G β J h Λ η φ ≤ c := by
  have hZ : 0 < partitionFunctionBC G β J h Λ η := partitionFunctionBC_pos G β J h Λ η
  unfold gibbsExpectationBC
  rw [← (div_eq_inv_mul _ _), div_le_iff₀ hZ]
  calc ∑ σ : Config ι, φ σ * boltzmannWeightBC G β J h Λ η σ
      ≤ ∑ σ : Config ι, c * boltzmannWeightBC G β J h Λ η σ :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_right (hφ σ) (boltzmannWeightBC_nonneg G β J h Λ η σ)
    _ = c * partitionFunctionBC G β J h Λ η := by
        rw [← Finset.mul_sum]; rfl

/-- **Lower bound for the BC expectation of a bounded-below observable**: if
`c ≤ φ σ` for all `σ`, then `c ≤ ⟨φ⟩^η_Λ`. -/
theorem gibbsExpectationBC_ge_of_forall_ge (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (η : Config ι)
    {φ : Config ι → ℝ} {c : ℝ} (hφ : ∀ σ, c ≤ φ σ) :
    c ≤ gibbsExpectationBC G β J h Λ η φ := by
  have hZ : 0 < partitionFunctionBC G β J h Λ η := partitionFunctionBC_pos G β J h Λ η
  unfold gibbsExpectationBC
  rw [← (div_eq_inv_mul _ _), le_div_iff₀ hZ]
  calc c * partitionFunctionBC G β J h Λ η
      = ∑ σ : Config ι, c * boltzmannWeightBC G β J h Λ η σ := by
        rw [← Finset.mul_sum]; rfl
    _ ≤ ∑ σ : Config ι, φ σ * boltzmannWeightBC G β J h Λ η σ :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_right (hφ σ) (boltzmannWeightBC_nonneg G β J h Λ η σ)

end Ambient

open Finset

/-- **Range of the spin sign**: `Spin.sign ℝ s ∈ [-1, 1]`. -/
theorem spin_sign_mem_Icc (s : Spin) : Spin.sign ℝ s ∈ Set.Icc (-1 : ℝ) 1 := by
  cases s <;> simp [Spin.sign, Spin.toSign]

namespace Ambient

/-! ## The single-site `+` box spin -/

/-- **Single-site `+` box spin**: the `+` boundary expectation of the single spin
`s(σ_x)` on the cubic box `cubicBox d m` with inner region `cubicBox d n` (the
annulus frozen to `+`), for a site `x ∈ cubicBox d m`. -/
noncomputable def plusBoxSpin (d n m : ℕ) (J h β : ℝ) (x : Fin d → ℤ)
    (hx : x ∈ cubicBox d m) : ℝ :=
  plusBoxExpectation d n m J h β (fun σ => Spin.sign ℝ (σ ⟨x, hx⟩))

/-- **The single-site `+` box spin lies in `[-1, 1]`** (hence is bounded below,
the input for the monotone-convergence limit).  The single spin observable takes
values in `[-1, 1]`, so its boundary-condition expectation does too. -/
theorem plusBoxSpin_mem_Icc (d n m : ℕ) (J h β : ℝ) (x : Fin d → ℤ)
    (hx : x ∈ cubicBox d m) :
    plusBoxSpin d n m J h β x hx ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · exact gibbsExpectationBC_ge_of_forall_ge _ β (fun _ => J) h _ _
      (fun σ => (spin_sign_mem_Icc (σ ⟨x, hx⟩)).1)
  · exact gibbsExpectationBC_le_of_forall_le _ β (fun _ => J) h _ _
      (fun σ => (spin_sign_mem_Icc (σ ⟨x, hx⟩)).2)

/-- **Inner-region antitonicity of the single-site `+` box spin** (single-site
cubic-box instance of FV Lemma 3.22): within a fixed ambient box `m`, growing the
inner region decreases the `+` expectation of the single spin,
`n₁ ≤ n₂ ⟹ plusBoxSpin d n₂ m … ≤ plusBoxSpin d n₁ m …`. -/
theorem plusBoxSpin_antitone_interior (d : ℕ) {n₁ n₂ m : ℕ} (hn : n₁ ≤ n₂)
    {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (x : Fin d → ℤ) (hx : x ∈ cubicBox d m) :
    plusBoxSpin d n₂ m J h β x hx ≤ plusBoxSpin d n₁ m J h β x hx :=
  plusBoxExpectation_antitone_interior d hn hβ hJ
    (fun σ => Spin.sign ℝ (σ ⟨x, hx⟩))
    (singleSpinObs_monotone (⟨x, hx⟩ : ↑(cubicBox d m)))

end Ambient

end IsingModel
