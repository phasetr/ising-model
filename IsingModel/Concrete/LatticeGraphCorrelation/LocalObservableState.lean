import IsingModel.Concrete.LatticeGraphCorrelation.LocalObservableLimit

/-!
# The full `+`-state functional on local observables on ℤ^d (Issue #3565)

Extends the infinite-volume `+` expectation from *monotone* local observables
(`tendsto_plusBoxLocalObservable_infiniteVolume`) to **all** local observables,
yielding the `+`-state functional and its linearity / normalisation / positivity
(Friedli–Velenik Theorem 3.17, via the monotone-difference decomposition that
plays the role of Lemma 3.19).

The key elementary fact (`exists_monotone_sub_monotone`): on the finite Boolean
lattice `Config ↑S`, every real function `φ` is a difference of two monotone
functions, `φ = (K·rank + φ) - K·rank`, where `rank σ` counts the up-spins and
`K = 2·max|φ|`.  Adding the large monotone `K·rank` dominates the variation of
`φ` across any single covering step, so `K·rank + φ` is monotone.

* `LocalObservable` — a real function of the spins on a finite support (no
  monotonicity required).
* `configUpRank` / `configUpRank_mono` — the up-spin count, monotone.
* `LocalObservable.upper` / `lower` — the canonical monotone-difference data.
* `plusStateExpectation` — the infinite-volume `+` expectation of any local
  observable, defined as the difference of the two monotone limits.
* `tendsto_plusStateExpectation` — the screened box expectations converge to it.
* `plusStateExpectation_add` / `_const_mul` / `_const` / `_nonneg` /
  `_of_monotone` — linearity, normalisation, positivity, and consistency with the
  monotone limit.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
§3.4 Theorem 3.17 (the infinite-volume `+` state) and Lemma 3.19 (local functions
as combinations of occupation variables).
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

/-- **A local observable**: a real function of the spins on a fixed finite support
`S` (no monotonicity assumption, unlike `LocalMonotoneObservable`). -/
structure LocalObservable (d : ℕ) where
  /-- The finite support of the observable. -/
  S : Finset (Fin d → ℤ)
  /-- The underlying function of the support spins. -/
  φ : Config (↑S : Type _) → ℝ

/-- **The up-spin count** of a support configuration: the number of sites carrying
the `+` spin.  Monotone in the configuration order (`configUpRank_mono`). -/
def configUpRank {d : ℕ} {S : Finset (Fin d → ℤ)} (σ : Config (↑S : Type _)) : ℕ :=
  (Finset.univ.filter (fun i => σ i = Spin.up)).card

/-- The up-spin count is monotone: raising spins can only add `+` sites. -/
theorem configUpRank_mono {d : ℕ} {S : Finset (Fin d → ℤ)} :
    Monotone (configUpRank (S := S)) := by
  intro σ σ' hσσ'
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have h1 : Spin.up ≤ σ' i := hi ▸ hσσ' i
  revert h1; cases σ' i <;> decide

/-- The up-spin count strictly increases along a strict configuration increase:
some site flips from `-` to `+`. -/
theorem configUpRank_lt_of_lt {d : ℕ} {S : Finset (Fin d → ℤ)}
    {σ σ' : Config (↑S : Type _)} (h : σ < σ') : configUpRank σ < configUpRank σ' := by
  obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.mp h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (fun j hj => ?_)]
  · refine ⟨i, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : σ i ≤ σ' i := hle i
      rcases lt_or_eq_of_le h1 with hlt | heq
      · revert hlt; cases σ' i <;> cases σ i <;> decide
      · exact absurd heq hi
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hcontra
      have h1 : σ i ≤ σ' i := hle i
      rw [hcontra] at hi h1
      exact hi (le_antisymm (by revert h1; cases σ' i <;> decide) h1).symm
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have h1 : Spin.up ≤ σ' j := hj ▸ hle j
    revert h1; cases σ' j <;> decide

/-- **A uniform bound** for a local observable: `2 · max |φ|` over the (finite)
support configurations.  Nonnegative, and `≥ 2·|φ σ|` for every `σ`. -/
noncomputable def LocalObservable.monoBound {d : ℕ} (O : LocalObservable d) : ℝ :=
  2 * Finset.univ.sup' Finset.univ_nonempty (fun σ => |O.φ σ|)

/-- The monotone bound is nonnegative. -/
theorem LocalObservable.monoBound_nonneg {d : ℕ} (O : LocalObservable d) : 0 ≤ O.monoBound := by
  unfold LocalObservable.monoBound
  have : (0 : ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty (fun σ => |O.φ σ|) :=
    Finset.le_sup'_of_le _ (Finset.mem_univ (Classical.arbitrary _)) (abs_nonneg _)
  positivity

/-- The monotone bound dominates twice the absolute value of the observable. -/
theorem LocalObservable.two_abs_le_monoBound {d : ℕ} (O : LocalObservable d)
    (σ : Config (↑O.S : Type _)) :
    2 * |O.φ σ| ≤ O.monoBound :=
  mul_le_mul_of_nonneg_left (Finset.le_sup' (fun σ => |O.φ σ|) (Finset.mem_univ σ)) (by norm_num)

/-- **The upper monotone part** of a local observable: `K · rank + φ`, where
`K = monoBound` dominates the variation of `φ` across every covering step, so the
sum is monotone. -/
noncomputable def LocalObservable.upper {d : ℕ} (O : LocalObservable d) :
    LocalMonotoneObservable d where
  S := O.S
  φ := fun σ => O.monoBound * (configUpRank σ : ℝ) + O.φ σ
  mono := by
    intro σ σ' hσσ'
    rcases eq_or_lt_of_le hσσ' with heq | hlt
    · rw [heq]
    · have hcast : (configUpRank σ : ℝ) + 1 ≤ (configUpRank σ' : ℝ) := by
        exact_mod_cast configUpRank_lt_of_lt hlt
      nlinarith [mul_le_mul_of_nonneg_left hcast O.monoBound_nonneg,
        O.two_abs_le_monoBound σ, O.two_abs_le_monoBound σ',
        le_abs_self (O.φ σ), neg_le_abs (O.φ σ')]

/-- **The lower monotone part** of a local observable: `K · rank`, monotone since
`K ≥ 0` and the up-spin count is monotone. -/
noncomputable def LocalObservable.lower {d : ℕ} (O : LocalObservable d) :
    LocalMonotoneObservable d where
  S := O.S
  φ := fun σ => O.monoBound * (configUpRank σ : ℝ)
  mono := fun σ σ' hσσ' =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast configUpRank_mono hσσ') O.monoBound_nonneg

/-- **The monotone-difference decomposition** (the role of FV Lemma 3.19): every
local observable is the difference of its upper and lower monotone parts. -/
theorem LocalObservable.phi_eq_upper_sub_lower {d : ℕ} (O : LocalObservable d)
    (σ : Config (↑O.S : Type _)) :
    O.φ σ = O.upper.φ σ - O.lower.φ σ := by
  simp only [LocalObservable.upper, LocalObservable.lower]; ring

/-! ## The `+` box expectation and its linearity -/

/-- **The `+` box expectation of an arbitrary local observable**: the `+` boundary
expectation on `cubicBox d m` (inner box `cubicBox d n`) of `O.φ` pulled back to
the box configuration. -/
noncomputable def plusBoxObsExpectation {d : ℕ} (n m : ℕ) (J h β : ℝ) (O : LocalObservable d)
    (hS : O.S ⊆ cubicBox d m) : ℝ :=
  plusBoxExpectation d n m J h β (fun σ => O.φ (restrictConfig hS σ))

/-- **The `+` box expectation splits along the monotone-difference decomposition**:
`plusBoxObsExpectation O = plusBoxLocalExpectation O.upper − plusBoxLocalExpectation
O.lower` (linearity of the boundary-condition Gibbs expectation). -/
theorem plusBoxObsExpectation_eq_sub {d : ℕ} (n m : ℕ) (J h β : ℝ) (O : LocalObservable d)
    (hS : O.S ⊆ cubicBox d m) :
    plusBoxObsExpectation n m J h β O hS
      = plusBoxLocalExpectation n m J h β O.upper hS
        - plusBoxLocalExpectation n m J h β O.lower hS := by
  unfold plusBoxObsExpectation plusBoxLocalExpectation plusBoxExpectation
  rw [show (fun σ : Config (↑(cubicBox d m) : Type _) => O.φ (restrictConfig hS σ))
        = (O.upper.lift hS) + (fun σ => (-1 : ℝ) * O.lower.lift hS σ) by
      funext σ
      change O.φ (restrictConfig hS σ) = O.upper.lift hS σ + (-1 : ℝ) * O.lower.lift hS σ
      rw [O.phi_eq_upper_sub_lower (restrictConfig hS σ)]
      change O.upper.φ (restrictConfig hS σ) - O.lower.φ (restrictConfig hS σ)
          = O.upper.φ (restrictConfig hS σ) + (-1 : ℝ) * O.lower.φ (restrictConfig hS σ)
      ring,
    gibbsExpectationBC_add, gibbsExpectationBC_const_mul]
  ring

/-- **Additivity of the `+` box expectation** (same support): the box expectation
of `φ₁ + φ₂` is the sum of the box expectations. -/
theorem plusBoxObsExpectation_add {d : ℕ} (n m : ℕ) (J h β : ℝ)
    {S : Finset (Fin d → ℤ)} (φ₁ φ₂ : Config (↑S : Type _) → ℝ) (hS : S ⊆ cubicBox d m) :
    plusBoxObsExpectation n m J h β ⟨S, fun σ => φ₁ σ + φ₂ σ⟩ hS
      = plusBoxObsExpectation n m J h β ⟨S, φ₁⟩ hS
        + plusBoxObsExpectation n m J h β ⟨S, φ₂⟩ hS := by
  unfold plusBoxObsExpectation plusBoxExpectation
  rw [show (fun σ : Config (↑(cubicBox d m) : Type _) => φ₁ (restrictConfig hS σ)
        + φ₂ (restrictConfig hS σ))
      = (fun σ => φ₁ (restrictConfig hS σ)) + (fun σ => φ₂ (restrictConfig hS σ)) from rfl,
    gibbsExpectationBC_add]

/-- **Scalar homogeneity of the `+` box expectation** (same support). -/
theorem plusBoxObsExpectation_const_mul {d : ℕ} (n m : ℕ) (J h β : ℝ)
    {S : Finset (Fin d → ℤ)} (c : ℝ) (φ : Config (↑S : Type _) → ℝ) (hS : S ⊆ cubicBox d m) :
    plusBoxObsExpectation n m J h β ⟨S, fun σ => c * φ σ⟩ hS
      = c * plusBoxObsExpectation n m J h β ⟨S, φ⟩ hS := by
  unfold plusBoxObsExpectation plusBoxExpectation
  exact gibbsExpectationBC_const_mul _ _ _ _ _ _ c _

/-- **The `+` box expectation of a constant is that constant** (normalisation). -/
theorem plusBoxObsExpectation_const {d : ℕ} (n m : ℕ) (J h β : ℝ)
    {S : Finset (Fin d → ℤ)} (c : ℝ) (hS : S ⊆ cubicBox d m) :
    plusBoxObsExpectation n m J h β ⟨S, fun _ => c⟩ hS = c := by
  unfold plusBoxObsExpectation plusBoxExpectation
  exact gibbsExpectationBC_const _ _ _ _ _ _ c

/-- **Monotonicity of the `+` box expectation** (same support): pointwise `φ₁ ≤ φ₂`
implies the box expectations are ordered (nonnegative-weight average). -/
theorem plusBoxObsExpectation_mono {d : ℕ} (n m : ℕ) (J h β : ℝ)
    {S : Finset (Fin d → ℤ)} {φ₁ φ₂ : Config (↑S : Type _) → ℝ}
    (hle : ∀ σ, φ₁ σ ≤ φ₂ σ) (hS : S ⊆ cubicBox d m) :
    plusBoxObsExpectation n m J h β ⟨S, φ₁⟩ hS ≤ plusBoxObsExpectation n m J h β ⟨S, φ₂⟩ hS := by
  unfold plusBoxObsExpectation plusBoxExpectation gibbsExpectationBC
  have hZ : 0 < partitionFunctionBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d m))
      β (fun _ => J) h (plusBoxInterior d n m) (plusConfig _) := partitionFunctionBC_pos _ _ _ _ _ _
  rw [← div_eq_inv_mul, ← div_eq_inv_mul, div_le_div_iff_of_pos_right hZ]
  exact Finset.sum_le_sum fun σ _ =>
    mul_le_mul_of_nonneg_right (hle (restrictConfig hS σ)) (boltzmannWeightBC_nonneg _ _ _ _ _ _ σ)

/-! ## The infinite-volume `+`-state functional -/

/-- **The infinite-volume `+` expectation of an arbitrary local observable** (the
`+`-state functional, FV Theorem 3.17): the difference of the two monotone limits
from the monotone-difference decomposition.  The screened box expectations converge
to it (`tendsto_plusStateExpectation`). -/
noncomputable def plusStateExpectation {d N : ℕ} (J h β : ℝ) (O : LocalObservable d)
    (hS : O.S ⊆ cubicBox d N) : ℝ :=
  (⨅ k, plusBoxLocalExpectation (N + k) (N + k + 1) J h β O.upper
      (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))))
    - (⨅ k, plusBoxLocalExpectation (N + k) (N + k + 1) J h β O.lower
      (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))))

/-- **The screened `+` box expectations converge to the `+`-state functional**: for
`O.S ⊆ cubicBox d N`,

`plusBoxObsExpectation (N+k) (N+k+1) … O  →  plusStateExpectation … O`   as `k → ∞`.

Each term is the difference of the two monotone screened sequences, which converge
to their infima (`tendsto_plusBoxLocalObservable_infiniteVolume`). -/
theorem tendsto_plusStateExpectation {d N : ℕ} {J h β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (O : LocalObservable d) (hS : O.S ⊆ cubicBox d N) :
    Tendsto (fun k => plusBoxObsExpectation (N + k) (N + k + 1) J h β O
        (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))) atTop
      (nhds (plusStateExpectation J h β O hS)) := by
  have hup := tendsto_plusBoxLocalObservable_infiniteVolume (h := h) hβ hJ O.upper hS
  have hlo := tendsto_plusBoxLocalObservable_infiniteVolume (h := h) hβ hJ O.lower hS
  have heq : (fun k => plusBoxObsExpectation (N + k) (N + k + 1) J h β O
        (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))))
      = (fun k => plusBoxLocalExpectation (N + k) (N + k + 1) J h β O.upper
          (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))
        - plusBoxLocalExpectation (N + k) (N + k + 1) J h β O.lower
          (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))) := by
    funext k; exact plusBoxObsExpectation_eq_sub _ _ J h β O _
  rw [heq]
  exact hup.sub hlo

/-- **Additivity of the `+`-state functional** (same support, FV Thm 3.17): the
`+` state is linear. -/
theorem plusStateExpectation_add {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    {S : Finset (Fin d → ℤ)} (φ₁ φ₂ : Config (↑S : Type _) → ℝ) (hS : S ⊆ cubicBox d N) :
    plusStateExpectation J h β (⟨S, fun σ => φ₁ σ + φ₂ σ⟩ : LocalObservable d) hS
      = plusStateExpectation J h β (⟨S, φ₁⟩ : LocalObservable d) hS
        + plusStateExpectation J h β (⟨S, φ₂⟩ : LocalObservable d) hS := by
  refine tendsto_nhds_unique (tendsto_plusStateExpectation hβ hJ _ hS) ?_
  have h1 := tendsto_plusStateExpectation (h := h) hβ hJ (⟨S, φ₁⟩ : LocalObservable d) hS
  have h2 := tendsto_plusStateExpectation (h := h) hβ hJ (⟨S, φ₂⟩ : LocalObservable d) hS
  have heq : (fun k => plusBoxObsExpectation (N + k) (N + k + 1) J h β
        (⟨S, fun σ => φ₁ σ + φ₂ σ⟩ : LocalObservable d)
        (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))))
      = (fun k => plusBoxObsExpectation (N + k) (N + k + 1) J h β (⟨S, φ₁⟩ : LocalObservable d)
          (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))
        + plusBoxObsExpectation (N + k) (N + k + 1) J h β (⟨S, φ₂⟩ : LocalObservable d)
          (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))) := by
    funext k; exact plusBoxObsExpectation_add _ _ J h β φ₁ φ₂ _
  rw [heq]
  exact h1.add h2

/-- **Scalar homogeneity of the `+`-state functional** (same support). -/
theorem plusStateExpectation_const_mul {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    {S : Finset (Fin d → ℤ)} (c : ℝ) (φ : Config (↑S : Type _) → ℝ) (hS : S ⊆ cubicBox d N) :
    plusStateExpectation J h β (⟨S, fun σ => c * φ σ⟩ : LocalObservable d) hS
      = c * plusStateExpectation J h β (⟨S, φ⟩ : LocalObservable d) hS := by
  refine tendsto_nhds_unique (tendsto_plusStateExpectation hβ hJ _ hS) ?_
  have h1 := tendsto_plusStateExpectation (h := h) hβ hJ (⟨S, φ⟩ : LocalObservable d) hS
  have heq : (fun k => plusBoxObsExpectation (N + k) (N + k + 1) J h β
        (⟨S, fun σ => c * φ σ⟩ : LocalObservable d)
        (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))))
      = (fun k => c * plusBoxObsExpectation (N + k) (N + k + 1) J h β (⟨S, φ⟩ : LocalObservable d)
          (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))) := by
    funext k; exact plusBoxObsExpectation_const_mul _ _ J h β c φ _
  rw [heq]
  exact h1.const_mul c

/-- **Normalisation of the `+`-state functional**: the `+` expectation of a constant
is that constant. -/
theorem plusStateExpectation_const {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    {S : Finset (Fin d → ℤ)} (c : ℝ) (hS : S ⊆ cubicBox d N) :
    plusStateExpectation J h β (⟨S, fun _ => c⟩ : LocalObservable d) hS = c := by
  refine tendsto_nhds_unique (tendsto_plusStateExpectation hβ hJ _ hS) ?_
  have heq : (fun k => plusBoxObsExpectation (N + k) (N + k + 1) J h β
        (⟨S, fun _ => c⟩ : LocalObservable d)
        (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))) = fun _ => c := by
    funext k; exact plusBoxObsExpectation_const _ _ J h β c _
  rw [heq]
  exact tendsto_const_nhds

/-- **Positivity of the `+`-state functional**: the `+` expectation of a
nonnegative observable is nonnegative. -/
theorem plusStateExpectation_nonneg {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    {S : Finset (Fin d → ℤ)} {φ : Config (↑S : Type _) → ℝ} (hφ : ∀ σ, 0 ≤ φ σ)
    (hS : S ⊆ cubicBox d N) :
    0 ≤ plusStateExpectation J h β (⟨S, φ⟩ : LocalObservable d) hS := by
  refine ge_of_tendsto' (tendsto_plusStateExpectation hβ hJ (⟨S, φ⟩ : LocalObservable d) hS)
    (fun k => ?_)
  unfold plusBoxObsExpectation plusBoxExpectation
  exact gibbsExpectationBC_ge_of_forall_ge _ _ _ _ _ _ (fun σ => hφ _)

/-- **Monotonicity of the `+`-state functional** (same support): pointwise `φ₁ ≤ φ₂`
implies `+` expectations are ordered. -/
theorem plusStateExpectation_mono {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    {S : Finset (Fin d → ℤ)} {φ₁ φ₂ : Config (↑S : Type _) → ℝ} (hle : ∀ σ, φ₁ σ ≤ φ₂ σ)
    (hS : S ⊆ cubicBox d N) :
    plusStateExpectation J h β (⟨S, φ₁⟩ : LocalObservable d) hS
      ≤ plusStateExpectation J h β (⟨S, φ₂⟩ : LocalObservable d) hS :=
  le_of_tendsto_of_tendsto'
    (tendsto_plusStateExpectation hβ hJ (⟨S, φ₁⟩ : LocalObservable d) hS)
    (tendsto_plusStateExpectation hβ hJ (⟨S, φ₂⟩ : LocalObservable d) hS)
    (fun _ => plusBoxObsExpectation_mono _ _ J h β hle _)

/-- **Consistency with the monotone limit**: for a monotone observable the
`+`-state functional coincides with the infimum limit
(`tendsto_plusBoxLocalObservable_infiniteVolume`). -/
theorem plusStateExpectation_of_monotone {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d N) :
    plusStateExpectation J h β (⟨O.S, O.φ⟩ : LocalObservable d) hS
      = ⨅ k, plusBoxLocalExpectation (N + k) (N + k + 1) J h β O
          (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))) := by
  refine tendsto_nhds_unique (tendsto_plusStateExpectation hβ hJ _ hS) ?_
  have hmono := tendsto_plusBoxLocalObservable_infiniteVolume (h := h) hβ hJ O hS
  have heq : (fun k => plusBoxObsExpectation (N + k) (N + k + 1) J h β
        (⟨O.S, O.φ⟩ : LocalObservable d)
        (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))))
      = (fun k => plusBoxLocalExpectation (N + k) (N + k + 1) J h β O
          (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))) := rfl
  rw [heq]; exact hmono

end Ambient

end IsingModel
