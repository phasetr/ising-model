import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMassDistUpper

/-!
# GJ §17.5 Lemma 17.5.2 — FULL high-temperature upper bound `m(σ) ≤ C·m⁻(σ)`

This module extends the restricted upper bound of
`GlobalPseudoMassDistUpper.lean` from the strict window `βJ·2d < 1/2` to the
**full high-temperature window** `βJ·2d < 1`, against the faithful
distance-parametrized system pseudo-mass `globalPseudoMassDist`.

## Why the `1/2` barrier was only an artefact

The restricted route builds the pair-uniform pseudo-mass lower bound
`M ≤ pseudoMassFromParamsAtPairDist` via the Simon–Lieb trichotomy, whose
*adjacent* (nearest-neighbour, `dist = 1`) branch was discharged through the
finite-susceptibility ceiling `corr ≤ B := βJ·2d/(1−βJ·2d)` and the rate
constraint `M ≤ −log B`.  That forces `B < 1`, i.e. `βJ·2d < 1/2`.

But the bridge's `bound` field only needs `corr ≤ pseudoMassG α r (M·dist/r)`,
which at `dist = 1` is `corr ≤ 2·exp(−M)/(1+M^α)`.  Since
`corr_adjacent ≤ 1` **always** (`correlationInfinite_latticeGraph_le_one`) and
`2·exp(−M)/(1+M^α) → 2` as `M → 0⁺`, this holds **unconditionally** for any
`M ≤ 1/3`:
`(1+M^α)·exp(M) ≤ (1+M)·exp(M) ≤ (1+M)/(1−M) ≤ 2` (via `Real.add_one_le_exp`).
No susceptibility ceiling, no `B < 1`.

The non-adjacent (`dist ≥ 2`) branches already use Simon–Lieb decay on the whole
`βJ·2d < 1`.  So choosing the pair-uniform rate
`M = min (1/3) (simonLiebRate β J d / (2(α+1)))` discharges all three branches on
`βJ·2d < 1`, yielding the full-window pair-uniform lower bound and hence the
full-window upper bound `latticeMass ≤ (−log(tanh(βJ))/M) · globalPseudoMassDist`.

This is the **qualitative** Lemma 17.5.2 upper bound (some finite `C`), which is
all the lemma asserts; the *sharp* `C` (the true correlation length, item C
#4271) is the genuinely transfer-matrix-bound quantity and remains out of scope.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp.~311--312;
  §5.1, pp.~73--74.
-/

namespace IsingModel
namespace Ambient

open Set Real

/-- **`pseudoMassG ≥ 1` at the adjacent profile point for small rates**: for
`1 ≤ α`, `0 < r`, `0 ≤ M ≤ 1/3`, the pseudo-mass profile at `t = M/r` (so the
profile argument `t·r = M`, the adjacent `dist = 1` value) satisfies
`1 ≤ pseudoMassG α r (M/r) = 2·exp(−M)/(1+M^α)`.

Proof: `1 ≤ 2·exp(−M)/(1+M^α) ⟺ 1 + M^α ≤ 2·exp(−M)`; then
`1 + M^α ≤ 1 + M` (`M^α ≤ M` for `0 ≤ M ≤ 1`, `α ≥ 1`),
`1 + M ≤ 2 − 2M` (`M ≤ 1/3`), and `2 − 2M = 2(1 − M) ≤ 2·exp(−M)`
(`1 − M ≤ exp(−M)` from `Real.add_one_le_exp`). -/
theorem pseudoMassG_one_le_of_le_third {α : ℕ} (hα : 1 ≤ α) {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hM_third : M ≤ 1 / 3) :
    1 ≤ pseudoMassG α r (M / r) := by
  have hMr_eq : M / r * r = M := div_mul_cancel₀ M (ne_of_gt hr)
  unfold pseudoMassG
  rw [hMr_eq]
  -- Goal: `1 ≤ 2 * exp (-M) / (1 + M ^ α)`.
  have hM_le_one : M ≤ 1 := by linarith
  have hpow_le : M ^ α ≤ M :=
    pow_le_of_le_one hM hM_le_one (Nat.one_le_iff_ne_zero.mp hα)
  have hpow_nn : (0 : ℝ) ≤ M ^ α := pow_nonneg hM α
  have hden_pos : (0 : ℝ) < 1 + M ^ α := by linarith
  have hexp : 1 - M ≤ Real.exp (-M) := by
    have := Real.add_one_le_exp (-M); linarith
  rw [le_div_iff₀ hden_pos, one_mul]
  -- Goal: `1 + M ^ α ≤ 2 * exp (-M)`.
  nlinarith [hexp, hpow_le, hM_third]

/-- **Adjacent-pair `bridge.bound` from the universal `corr ≤ 1` ceiling**
(full-window replacement for the susceptibility-ceiling adjacent input).

For a nearest-neighbour pair (`dist(0, w) = 1`), the zero-anchored bound
`M ≤ pseudoMassFromParamsAtPair · r` follows from the universal correlation
ceiling `corr ≤ 1` together with `pseudoMassG_one_le_of_le_third` (needs only
`M ≤ 1/3`), via `pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_pseudoMassG`.
No `βJ·2d < 1/2` susceptibility ceiling is used. -/
theorem pseudoMassFromParamsAtPair_zero_le_of_corr_le_one_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {M : ℝ} (hM : 0 ≤ M) (hM_third : M ≤ 1 / 3)
    {w : Fin d → ℤ} (hdist : latticeDistance d 0 w = 1)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
              ∈ Set.Ioo (0 : ℝ) 2) :
    M ≤ pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  have hdist_cast : (latticeDistance d 0 w : ℝ) = 1 := by rw [hdist]; norm_cast
  have hcorr_le_one :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w} ≤ 1 :=
    correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p {0, w}
  have hle : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
      ≤ pseudoMassG α r (M * (latticeDistance d 0 w : ℝ) / r) := by
    have harg : M * (latticeDistance d 0 w : ℝ) / r = M / r := by
      rw [hdist_cast, mul_one]
    rw [harg]
    exact hcorr_le_one.trans (pseudoMassG_one_le_of_le_third hα hr hM hM_third)
  have h := pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_pseudoMassG
    hα hr d Λ p hM w hcorr hle
  rw [hdist_cast, mul_one] at h
  exact h

/-- **Combined zero-anchored `bridge.bound` from the full Simon–Lieb trichotomy
with the `corr ≤ 1` adjacent input** (full-window `_unit` variant of
`pseudoMassFromParamsAtPair_M_dist_zero_le_simonLieb_trichotomy_combined`).

Same case split (adjacent / small / large), but the adjacent branch is
discharged unconditionally from `corr ≤ 1` (requiring `M ≤ 1/3`) rather than from
an `exp(−M)` adjacent hypothesis. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_simonLieb_trichotomy_combined_unit
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_third : M ≤ 1 / 3)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    {w : Fin d → ℤ} (hw_ne : w ≠ 0)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
                (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
              ∈ Set.Ioo (0 : ℝ) 2) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  have hMrate_small : M ≤ simonLiebRate β J d / 2 := by
    have hfactor : (1 : ℝ) ≤ (α : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg α)
    have hM_le_scaled : M ≤ ((α : ℝ) + 1) * M := by nlinarith [hfactor, hM_pos.le]
    exact hM_le_scaled.trans hMrate
  by_cases h_eq_one : latticeDistance d 0 w = 1
  · have hdist_cast : (latticeDistance d 0 w : ℝ) = 1 := by rw [h_eq_one]; norm_cast
    have h := pseudoMassFromParamsAtPair_zero_le_of_corr_le_one_adjacent
      hα hr d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      hM_pos.le hM_third h_eq_one hcorr
    rw [hdist_cast, mul_one]
    exact h
  · have h_ge_two : 2 ≤ latticeDistance d 0 w := by
      have hdist_pos : 0 < latticeDistance d 0 w := by
        apply Nat.pos_of_ne_zero
        intro h_eq_zero
        exact hw_ne ((IsingModel.latticeDistance_eq_zero_iff d 0 w).mp h_eq_zero).symm
      omega
    by_cases hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1
    · exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_simonLieb_smallReg
        hα hr d hβJ hβJd_pos hβJd_le hM_pos.le hMrate_small h_ge_two hsmall hcorr
    · have hlarge : 1 ≤ M * (latticeDistance d 0 w : ℝ) := (lt_of_not_ge hsmall).le
      exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_simonLieb_largeReg
        hα hr d hβJ hβJd_pos hβJd_le hMrate h_ge_two hlarge hcorr

/-- **Zero-anchored full-trichotomy bound (`∀ w ≠ 0`) with the `corr ≤ 1`
adjacent input** (full-window `_unit` variant of
`pseudoMassFromParamsAtPair_zero_anchored_simonLieb_trichotomy_uniform`). -/
theorem pseudoMassFromParamsAtPair_zero_anchored_simonLieb_trichotomy_uniform_unit
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_third : M ≤ 1 / 3)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ∈ Set.Ioo (0 : ℝ) 2) :
    ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  intro w hw_ne
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_simonLieb_trichotomy_combined_unit
    hα hr d hβJ hβJd_pos hβJd_le hM_pos hM_third hMrate hw_ne (h_corr_active w hw_ne)

/-- **All-pair full-trichotomy `bridge.bound` with the `corr ≤ 1` adjacent
input** (full-window `_unit` variant of
`pseudoMassFromParamsAtPair_all_pair_simonLieb_trichotomy_bound`).

Composes the zero-anchored uniform bound with the translation lift
`pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored`. -/
theorem pseudoMassFromParamsAtPair_all_pair_simonLieb_trichotomy_bound_unit
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_third : M ≤ 1 / 3)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ∈ Set.Ioo (0 : ℝ) 2) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      M * (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  have h_zero_anchored :=
    pseudoMassFromParamsAtPair_zero_anchored_simonLieb_trichotomy_uniform_unit
      hα hr d hβJ hβJd_pos hβJd_le hM_pos hM_third hMrate h_corr_active
  exact pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored
    hα hr d hJ hβ h_zero_anchored

/-- **Unconditional full-window `PseudoMassLatticeDistanceBridge`**
`0 < βJ·2d < 1` (full-window `_unit` variant of
`pseudoMassLatticeDistanceBridge_of_high_temp`).

The pair-uniform rate is `M := min (1/3) (simonLiebRate β J d / (2(α+1)))`; the
adjacent input is the universal `corr ≤ 1` ceiling, so **no** `βJ·2d < 1/2` is
required. -/
noncomputable def pseudoMassLatticeDistanceBridge_of_high_temp_full
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt1 : β * J * (2 * d) < 1) :
    PseudoMassLatticeDistanceBridge hα hr d J β := by
  have hSL_pos : 0 < simonLiebRate β J d := simonLiebRate_pos hβJd_pos hβJd_lt1
  have hαR_pos : (0 : ℝ) < (α : ℝ) + 1 := by positivity
  have hSLfrac_pos : 0 < simonLiebRate β J d / (2 * ((α : ℝ) + 1)) := by positivity
  set M := min (1 / 3) (simonLiebRate β J d / (2 * ((α : ℝ) + 1))) with hM_def
  have hM_pos : 0 < M := lt_min (by norm_num) hSLfrac_pos
  have hM_third : M ≤ 1 / 3 := min_le_left _ _
  have hM_le_SLfrac : M ≤ simonLiebRate β J d / (2 * ((α : ℝ) + 1)) := min_le_right _ _
  have hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2 := by
    calc ((α : ℝ) + 1) * M
        ≤ ((α : ℝ) + 1) * (simonLiebRate β J d / (2 * ((α : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hM_le_SLfrac hαR_pos.le
      _ = simonLiebRate β J d / 2 := by field_simp
  exact PseudoMassLatticeDistanceBridge_of_bound_active hα hr d hM_pos
    ⟨hJ, le_refl 0, hβ⟩
    (pseudoMassFromParamsAtPair_all_pair_simonLieb_trichotomy_bound_unit
      hα hr d hJ hβ hβJd_pos (le_of_lt hβJd_lt1) hM_pos hM_third hMrate
      (fun w hw_ne =>
        correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos 0 w
          (fun h => hw_ne h.symm)))
    (correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos)

/-- **Full-window pair-uniform lower rate** for the distance-parametrized
pseudo-mass: `M = min (1/3) (simonLiebRate β J d / (2(α+1)))`. -/
noncomputable def globalPseudoMassDistFullRate (α d : ℕ) (J β : ℝ) : ℝ :=
  min (1 / 3) (simonLiebRate β J d / (2 * ((α : ℝ) + 1)))

/-- **Positivity of the full-window rate** on `0 < βJ·2d < 1`. -/
theorem globalPseudoMassDistFullRate_pos
    {α d : ℕ} {J β : ℝ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt1 : β * J * (2 * d) < 1) :
    0 < globalPseudoMassDistFullRate α d J β := by
  have hSL_pos : 0 < simonLiebRate β J d := simonLiebRate_pos hβJd_pos hβJd_lt1
  have hSLfrac_pos : 0 < simonLiebRate β J d / (2 * ((α : ℝ) + 1)) := by positivity
  unfold globalPseudoMassDistFullRate
  exact lt_min (by norm_num) hSLfrac_pos

/-- **Full-window pair-uniform lower bound on the distance-parametrized per-pair
pseudo-mass**: for every distinct pair in `0 < βJ·2d < 1`, the full-window rate
bounds `pseudoMassFromParamsAtPairDist`.

Instantiates the full-window bridge at the profile radius `r = latticeDistance d
x z` and divides its per-pair bound by `0 < dist`. -/
theorem globalPseudoMassDistFullRate_le_pseudoMassFromParamsAtPairDist
    {α d : ℕ} (hα : 1 ≤ α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d))
    (hβJd_lt1 : β * J * (2 * d) < 1)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    globalPseudoMassDistFullRate α d J β ≤
      pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hdist : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
    have hne : IsingModel.latticeDistance d x z ≠ 0 :=
      fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h)
    exact_mod_cast Nat.pos_of_ne_zero hne
  -- The full-window rate is exactly the bridge's `M_inf` at radius `dist`.
  have hM_pos : 0 < globalPseudoMassDistFullRate α d J β :=
    globalPseudoMassDistFullRate_pos hβJd_pos hβJd_lt1
  have hSL_pos : 0 < simonLiebRate β J d := simonLiebRate_pos hβJd_pos hβJd_lt1
  have hαR_pos : (0 : ℝ) < (α : ℝ) + 1 := by positivity
  have hM_third : globalPseudoMassDistFullRate α d J β ≤ 1 / 3 := by
    unfold globalPseudoMassDistFullRate; exact min_le_left _ _
  have hM_le_SLfrac :
      globalPseudoMassDistFullRate α d J β
        ≤ simonLiebRate β J d / (2 * ((α : ℝ) + 1)) := by
    unfold globalPseudoMassDistFullRate; exact min_le_right _ _
  have hMrate :
      ((α : ℝ) + 1) * globalPseudoMassDistFullRate α d J β
        ≤ simonLiebRate β J d / 2 := by
    calc ((α : ℝ) + 1) * globalPseudoMassDistFullRate α d J β
        ≤ ((α : ℝ) + 1) * (simonLiebRate β J d / (2 * ((α : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hM_le_SLfrac hαR_pos.le
      _ = simonLiebRate β J d / 2 := by field_simp
  have hbound :
      globalPseudoMassDistFullRate α d J β
          * (IsingModel.latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hdist d (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) x z
          * (IsingModel.latticeDistance d x z : ℝ) :=
    pseudoMassFromParamsAtPair_all_pair_simonLieb_trichotomy_bound_unit
      hα hdist d hJ hβ hβJd_pos (le_of_lt hβJd_lt1) hM_pos hM_third hMrate
      (fun w hw_ne =>
        correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos 0 w
          (fun h => hw_ne h.symm))
      x z hxz
  have hcancel :
      globalPseudoMassDistFullRate α d J β ≤
        pseudoMassFromParamsAtPair hα hdist d (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    le_of_mul_le_mul_right hbound hdist
  rw [pseudoMassFromParamsAtPairDist_of_ne hα (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) hxz hdist]
  exact hcancel

/-- **Full-window pair-uniform lower bound for `globalPseudoMassDist`** on
`0 < βJ·2d < 1`. -/
theorem globalPseudoMassDistFullRate_le_globalPseudoMassDist
    {α d : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d))
    (hβJd_lt1 : β * J * (2 * d) < 1) :
    globalPseudoMassDistFullRate α d J β ≤
      globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  unfold globalPseudoMassDist
  refine le_csInf
    (globalPseudoMassDistSet_nonempty_of_high_temp hα hd hβ hβJ_pos) ?_
  rintro m ⟨x, z, hactive, rfl⟩
  exact globalPseudoMassDistFullRate_le_pseudoMassFromParamsAtPairDist
    hα hJ hβ hβJ_pos hβJd_pos hβJd_lt1 hactive.1

/-- **Full-window upper constant** `C = (−log(tanh(βJ)))/M` for GJ §17.5
Lemma 17.5.2, with `M = globalPseudoMassDistFullRate`. -/
noncomputable def globalPseudoMassDistFullUpperConst (α d : ℕ) (J β : ℝ) : ℝ :=
  (-Real.log (Real.tanh (β * J))) / globalPseudoMassDistFullRate α d J β

/-- **GJ §17.5 Lemma 17.5.2 FULL high-temperature upper bound** `m(σ) ≤ C·m⁻(σ)`:
on the **full** high-temperature window `βJ·2d < 1` of the cubic exhaustion, the
lattice mass is dominated by the full-window upper constant times the faithful
distance-parametrized system pseudo-mass.

This extends `latticeMass_le_globalPseudoMassDist_restrictedUpper` from
`βJ·2d < 1/2` to the whole high-temperature regime, using the universal
`corr ≤ 1` adjacent ceiling (`pseudoMassG_one_le_of_le_third`) instead of the
susceptibility ceiling. -/
theorem latticeMass_le_globalPseudoMassDist_fullUpper
    {α d : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hβJd_lt1 : β * J * (2 * d) < 1) :
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) ≤
      ENNReal.ofReal (globalPseudoMassDistFullUpperConst α d J β) *
        ENNReal.ofReal
          (globalPseudoMassDist hα (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ)) := by
  have hβJ_pos : 0 < β * J := mul_pos hβ hJ
  have hβJd_pos : 0 < β * J * (2 * d) := by
    have hd' : (0 : ℝ) < (2 * d : ℕ) := by exact_mod_cast (by omega : 0 < 2 * d)
    have : (0 : ℝ) < β * J * ((2 * d : ℕ) : ℝ) := mul_pos hβJ_pos hd'
    simpa using this
  have hgpmd :
      globalPseudoMassDistFullRate α d J β ≤
        globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) :=
    globalPseudoMassDistFullRate_le_globalPseudoMassDist
      hα hd hJ.le hβ hβJ_pos hβJd_pos hβJd_lt1
  have hM_pos : 0 < globalPseudoMassDistFullRate α d J β :=
    globalPseudoMassDistFullRate_pos hβJd_pos hβJd_lt1
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβJ_pos) (Real.cosh_pos _)
  have hB_nonneg : 0 ≤ -Real.log (Real.tanh (β * J)) := by
    have hlog := Real.log_neg htanh_pos (Real.tanh_lt_one _); linarith
  have hC_nonneg : 0 ≤ globalPseudoMassDistFullUpperConst α d J β := by
    unfold globalPseudoMassDistFullUpperConst
    exact div_nonneg hB_nonneg hM_pos.le
  have hBeq :
      -Real.log (Real.tanh (β * J))
        = globalPseudoMassDistFullUpperConst α d J β
            * globalPseudoMassDistFullRate α d J β := by
    unfold globalPseudoMassDistFullUpperConst
    rw [div_mul_cancel₀ _ (ne_of_gt hM_pos)]
  calc
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        ≤ ENNReal.ofReal (-Real.log (Real.tanh (β * J))) :=
          latticeMass_le_neg_log_tanh_betaJ hd hJ hβ
    _ = ENNReal.ofReal (globalPseudoMassDistFullUpperConst α d J β
          * globalPseudoMassDistFullRate α d J β) := by rw [hBeq]
    _ = ENNReal.ofReal (globalPseudoMassDistFullUpperConst α d J β)
          * ENNReal.ofReal (globalPseudoMassDistFullRate α d J β) :=
          ENNReal.ofReal_mul hC_nonneg
    _ ≤ ENNReal.ofReal (globalPseudoMassDistFullUpperConst α d J β)
          * ENNReal.ofReal
              (globalPseudoMassDist hα (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ)) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal hgpmd) _

/-- **GJ §17.5 Lemma 17.5.2 faithful FULL-window sandwich**
`m⁻(σ) ≤ m(σ) ≤ C·m⁻(σ)`: on the **full** high-temperature window
`βJ·2d < 1` of the cubic exhaustion, the lattice mass is sandwiched between the
faithful distance-parametrized system pseudo-mass and the full-window upper
constant times that same pseudo-mass.

Bundles the unconditional lower bound `globalPseudoMassDist_le_latticeMass` with
the full-window upper bound `latticeMass_le_globalPseudoMassDist_fullUpper`.  This
closes the upper side on the whole high-temperature regime (vs the `βJ·2d < 1/2`
restricted version `globalPseudoMassDist_restrictedSandwich`). -/
theorem globalPseudoMassDist_fullSandwich
    {α d : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hβJd_lt1 : β * J * (2 * d) < 1) :
    ENNReal.ofReal
        (globalPseudoMassDist hα (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ)) ≤
      latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) ≤
      ENNReal.ofReal (globalPseudoMassDistFullUpperConst α d J β) *
        ENNReal.ofReal
          (globalPseudoMassDist hα (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨globalPseudoMassDist_le_latticeMass hα (cubicExhaustion d) hJ.le hβ,
   latticeMass_le_globalPseudoMassDist_fullUpper hα hd hJ hβ hβJd_lt1⟩

end Ambient
end IsingModel
