import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivative
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivativeSuscSq
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivativeHighTemp
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Analysis.BoundedVariation

/-!
# High-temperature Lipschitz and uniform convergence wrappers at ℤ^d

This module contains the concrete §17.5 high-temperature Lipschitz layer split
from the original `Inequalities` module: finite-stage β/J Lipschitz helpers,
infinite-volume compact Lipschitz and continuity wrappers, compact uniform
convergence, a.e. differentiability / locally bounded variation on compact and
open high-temperature intervals, open-interval continuity, locally uniform
convergence, and interior `ContinuousAt` wrappers.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Helper**: uniform norm bound for each `corr_n` on `[a, b]` (Step 167, GJ §17.5).

For each stage `n` and any β₁ β₂ ∈ [a, b] (with `0 < a ≤ b` and `bJ·2d < 1`):
`‖corr_n(β₂) - corr_n(β₁)‖ ≤ (J·M² + J·4d) · ‖β₂ - β₁‖`
where `M = bJ·2d/(1-bJ·2d)`.

Proof: MVT (`Convex.norm_image_sub_le_of_norm_deriv_le`).
Each derivative `d_β` satisfies `0 ≤ d_β ≤ C`:
- `d_β ≥ 0`: monotonicity (`correlation_monotoneOn_beta`) + `HasDerivWithinAt.nonneg_of_monotoneOn`.
- `d_β ≤ C`: Step 166 + `susceptibilityInfinite_latticeGraph_le_of_high_temp_gen`. -/
lemma inducedLatticeGraph_correlation_norm_sub_le
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (β₁ β₂ : ℝ) (h₁ : β₁ ∈ Set.Icc a b) (h₂ : β₂ ∈ Set.Icc a b) :
    let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    ‖IsingModel.correlation G (⟨J, 0, β₂⟩ : IsingParams ℝ) {r, s} -
     IsingModel.correlation G (⟨J, 0, β₁⟩ : IsingParams ℝ) {r, s}‖ ≤
    (J * M ^ 2 + J * (4 * ↑d)) * ‖β₂ - β₁‖ := by
  intro G M
  have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
  have hb_pos : 0 < b := ha.trans_le hab
  have hM_nn : 0 ≤ M :=
    div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ) (Nat.cast_nonneg _)) hdenom_b.le
  have hC_nn : 0 ≤ J * M ^ 2 + J * (4 * ↑d) :=
    add_nonneg (mul_nonneg hJ (pow_nonneg hM_nn 2))
               (mul_nonneg hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  apply (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
    (f := fun β' => IsingModel.correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s})
    (C := J * M ^ 2 + J * (4 * ↑d))
  · -- DifferentiableAt at each β ∈ [a, b]
    intro β _
    exact (IsingModel.hasDerivAt_correlation_beta G J β {r, s}).differentiableAt
  · -- ‖deriv f β‖ ≤ C at each β ∈ [a, b]
    intro β hβ
    -- Get the derivative and its HasDerivAt witness
    obtain ⟨dval, hd, hbound⟩ :=
      inducedLatticeGraph_beta_deriv_le_susc_sq_high_temp Λ J β hJ
        (ha.trans_le hβ.1)
        (by have : β ≤ b := hβ.2; nlinarith [mul_le_mul_of_nonneg_right this
              (mul_nonneg hJ (Nat.cast_nonneg (2 * d)))])
        n r s hrs
    -- deriv f β = dval
    have hdeq : deriv (fun β' => IsingModel.correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) β
                = dval := hd.deriv
    -- dval ≥ 0 from monotonicity
    have hβ_pos : 0 < β := ha.trans_le hβ.1
    have hmono : MonotoneOn
        (fun β' => IsingModel.correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) (Set.Ici 0) :=
      IsingModel.correlation_monotoneOn_beta G J hJ {r, s}
    have hacc : AccPt β (Filter.principal (Set.Ici 0)) := by
      rw [accPt_principal_iff_nhdsWithin]
      exact (right_nhdsWithin_Ioo_neBot hβ_pos).mono
        (nhdsWithin_mono β (fun x hx => ⟨le_of_lt hx.1, ne_of_lt hx.2⟩))
    have hdnn : 0 ≤ dval :=
      hd.hasDerivWithinAt.nonneg_of_monotoneOn hacc hmono
    -- dval ≤ C from susceptibility bound
    have hβJ : 0 ≤ β * J := mul_nonneg hβ_pos.le hJ
    have hlt_β : β * J * ↑(2 * d) < 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hβ.2
                  (mul_nonneg hJ (Nat.cast_nonneg (2 * d)))]
    have hsusc_r : susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val ≤ M := by
      calc susceptibilityInfinite _ Λ _ r.val
          ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
            IsingModel.Ambient.susceptibilityInfinite_latticeGraph_le_of_high_temp_gen
              Λ hβJ hlt_β r.val
        _ ≤ M := by
            have hdenom_β : 0 < 1 - β * J * ↑(2 * d) := by linarith
            rw [div_le_div_iff₀ hdenom_β hdenom_b]
            nlinarith [mul_le_mul_of_nonneg_right hβ.2
                        (mul_nonneg hJ (Nat.cast_nonneg (2 * d)))]
    have hsusc_s : susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val ≤ M := by
      calc susceptibilityInfinite _ Λ _ s.val
          ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
            IsingModel.Ambient.susceptibilityInfinite_latticeGraph_le_of_high_temp_gen
              Λ hβJ hlt_β s.val
        _ ≤ M := by
            have hdenom_β : 0 < 1 - β * J * ↑(2 * d) := by linarith
            rw [div_le_div_iff₀ hdenom_β hdenom_b]
            nlinarith [mul_le_mul_of_nonneg_right hβ.2
                        (mul_nonneg hJ (Nat.cast_nonneg (2 * d)))]
    have hsusc_r_nn : 0 ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val :=
      IsingModel.Ambient.susceptibilityInfinite_nonneg _ Λ _ ⟨hJ, le_refl 0, hβ_pos⟩ _
    have hsusc_s_nn : 0 ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val :=
      IsingModel.Ambient.susceptibilityInfinite_nonneg _ Λ _ ⟨hJ, le_refl 0, hβ_pos⟩ _
    have hdval_le : dval ≤ J * M ^ 2 + J * (4 * ↑d) :=
      calc dval ≤ J * susceptibilityInfinite _ Λ _ r.val *
                  susceptibilityInfinite _ Λ _ s.val + J * (4 * ↑d) := hbound
           _ ≤ J * M ^ 2 + J * (4 * ↑d) := by
                nlinarith [mul_le_mul hsusc_r hsusc_s hsusc_s_nn hM_nn,
                           mul_nonneg hJ (pow_nonneg hM_nn 2)]
    -- Conclude ‖dval‖ ≤ C
    rw [hdeq, Real.norm_of_nonneg hdnn]
    exact hdval_le
  · exact h₁
  · exact h₂

/-- **Helper**: uniform norm bound for each `corr_n` on `[a, b]` in J (Step 221).

For each stage `n` and any J₁ J₂ ∈ [a, b] (with `0 < a ≤ b` and `bβ·2d < 1`):
`‖corr_n(J₂) - corr_n(J₁)‖ ≤ (β·M² + β·4d) · ‖J₂ - J₁‖`
where `M = bβ·2d/(1-bβ·2d)`.

Direct J-direction analogue of `inducedLatticeGraph_correlation_norm_sub_le` (Step 167).
Proof: MVT (`Convex.norm_image_sub_le_of_norm_deriv_le`).
Each derivative `d_J` satisfies `0 ≤ d_J ≤ C`:
- `d_J ≥ 0`: `correlation_monotone_J` at h=0 + `HasDerivWithinAt.nonneg_of_monotoneOn`.
- `d_J ≤ C`: Step 220 + `susceptibilityInfinite_latticeGraph_le_of_high_temp_gen`. -/
lemma inducedLatticeGraph_correlation_norm_sub_le_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (J₁ J₂ : ℝ) (h₁ : J₁ ∈ Set.Icc a b) (h₂ : J₂ ∈ Set.Icc a b) :
    let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    ‖IsingModel.correlation G (⟨J₂, 0, β⟩ : IsingParams ℝ) {r, s} -
     IsingModel.correlation G (⟨J₁, 0, β⟩ : IsingParams ℝ) {r, s}‖ ≤
    (β * M ^ 2 + β * (4 * ↑d)) * ‖J₂ - J₁‖ := by
  intro G M
  have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
  have hb_pos : 0 < b := ha.trans_le hab
  have hM_nn : 0 ≤ M :=
    div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le) (Nat.cast_nonneg _)) hdenom_b.le
  have hC_nn : 0 ≤ β * M ^ 2 + β * (4 * ↑d) :=
    add_nonneg (mul_nonneg hβ.le (pow_nonneg hM_nn 2))
               (mul_nonneg hβ.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  apply (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
    (f := fun J' => IsingModel.correlation G (⟨J', 0, β⟩ : IsingParams ℝ) {r, s})
    (C := β * M ^ 2 + β * (4 * ↑d))
  · intro J _
    exact (IsingModel.hasDerivAt_correlation_J G J 0 β {r, s}).differentiableAt
  · intro J hJ_mem
    obtain ⟨dval, hd, hbound⟩ :=
      inducedLatticeGraph_J_deriv_le_susc_sq_high_temp Λ J β
        (le_of_lt (ha.trans_le hJ_mem.1))
        hβ
        (by have : J ≤ b := hJ_mem.2; nlinarith [mul_le_mul_of_nonneg_right this
              (mul_nonneg hβ.le (Nat.cast_nonneg (2 * d)))])
        n r s hrs
    have hdeq : deriv (fun J' => IsingModel.correlation G (⟨J', 0, β⟩ : IsingParams ℝ) {r, s}) J
                = dval := hd.deriv
    have hJ_pos : 0 < J := ha.trans_le hJ_mem.1
    -- Monotonicity in J at h = 0
    have hmono : MonotoneOn
        (fun J' => IsingModel.correlation G (⟨J', 0, β⟩ : IsingParams ℝ) {r, s})
        (Set.Ici 0) :=
      IsingModel.correlation_monotone_J G 0 (le_refl 0) β hβ {r, s}
    have hacc : AccPt J (Filter.principal (Set.Ici 0)) := by
      rw [accPt_principal_iff_nhdsWithin]
      exact (right_nhdsWithin_Ioo_neBot hJ_pos).mono
        (nhdsWithin_mono J (fun x hx => ⟨le_of_lt hx.1, ne_of_lt hx.2⟩))
    have hdnn : 0 ≤ dval :=
      hd.hasDerivWithinAt.nonneg_of_monotoneOn hacc hmono
    have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ_pos.le
    have hlt_J : β * J * ↑(2 * d) < 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hJ_mem.2
                  (mul_nonneg hβ.le (Nat.cast_nonneg (2 * d)))]
    have hsusc_r : susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val ≤ M := by
      calc susceptibilityInfinite _ Λ _ r.val
          ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
            IsingModel.Ambient.susceptibilityInfinite_latticeGraph_le_of_high_temp_gen
              Λ hβJ hlt_J r.val
        _ ≤ M := by
            have hdenom_J : 0 < 1 - β * J * ↑(2 * d) := by linarith
            rw [div_le_div_iff₀ hdenom_J hdenom_b]
            nlinarith [mul_le_mul_of_nonneg_right hJ_mem.2
                        (mul_nonneg hβ.le (Nat.cast_nonneg (2 * d)))]
    have hsusc_s : susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val ≤ M := by
      calc susceptibilityInfinite _ Λ _ s.val
          ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
            IsingModel.Ambient.susceptibilityInfinite_latticeGraph_le_of_high_temp_gen
              Λ hβJ hlt_J s.val
        _ ≤ M := by
            have hdenom_J : 0 < 1 - β * J * ↑(2 * d) := by linarith
            rw [div_le_div_iff₀ hdenom_J hdenom_b]
            nlinarith [mul_le_mul_of_nonneg_right hJ_mem.2
                        (mul_nonneg hβ.le (Nat.cast_nonneg (2 * d)))]
    have hsusc_r_nn : 0 ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val :=
      IsingModel.Ambient.susceptibilityInfinite_nonneg _ Λ _ ⟨hJ_pos.le, le_refl 0, hβ⟩ _
    have hsusc_s_nn : 0 ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val :=
      IsingModel.Ambient.susceptibilityInfinite_nonneg _ Λ _ ⟨hJ_pos.le, le_refl 0, hβ⟩ _
    have hdval_le : dval ≤ β * M ^ 2 + β * (4 * ↑d) :=
      calc dval ≤ β * susceptibilityInfinite _ Λ _ r.val *
                  susceptibilityInfinite _ Λ _ s.val + β * (4 * ↑d) := hbound
           _ ≤ β * M ^ 2 + β * (4 * ↑d) := by
                nlinarith [mul_le_mul hsusc_r hsusc_s hsusc_s_nn hM_nn,
                           mul_nonneg hβ.le (pow_nonneg hM_nn 2)]
    rw [hdeq, Real.norm_of_nonneg hdnn]
    exact hdval_le
  · exact h₁
  · exact h₂

/-- **Infinite-volume two-point function is Lipschitz in β** (Step 168, GJ §17.5):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 ≤ J`, `0 < a ≤ b`, `bJ·2d < 1`,
`β ↦ correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {r_val,s_val}`
is `C`-Lipschitz on `[a, b]`, with `C = J·M² + J·4d`, `M = bJ·2d/(1-bJ·2d)`.

Proof: for β₁ ≤ β₂ in `[a,b]`:
- Monotonicity: `corr_∞(β₁) ≤ corr_∞(β₂)`.
- Upper bound: for each stage `n`, either `corr_n(β₂) ≤ corr_n(β₁) + C·(β₂-β₁)` (Step 167)
  or `corr_n(β₂) = 0 ≤ corr_∞(β₁) + C·(β₂-β₁)`. Taking `ciSup_le` gives
  `corr_∞(β₂) ≤ corr_∞(β₁) + C·(β₂-β₁)`.
  So `|corr_∞(β₂) - corr_∞(β₁)| = corr_∞(β₂) - corr_∞(β₁) ≤ C·|β₂-β₁|`.

Reference: Glimm–Jaffe §17.5 p.~312. -/
theorem correlationInfinite_lipschitzOnWith_beta_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    LipschitzOnWith ⟨J * M ^ 2 + J * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg (le_of_lt (ha.trans_le hab)) hJ)
                       (Nat.cast_nonneg _)) hdenom_b.le
        exact add_nonneg (mul_nonneg hJ (pow_nonneg hM_nn 2))
               (mul_nonneg hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) := by
  intro M
  have hb_pos : 0 < b := ha.trans_le hab
  have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
  have hM_nn : 0 ≤ M :=
    div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ) (Nat.cast_nonneg _)) hdenom_b.le
  have hC_nn : 0 ≤ J * M ^ 2 + J * (4 * ↑d) :=
    add_nonneg (mul_nonneg hJ (pow_nonneg hM_nn 2))
               (mul_nonneg hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  apply LipschitzOnWith.of_dist_le_mul
  intro β₁ h₁ β₂ h₂
  simp only [Real.dist_eq, NNReal.coe_mk]
  rcases le_total β₁ β₂ with hβ | hβ
  · -- Case β₁ ≤ β₂
    have hmono_inf := IsingModel.Ambient.correlationInfinite_monotone_beta
        (IsingModel.latticeGraph d) Λ hJ (le_refl 0) {r_val, s_val}
        (Set.mem_Ioi.mpr (ha.trans_le h₁.1)) (Set.mem_Ioi.mpr (ha.trans_le h₂.1)) hβ
    rw [abs_of_nonpos (sub_nonpos_of_le hmono_inf), neg_sub,
        abs_of_nonpos (sub_nonpos.mpr hβ), neg_sub]
    simp only [correlationInfinite_eq_ciSup]
    apply sub_le_iff_le_add.mpr
    apply ciSup_le; intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      set r : ↑(Λ.volume n) := ⟨r_val, hrn⟩ with hr_def
      set s : ↑(Λ.volume n) := ⟨s_val, hsn⟩ with hs_def
      have hrs' : r ≠ s := fun h => hrs (congrArg Subtype.val h)
      have heq : ∀ (p : IsingParams ℝ),
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {r_val, s_val} n =
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) p {r, s} := by
        intro p
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        exact Iff.rfl
      rw [heq]
      have hnorm := inducedLatticeGraph_correlation_norm_sub_le Λ J hJ a b ha hab hlt
                     n r s hrs' β₁ β₂ h₁ h₂
      have hmono_n := IsingModel.correlation_monotoneOn_beta
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) J hJ {r, s}
          (Set.mem_Ici.mpr (ha.trans_le h₁.1).le)
          (Set.mem_Ici.mpr (ha.trans_le h₂.1).le) hβ
      simp only [Real.norm_of_nonneg (sub_nonneg_of_le hmono_n),
                 Real.norm_of_nonneg (sub_nonneg.mpr hβ)] at hnorm
      have hcn_le_inf :
          IsingModel.correlation
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r, s} ≤
          ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} m := by
        rw [← heq (⟨J, 0, β₁⟩ : IsingParams ℝ)]
        exact le_ciSup (correlationAlongExhaustion_bddAbove _ Λ _ _) n
      linarith
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      have hnn : 0 ≤ ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} m :=
        Real.iSup_nonneg (fun m => correlationAlongExhaustion_nonneg
          (IsingModel.latticeGraph d) Λ (⟨J, 0, β₁⟩ : IsingParams ℝ)
          ⟨hJ, le_refl 0, ha.trans_le h₁.1⟩ {r_val, s_val} m)
      linarith [mul_nonneg hC_nn (sub_nonneg.mpr hβ)]
  · -- Case β₂ ≤ β₁: symmetric
    have hmono_inf := IsingModel.Ambient.correlationInfinite_monotone_beta
        (IsingModel.latticeGraph d) Λ hJ (le_refl 0) {r_val, s_val}
        (Set.mem_Ioi.mpr (ha.trans_le h₂.1)) (Set.mem_Ioi.mpr (ha.trans_le h₁.1)) hβ
    rw [abs_of_nonneg (sub_nonneg_of_le hmono_inf),
        abs_of_nonneg (sub_nonneg.mpr hβ)]
    simp only [correlationInfinite_eq_ciSup]
    apply sub_le_iff_le_add.mpr
    apply ciSup_le; intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      set r : ↑(Λ.volume n) := ⟨r_val, hrn⟩ with hr_def
      set s : ↑(Λ.volume n) := ⟨s_val, hsn⟩ with hs_def
      have hrs' : r ≠ s := fun h => hrs (congrArg Subtype.val h)
      have heq : ∀ (p : IsingParams ℝ),
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {r_val, s_val} n =
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) p {r, s} := by
        intro p
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        exact Iff.rfl
      rw [heq]
      have hnorm := inducedLatticeGraph_correlation_norm_sub_le Λ J hJ a b ha hab hlt
                     n r s hrs' β₂ β₁ h₂ h₁
      have hmono_n := IsingModel.correlation_monotoneOn_beta
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) J hJ {r, s}
          (Set.mem_Ici.mpr (ha.trans_le h₂.1).le)
          (Set.mem_Ici.mpr (ha.trans_le h₁.1).le) hβ
      simp only [Real.norm_of_nonneg (sub_nonneg_of_le hmono_n),
                 Real.norm_of_nonneg (sub_nonneg.mpr hβ)] at hnorm
      have hcn_le_inf :
          IsingModel.correlation
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r, s} ≤
          ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} m := by
        rw [← heq (⟨J, 0, β₂⟩ : IsingParams ℝ)]
        exact le_ciSup (correlationAlongExhaustion_bddAbove _ Λ _ _) n
      linarith
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      have hnn : 0 ≤ ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} m :=
        Real.iSup_nonneg (fun m => correlationAlongExhaustion_nonneg
          (IsingModel.latticeGraph d) Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
          ⟨hJ, le_refl 0, ha.trans_le h₂.1⟩ {r_val, s_val} m)
      linarith [mul_nonneg hC_nn (sub_nonneg.mpr hβ)]

/-- **Infinite-volume two-point function is Lipschitz in J** (Step 222):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 < β`, `0 < a ≤ b`, `bβ·2d < 1`,
`J ↦ correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {r_val,s_val}`
is `C`-Lipschitz on `[a, b]`, with `C = β·M² + β·4d`, `M = bβ·2d/(1-bβ·2d)`.

Direct J-direction analogue of Step 168. Proof: for J₁ ≤ J₂ in `[a,b]`:
- Monotonicity in J: `corr_∞(J₁) ≤ corr_∞(J₂)`.
- For each stage `n`, either `corr_n(J₂) ≤ corr_n(J₁) + C·(J₂-J₁)` (Step 221)
  or `corr_n(J₂) = 0 ≤ corr_∞(J₁) + C·(J₂-J₁)`. Take `ciSup_le`. -/
theorem correlationInfinite_lipschitzOnWith_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    LipschitzOnWith ⟨β * M ^ 2 + β * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg (le_of_lt (ha.trans_le hab)) hβ.le)
                       (Nat.cast_nonneg _)) hdenom_b.le
        exact add_nonneg (mul_nonneg hβ.le (pow_nonneg hM_nn 2))
               (mul_nonneg hβ.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) := by
  intro M
  have hb_pos : 0 < b := ha.trans_le hab
  have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
  have hM_nn : 0 ≤ M :=
    div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le) (Nat.cast_nonneg _)) hdenom_b.le
  have hC_nn : 0 ≤ β * M ^ 2 + β * (4 * ↑d) :=
    add_nonneg (mul_nonneg hβ.le (pow_nonneg hM_nn 2))
               (mul_nonneg hβ.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  apply LipschitzOnWith.of_dist_le_mul
  intro J₁ h₁ J₂ h₂
  simp only [Real.dist_eq, NNReal.coe_mk]
  rcases le_total J₁ J₂ with hJ_le | hJ_le
  · have hmono_inf := IsingModel.Ambient.correlationInfinite_monotone_J
        (IsingModel.latticeGraph d) Λ (le_refl 0) hβ {r_val, s_val}
        (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₁.1)))
        (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₂.1))) hJ_le
    rw [abs_of_nonpos (sub_nonpos_of_le hmono_inf), neg_sub,
        abs_of_nonpos (sub_nonpos.mpr hJ_le), neg_sub]
    simp only [correlationInfinite_eq_ciSup]
    apply sub_le_iff_le_add.mpr
    apply ciSup_le; intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      set r : ↑(Λ.volume n) := ⟨r_val, hrn⟩ with hr_def
      set s : ↑(Λ.volume n) := ⟨s_val, hsn⟩ with hs_def
      have hrs' : r ≠ s := fun h => hrs (congrArg Subtype.val h)
      have heq : ∀ (p : IsingParams ℝ),
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {r_val, s_val} n =
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) p {r, s} := by
        intro p
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        exact Iff.rfl
      rw [heq]
      have hnorm := inducedLatticeGraph_correlation_norm_sub_le_J Λ β hβ a b ha hab hlt
                     n r s hrs' J₁ J₂ h₁ h₂
      have hmono_n := IsingModel.correlation_monotone_J
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 (le_refl 0) β hβ {r, s}
          (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₁.1)))
          (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₂.1))) hJ_le
      simp only [correlationJ] at hmono_n
      simp only [Real.norm_of_nonneg (sub_nonneg_of_le hmono_n),
                 Real.norm_of_nonneg (sub_nonneg.mpr hJ_le)] at hnorm
      have hcn_le_inf :
          IsingModel.correlation
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r, s} ≤
          ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} m := by
        rw [← heq (⟨J₁, 0, β⟩ : IsingParams ℝ)]
        exact le_ciSup (correlationAlongExhaustion_bddAbove _ Λ _ _) n
      linarith
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      have hnn : 0 ≤ ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} m :=
        Real.iSup_nonneg (fun m => correlationAlongExhaustion_nonneg
          (IsingModel.latticeGraph d) Λ (⟨J₁, 0, β⟩ : IsingParams ℝ)
          ⟨le_of_lt (ha.trans_le h₁.1), le_refl 0, hβ⟩ {r_val, s_val} m)
      linarith [mul_nonneg hC_nn (sub_nonneg.mpr hJ_le)]
  · -- Case J₂ ≤ J₁: symmetric
    have hmono_inf := IsingModel.Ambient.correlationInfinite_monotone_J
        (IsingModel.latticeGraph d) Λ (le_refl 0) hβ {r_val, s_val}
        (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₂.1)))
        (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₁.1))) hJ_le
    rw [abs_of_nonneg (sub_nonneg_of_le hmono_inf),
        abs_of_nonneg (sub_nonneg.mpr hJ_le)]
    simp only [correlationInfinite_eq_ciSup]
    apply sub_le_iff_le_add.mpr
    apply ciSup_le; intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      set r : ↑(Λ.volume n) := ⟨r_val, hrn⟩ with hr_def
      set s : ↑(Λ.volume n) := ⟨s_val, hsn⟩ with hs_def
      have hrs' : r ≠ s := fun h => hrs (congrArg Subtype.val h)
      have heq : ∀ (p : IsingParams ℝ),
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {r_val, s_val} n =
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) p {r, s} := by
        intro p
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        exact Iff.rfl
      rw [heq]
      have hnorm := inducedLatticeGraph_correlation_norm_sub_le_J Λ β hβ a b ha hab hlt
                     n r s hrs' J₂ J₁ h₂ h₁
      have hmono_n := IsingModel.correlation_monotone_J
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 (le_refl 0) β hβ {r, s}
          (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₂.1)))
          (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₁.1))) hJ_le
      simp only [correlationJ] at hmono_n
      simp only [Real.norm_of_nonneg (sub_nonneg_of_le hmono_n),
                 Real.norm_of_nonneg (sub_nonneg.mpr hJ_le)] at hnorm
      have hcn_le_inf :
          IsingModel.correlation
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r, s} ≤
          ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} m := by
        rw [← heq (⟨J₂, 0, β⟩ : IsingParams ℝ)]
        exact le_ciSup (correlationAlongExhaustion_bddAbove _ Λ _ _) n
      linarith
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      have hnn : 0 ≤ ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} m :=
        Real.iSup_nonneg (fun m => correlationAlongExhaustion_nonneg
          (IsingModel.latticeGraph d) Λ (⟨J₂, 0, β⟩ : IsingParams ℝ)
          ⟨le_of_lt (ha.trans_le h₂.1), le_refl 0, hβ⟩ {r_val, s_val} m)
      linarith [mul_nonneg hC_nn (sub_nonneg.mpr hJ_le)]

/-- **Continuity of infinite-volume two-point function in β** (Step 169, GJ §17.5):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 ≤ J`, `0 < a ≤ b`, `bJ·2d < 1`,
`β ↦ correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {r_val,s_val}` is continuous on `[a, b]`.

Follows immediately from the Lipschitz bound of Step 168.

Reference: Glimm–Jaffe §17.5 p.~312. -/
theorem correlationInfinite_continuousOn_beta_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    ContinuousOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) :=
  (correlationInfinite_lipschitzOnWith_beta_of_high_temp Λ r_val s_val hrs J hJ a b ha hab
    hlt).continuousOn

/-- **Continuity of infinite-volume two-point function in J** (Step 223):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 < β`, `0 < a ≤ b`, `bβ·2d < 1`,
`J ↦ correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {r_val,s_val}` is continuous on `[a, b]`.

Direct J-direction analogue of Step 169. Follows immediately from Step 222
(`correlationInfinite_lipschitzOnWith_J_of_high_temp`). -/
theorem correlationInfinite_continuousOn_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    ContinuousOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) :=
  (correlationInfinite_lipschitzOnWith_J_of_high_temp Λ r_val s_val hrs β hβ a b ha hab
    hlt).continuousOn

/-- **Uniform convergence of finite-volume correlations** (Step 170, GJ §17.5):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 ≤ J`, `0 < a ≤ b`, `bJ·2d < 1`,
the finite-volume two-point functions converge uniformly on `[a, b]`:
`∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ β ∈ [a,b], |corr_n(β) - corr_∞(β)| < ε`.

In Lean: `TendstoUniformlyOn (fun n β => corr_n(β)) (fun β => corr_∞(β)) atTop (Set.Icc a b)`.

Proof: Dini's theorem (`tendstoUniformlyOn_of_forall_tendsto`) on the compact set `[a, b]`:
1. Each `β ↦ corr_n(β)` is continuous on `[a,b]` (Step 117a for finite-vol case,
   constant 0 otherwise).
2. For each `β ∈ [a,b]`, `n ↦ corr_n(β)` is monotone (`correlationAlongExhaustion_monotone`).
3. The limit `β ↦ corr_∞(β)` is continuous on `[a,b]` (Step 169).
4. Pointwise convergence (`correlationAlongExhaustion_tendsto_ciSup`).

Reference: Glimm–Jaffe §17.5 p.~312 (monotone convergence to thermodynamic limit). -/
theorem correlationAlongExhaustion_tendstoUniformlyOn_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    TendstoUniformlyOn
      (fun n β => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Icc a b) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · -- (1) Continuity of each corr_n in β
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      -- Each β ↦ correlation G_n ⟨J,0,β⟩ {r,s} is continuous (Step 117a)
      intro β _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun β' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext β'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact IsingModel.correlation_continuousAt_beta _ J β _
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · -- (2) Monotone in n for each β ∈ [a, b]
    intro β hβ
    exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ, le_refl 0, ha.trans_le hβ.1⟩ {r_val, s_val}
  · -- (3) Continuity of the limit (Step 169)
    exact correlationInfinite_continuousOn_beta_of_high_temp Λ r_val s_val hrs J hJ a b ha hab hlt
  · -- (4) Pointwise convergence
    intro β hβ
    have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨hJ, le_refl 0, ha.trans_le hβ.1⟩
    have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
      (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
    simp only [correlationInfinite_eq_ciSup]
    exact htend

/-- **Uniform convergence of finite-volume correlations in J** (Step 224):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 < β`, `0 < a ≤ b`, `bβ·2d < 1`,
the finite-volume two-point functions converge uniformly on `[a, b]` in J.

Direct J-direction analogue of Step 170. Proof: Dini's theorem on the compact `[a, b]`:
1. Each `J ↦ corr_n(J)` is continuous (Step 207 + `.continuousAt`).
2. `n ↦ corr_n(J)` is monotone (`correlationAlongExhaustion_monotone`).
3. Limit `J ↦ corr_∞(J)` is continuous (Step 223).
4. Pointwise convergence (`correlationAlongExhaustion_tendsto_ciSup`). -/
theorem correlationAlongExhaustion_tendstoUniformlyOn_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    TendstoUniformlyOn
      (fun n J => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Icc a b) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      intro J _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J', 0, β⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun J' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J', 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext J'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact (IsingModel.correlation_continuous_J _ 0 β _).continuousAt
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · intro J hJ_mem
    exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ)
      ⟨le_of_lt (ha.trans_le hJ_mem.1), le_refl 0, hβ⟩ {r_val, s_val}
  · exact correlationInfinite_continuousOn_J_of_high_temp Λ r_val s_val hrs β hβ a b ha hab hlt
  · intro J hJ_mem
    have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨le_of_lt (ha.trans_le hJ_mem.1), le_refl 0, hβ⟩
    have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
      (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
    simp only [correlationInfinite_eq_ciSup]
    exact htend

/-- **A.e. differentiability of infinite-volume two-point function in β** (Step 171):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 ≤ J`, `0 < a ≤ b`, `bJ·2d < 1`,
the infinite-volume two-point function `β ↦ corr_∞(β)` is differentiable within `[a,b]`
at Lebesgue-almost every `β ∈ [a,b]`.

Proof: direct from Step 168 (`correlationInfinite_lipschitzOnWith_beta_of_high_temp`)
via Rademacher's theorem (`LipschitzOnWith.ae_differentiableWithinAt_real`).

Analytic corollary of the Lipschitz bound established in the GJ §17.5 derivative program.
Not yet the full everywhere-differentiability claimed by GJ §17.6 Thm 17.6.1 p.313
(that requires uniform convergence of the derivative sequence). -/
theorem correlationInfinite_ae_differentiableWithinAt_beta_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    ∀ᵐ β ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc a b),
    DifferentiableWithinAt ℝ
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) β := by
  have hlip := correlationInfinite_lipschitzOnWith_beta_of_high_temp
    Λ r_val s_val hrs J hJ a b ha hab hlt
  exact LipschitzOnWith.ae_differentiableWithinAt_real hlip measurableSet_Icc

/-- **A.e. differentiability of infinite-volume two-point function in J** (Step 225):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 < β`, `0 < a ≤ b`, `bβ·2d < 1`,
`J ↦ corr_∞(J)` is differentiable within `[a, b]` at Lebesgue-a.e. J.

Direct J-direction analogue of Step 171. Proof: Step 222 (Lipschitz) +
Rademacher's theorem (`LipschitzOnWith.ae_differentiableWithinAt_real`). -/
theorem correlationInfinite_ae_differentiableWithinAt_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc a b),
    DifferentiableWithinAt ℝ
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) J := by
  have hlip := correlationInfinite_lipschitzOnWith_J_of_high_temp
    Λ r_val s_val hrs β hβ a b ha hab hlt
  exact LipschitzOnWith.ae_differentiableWithinAt_real hlip measurableSet_Icc

/-! ## Moved: open-interval correlationInfinite BV / a.e.-diff wrappers

The four open-interval `correlationInfinite_*` regularity wrappers
(`locallyBoundedVariationOn` and `ae_differentiableWithinAt_*_of_high_temp_open`
in both β and J directions) now live in
`LatticeMassHighTempLipschitzOpenIntervalAe.lean`. -/



/-! ## Moved: continuity of corr_∞ on open high-temperature intervals

The two wrappers
`correlationInfinite_continuousOn_{beta,J}_of_high_temp_open`
now live in `LatticeMassHighTempLipschitzContinuousOnOpen.lean`. -/



/-! ## Moved: locally uniform convergence on open high-temperature interval

The two wrappers
`correlationAlongExhaustion_tendstoLocallyUniformlyOn_{beta,J}_of_high_temp_open`
now live in `LatticeMassHighTempLipschitzTendstoLocallyUniformly.lean`. -/



/-! ## Moved: continuousAt wrappers on Ioo 0 _c

The two wrappers
`correlationInfinite_continuousAt_{beta,J}_of_high_temp` now live in
`LatticeMassHighTempContinuousAt.lean`. -/



end Ambient
end IsingModel
