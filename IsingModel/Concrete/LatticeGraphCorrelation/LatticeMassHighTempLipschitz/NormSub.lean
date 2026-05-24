import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitz.DerivBound

/-!
# Lattice mass high-temp Lipschitz split — correlation norm-difference bounds in beta and J

Part of the split high-temperature Lipschitz layer (Issue #1850).
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
    obtain ⟨dval, hd, hbound⟩ :=
      inducedLatticeGraph_beta_deriv_abs_le_high_temp Λ J hJ a b ha hab hlt
        n r s hrs β hβ
    have hdeq : deriv (fun β' => IsingModel.correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) β
                = dval := hd.deriv
    simpa [hdeq, Real.norm_eq_abs, M] using hbound
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


end Ambient
end IsingModel
