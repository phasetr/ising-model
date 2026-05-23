import IsingModel.AmbientComplexAnalyticity.Basic.StageAnalyticity

/-!
# Upper norm-bound wrappers

This module contains wrappers split from `AmbientComplexAnalyticity.Basic`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Per-stage locally-uniform norm bound** for
`partitionFunctionComplexAlongExhaustion` under `|Re h| ≤ R`. Montel input. -/
theorem norm_partitionFunctionComplexAlongExhaustion_le_of_re_bound_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) {R : ℝ} {h : ℂ} (hh : |h.re| ≤ R) :
    ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
      ≤ Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) *
          Real.exp (|β| *
            (|J| * (inducedGraph G (Λ.volume n)).edgeFinset.card
              + R * Fintype.card (↑(Λ.volume n) : Type _))) :=
  IsingModel.norm_partitionFunctionComplex_le_of_re_bound
    (inducedGraph G (Λ.volume n)) β J hh

/-- **Compact real-part bound** for complex fields: every compact set of
fields has a uniform bound on `|Re h|`. This is the topological input that
turns the pointwise `|Re h| ≤ R` partition-function estimate into a
compact-uniform estimate. -/
theorem exists_abs_re_le_on_isCompact {K : Set ℂ} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ h ∈ K, |h.re| ≤ R := by
  rcases hK.bddAbove_image (by fun_prop : ContinuousOn (fun h : ℂ => |h.re|) K) with
    ⟨R₀, hR₀⟩
  refine ⟨max R₀ 0, le_max_right _ _, ?_⟩
  intro h hh
  exact (hR₀ ⟨h, hh, rfl⟩).trans (le_max_left _ _)

/-- **Per-stage compact-uniform norm bound** for
`partitionFunctionComplexAlongExhaustion`: on any compact field set `K`,
there is a single real-part bound `R` that works for every `h ∈ K` and every
stage estimate. The right-hand side still depends on the stage size; this
packages the compact-field envelope needed by later normalised logarithmic
estimates rather than a stage-uniform Montel bound by itself. -/
theorem norm_partitionFunctionComplexAlongExhaustion_le_on_isCompact_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) {K : Set ℂ} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ n, ∀ h ∈ K,
      ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        ≤ Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) *
            Real.exp (|β| *
              (|J| * (inducedGraph G (Λ.volume n)).edgeFinset.card
                + R * Fintype.card (↑(Λ.volume n) : Type _))) := by
  rcases exists_abs_re_le_on_isCompact hK with ⟨R, hR_nonneg, hR⟩
  refine ⟨R, hR_nonneg, ?_⟩
  intro n h hh
  exact norm_partitionFunctionComplexAlongExhaustion_le_of_re_bound_stage
    G Λ β J n (hR h hh)

/-- **Per-stage upper bound on the normalised real logarithm of `‖Z_ℂ‖`**:
under `|Re h| ≤ R` and nonvanishing of the complex partition function, the
compact-envelope estimate gives an upper bound for
`log ‖Z_{Λ_n}(h)‖ / |Λ_n|`. This is only the upper half of the later
normalised absolute-log control; it does not provide lower control on
`‖Z_{Λ_n}(h)‖`. -/
theorem real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_of_re_bound_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) [Nonempty (↑(Λ.volume n) : Type _)] {R : ℝ} {h : ℂ}
    (hZ : partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n ≠ 0)
    (hh : |h.re| ≤ R) :
    Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
      ≤ Real.log 2 +
        |β| * (|J| * (inducedGraph G (Λ.volume n)).edgeFinset.card
          + R * Fintype.card (↑(Λ.volume n) : Type _))
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
  set A : ℝ :=
    |β| * (|J| * (inducedGraph G (Λ.volume n)).edgeFinset.card
      + R * Fintype.card (↑(Λ.volume n) : Type _))
  have hcard_pos : (0 : ℝ) < (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (↑(Λ.volume n) : Type _))
  have hconfig_pos :
      (0 : ℝ) < (Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) : ℝ) := by
    rw [card_config_eq_two_pow]
    positivity
  have hexp_pos : (0 : ℝ) < Real.exp A := Real.exp_pos _
  have hnorm_pos :
      0 < ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ :=
    norm_pos_iff.mpr hZ
  have hlog :
      Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        ≤ (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) * Real.log 2 + A := by
    calc
      Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
          ≤ Real.log
              ((Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) : ℝ)
                * Real.exp A) := by
            refine (Real.log_le_log_iff hnorm_pos
              (mul_pos hconfig_pos hexp_pos)).mpr ?_
            simpa [A] using
              norm_partitionFunctionComplexAlongExhaustion_le_of_re_bound_stage
                G Λ β J n hh
      _ = Real.log
              (Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) : ℝ)
            + A := by
            rw [Real.log_mul hconfig_pos.ne' hexp_pos.ne', Real.log_exp]
      _ = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) * Real.log 2 + A := by
            rw [card_config_eq_two_pow]
            push_cast
            rw [Real.log_pow]
  calc
    Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
        = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹ *
          Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ := by
            field_simp
    _ ≤ (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹ *
        ((Fintype.card (↑(Λ.volume n) : Type _) : ℝ) * Real.log 2 + A) :=
          mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hcard_pos.le)
    _ = Real.log 2 + A / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
          field_simp
    _ = Real.log 2 +
        |β| * (|J| * (inducedGraph G (Λ.volume n)).edgeFinset.card
          + R * Fintype.card (↑(Λ.volume n) : Type _))
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
          simp [A]

/-- **Compact-field upper normalised-log handoff under bounded edge density**:
if `K` is compact, the exhaustion has bounded edge density, every stage is
nonempty, and `Z_{Λ_n}(h)` is nonzero on `K`, then
`Real.log ‖Z_{Λ_n}(h)‖ / |Λ_n|` has one stage-independent upper bound on
`K`. This packages the upper half of the normalised-log input for the later
normal-family argument; the lower control needed for `|log ‖Z‖|` remains
separate. -/
theorem exists_real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_on_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) (β J : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hZ : ∀ n, ∀ h ∈ K,
      partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n ≠ 0) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C := by
  rcases hBED with ⟨c, hc⟩
  rcases exists_abs_re_le_on_isCompact hK with ⟨R, _hR_nonneg, hR⟩
  refine ⟨Real.log 2 + |β| * (|J| * c + R), ?_⟩
  intro n h hh
  have hstage :=
    real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_of_re_bound_stage
      G Λ β J n (hZ n h hh) (hR h hh)
  have hcard_pos_nat : 0 < Fintype.card (↑(Λ.volume n) : Type _) :=
    Fintype.card_pos
  have hvol_nonempty : (Λ.volume n).Nonempty := by
    exact Finset.card_pos.mp (by
      simpa [Fintype.card_coe] using hcard_pos_nat)
  have hcard_pos : (0 : ℝ) < (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast hcard_pos_nat
  have hratio :
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ c :=
    (div_le_iff₀ hcard_pos).mpr (hc n hvol_nonempty)
  calc
    Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
        ≤ Real.log 2 +
          |β| * (|J| * (inducedGraph G (Λ.volume n)).edgeFinset.card
            + R * Fintype.card (↑(Λ.volume n) : Type _))
            / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := hstage
    _ = Real.log 2 +
          |β| * (|J| *
              (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
                (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) + R) := by
          field_simp
    _ ≤ Real.log 2 + |β| * (|J| * c + R) := by
          gcongr

/-- **Stage free-energy bound from a normalised absolute-log bound**:
if the normalised quantity
`|log ‖Z_{Λ_n}(h)‖| / |Λ_n|` is bounded by `C` at a nonempty stage, then the
principal complex free energy is bounded by `C + π / |Λ_n|`. This is the
precise handoff from normalised logarithmic control to the free-energy bound
needed by the later normal-family step; it does not assert that the
partition-function upper envelope alone supplies the hypothesis. -/
theorem norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) [Nonempty (↑(Λ.volume n) : Type _)] {h : ℂ} {C : ℝ}
    (hC :
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
      ≤ C + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
  have hbase :=
    IsingModel.norm_freeEnergyComplex_le_trivial_bound
      (inducedGraph G (Λ.volume n)) β J h
  have hC' :
      |Real.log ‖partitionFunctionComplex
          (inducedGraph G (Λ.volume n)) (J : ℂ) h (β : ℂ)‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C := by
    simpa [partitionFunctionComplexAlongExhaustion] using hC
  have hstep :
      |Real.log ‖partitionFunctionComplex
          (inducedGraph G (Λ.volume n)) (J : ℂ) h (β : ℂ)‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
          + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
        ≤ C + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    linarith
  simpa [freeEnergyComplexAlongExhaustion,
    partitionFunctionComplexAlongExhaustion] using hbase.trans hstep

/-- **Setwise free-energy bound from normalised absolute-log control**:
if one constant `C` bounds
`|log ‖Z_{Λ_n}(h)‖| / |Λ_n|` for every stage and every `h` in a set `K`, then
the along-exhaustion principal free energies satisfy the corresponding
stagewise bound on `K`. This packages the exact remaining analytic input for
the Montel/Vitali normal-family step. -/
theorem norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (β J : ℝ) {K : Set ℂ} {C : ℝ}
    (hC : ∀ n, ∀ h ∈ K,
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ∀ n, ∀ h ∈ K,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        ≤ C + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
  intro n h hh
  exact norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_stage
    G Λ β J n (hC n h hh)

/-- **Stage-independent setwise free-energy bound from normalised
absolute-log control**: if one constant `C` bounds
`|log ‖Z_{Λ_n}(h)‖| / |Λ_n|` for every nonempty stage and every `h ∈ K`, then
the along-exhaustion principal free energies are bounded on `K` by the single
stage-independent constant `C + π`. This is the locally bounded family shape
needed by a later Montel/normal-family argument. -/
theorem norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set_uniform
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (β J : ℝ) {K : Set ℂ} {C : ℝ}
    (hC : ∀ n, ∀ h ∈ K,
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ∀ n, ∀ h ∈ K,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        ≤ C + Real.pi := by
  intro n h hh
  have hstage :=
    norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set
      G Λ β J hC n h hh
  have hcard_pos : (0 : ℝ) < (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (↑(Λ.volume n) : Type _))
  have hcard_ge_one : (1 : ℝ) ≤ (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast
      (Nat.succ_le_iff.mp (Fintype.card_pos : 0 < Fintype.card (↑(Λ.volume n) : Type _)))
  have hpi :
      Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hcard_pos]
    nlinarith [Real.pi_nonneg, hcard_ge_one]
  have hpi_step :
      C + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
        ≤ C + Real.pi := by
    linarith
  exact hstage.trans hpi_step

/-- **Absolute normalised-log control from two-sided control**:
if `Real.log ‖Z_{Λ_n}(h)‖ / |Λ_n|` is bounded above by `C` and below by
`-C` on a set `K`, then
`|Real.log ‖Z_{Λ_n}(h)‖| / |Λ_n| ≤ C` there. This is the elementary bridge
from separate upper/lower logarithmic estimates to the normalised absolute-log
hypothesis consumed by the free-energy bounds. -/
theorem abs_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_of_two_sided_on_set
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (β J : ℝ) {K : Set ℂ} {C : ℝ}
    (hlo : ∀ n, ∀ h ∈ K,
      -C ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ))
    (hhi : ∀ n, ∀ h ∈ K,
      Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ∀ n, ∀ h ∈ K,
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C := by
  intro n h hh
  have hcard_pos : (0 : ℝ) < (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (↑(Λ.volume n) : Type _))
  have habs :
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)| ≤ C :=
    abs_le.mpr ⟨hlo n h hh, hhi n h hh⟩
  have hrewrite :
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)|
        =
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    rw [abs_div, abs_of_pos hcard_pos]
  calc
    |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
        =
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)| := hrewrite.symm
    _ ≤ C := habs

end Ambient

end IsingModel
