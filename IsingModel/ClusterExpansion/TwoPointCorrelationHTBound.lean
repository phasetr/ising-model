import IsingModel.ClusterExpansion.TwoPointRatioBound
import IsingModel.ClusterExpansion.MayerSumDiffSupportBoundComplex
import IsingModel.ClusterExpansion.TwoPointCapstonePrereqs
import IsingModel.ClusterExpansion.HighTempKoteckyPreiss

/-!
# High-temperature two-point correlation bound

This file assembles the per-component Kotecky--Preiss avoiding-ratio estimate into a finite-graph
complex two-point bound on a small beta-disc.  The activity radius and the final norm bound are
chosen from a degree cap `Delta`; the final beta-disc also intersects the finite-graph
high-temperature expansion radius supplied by the existing `correlationComplex` bridge.
-/

namespace IsingModel

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A small activity radius depending only on the degree cap.  It forces both the KP parameter
`Delta^2 e R` below `1/64` and the final geometric ratio `R exp(8) Delta^2` below `1`. -/
noncomputable def twoPointHTActivityRadius (Δ : ℕ) : ℝ :=
  min (1 / (64 * (((Δ : ℝ) ^ 2 + 1) * Real.exp 1)))
    (1 / (2 * (((Δ : ℝ) ^ 2 + 1) * Real.exp 8)))

/-- The degree-uniform high-temperature two-point bound value (depends only on `Δ`). -/
noncomputable def twoPointHTBoundValue (Δ : ℕ) : ℝ :=
  Real.exp 8 / (1 - twoPointHTActivityRadius Δ * Real.exp 8 * (Δ : ℝ) ^ 2)

/-- The activity radius is positive. -/
theorem twoPointHTActivityRadius_pos (Δ : ℕ) : 0 < twoPointHTActivityRadius Δ := by
  unfold twoPointHTActivityRadius
  exact lt_min (by positivity) (by positivity)

/-- The activity radius satisfies the `1/64` KP threshold for the degree cap. -/
theorem twoPointHTActivityRadius_kp_threshold (Δ : ℕ) :
    (Δ : ℝ) ^ 2 * (Real.exp 1 * twoPointHTActivityRadius Δ) < 1 / 64 := by
  unfold twoPointHTActivityRadius
  have hmain : (Δ : ℝ) ^ 2 * (Real.exp 1 * min
      (1 / (64 * (((Δ : ℝ) ^ 2 + 1) * Real.exp 1)))
      (1 / (2 * (((Δ : ℝ) ^ 2 + 1) * Real.exp 8))))
      ≤ (Δ : ℝ) ^ 2 * (Real.exp 1 * (1 / (64 * (((Δ : ℝ) ^ 2 + 1) * Real.exp 1)))) := by
    gcongr
    exact min_le_left _ _
  have hstrict : (Δ : ℝ) ^ 2 * (Real.exp 1 * (1 / (64 * (((Δ : ℝ) ^ 2 + 1) * Real.exp 1))))
      < 1 / 64 := by
    rw [show (Δ : ℝ) ^ 2 * (Real.exp 1 * (1 / (64 * (((Δ : ℝ) ^ 2 + 1) * Real.exp 1))))
        = (Δ : ℝ) ^ 2 / (64 * ((Δ : ℝ) ^ 2 + 1)) by field_simp]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Δ : ℝ)]
  exact lt_of_le_of_lt hmain hstrict

/-- The activity radius makes the geometric ratio strictly subcritical for the degree cap. -/
theorem twoPointHTActivityRadius_hq_threshold (Δ : ℕ) :
    twoPointHTActivityRadius Δ * Real.exp 8 * ((Δ : ℝ) ^ 2) < 1 := by
  unfold twoPointHTActivityRadius
  have hmain : min (1 / (64 * (((Δ : ℝ) ^ 2 + 1) * Real.exp 1)))
      (1 / (2 * (((Δ : ℝ) ^ 2 + 1) * Real.exp 8))) * Real.exp 8 * ((Δ : ℝ) ^ 2)
      ≤ (1 / (2 * (((Δ : ℝ) ^ 2 + 1) * Real.exp 8))) * Real.exp 8 * ((Δ : ℝ) ^ 2) := by
    gcongr
    exact min_le_right _ _
  have hstrict : (1 / (2 * (((Δ : ℝ) ^ 2 + 1) * Real.exp 8))) * Real.exp 8 * ((Δ : ℝ) ^ 2)
      < 1 := by
    rw [show (1 / (2 * (((Δ : ℝ) ^ 2 + 1) * Real.exp 8))) * Real.exp 8 * ((Δ : ℝ) ^ 2)
        = (Δ : ℝ) ^ 2 / (2 * ((Δ : ℝ) ^ 2 + 1)) by field_simp]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Δ : ℝ)]
  exact lt_of_le_of_lt hmain hstrict

/-- The degree-uniform high-temperature two-point bound value is positive. -/
theorem twoPointHTBoundValue_pos (Δ : ℕ) : 0 < twoPointHTBoundValue Δ := by
  unfold twoPointHTBoundValue
  have hq : twoPointHTActivityRadius Δ * Real.exp 8 * ((Δ : ℝ) ^ 2) < 1 :=
    twoPointHTActivityRadius_hq_threshold Δ
  have hden : 0 < 1 - twoPointHTActivityRadius Δ * Real.exp 8 * ((Δ : ℝ) ^ 2) := by
    linarith
  exact div_pos (Real.exp_pos 8) hden

/-- On the smaller KP threshold `r < 1/64`, the Mayer-difference coefficient is at most `8`. -/
private lemma kpCoeff_le_eight {r : ℝ} (h0 : 0 ≤ r) (hr : r < 1 / 64) :
    (1 / (1 - r)) * (1 - 4 * r / (1 - r) ^ 2)⁻¹ ^ 2 ≤ 8 := by
  have hr_half : r < 1 / 2 := by linarith
  have hden_pos : 0 < 1 - r := by linarith
  have hden_sq_pos : 0 < (1 - r) ^ 2 := pow_pos hden_pos 2
  have hden_sq_ge : (1 / 4 : ℝ) ≤ (1 - r) ^ 2 := by
    nlinarith [h0, hr_half]
  have hrho_le : 4 * r / (1 - r) ^ 2 ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hden_sq_pos]
    nlinarith [hden_sq_ge, hr]
  have hone_minus_rho_pos : 0 < 1 - 4 * r / (1 - r) ^ 2 := by linarith
  have hinv1 : 1 / (1 - r) ≤ (2 : ℝ) := by
    rw [div_le_iff₀ hden_pos]
    nlinarith [hr_half]
  have hinv2 : (1 - 4 * r / (1 - r) ^ 2)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀ hone_minus_rho_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hinv2_nonneg : 0 ≤ (1 - 4 * r / (1 - r) ^ 2)⁻¹ :=
    inv_nonneg.mpr (le_of_lt hone_minus_rho_pos)
  have hsquare : (1 - 4 * r / (1 - r) ^ 2)⁻¹ ^ 2 ≤ (4 : ℝ) := by
    nlinarith [mul_le_mul hinv2 hinv2 hinv2_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
  nlinarith [mul_le_mul hinv1 hsquare
    (by positivity : 0 ≤ (1 - 4 * r / (1 - r) ^ 2)⁻¹ ^ 2)
    (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]

/-- The elementary exponential identity used to package the per-component bound. -/
private lemma activity_exp_card_identity (R : ℝ) (n : ℕ) :
    R ^ n * Real.exp (8 * ((n : ℝ) + 1)) = Real.exp 8 * (R * Real.exp 8) ^ n := by
  rw [mul_add, mul_one]
  have hmul : 8 * (n : ℝ) = (n : ℝ) * 8 := by ring
  rw [hmul, Real.exp_add, Real.exp_nat_mul, mul_pow]
  ring

/-- **Finite-graph high-temperature two-point bound with a degree-uniform value.**  If
`G.maxDegree <= Delta`, then on a small beta-disc the zero-field complex two-point correlation is
bounded by a constant chosen only from `Delta`.  The disc is the intersection of the degree-uniform
activity disc with the finite-graph high-temperature expansion disc for `correlationComplex`.
-/
theorem correlationComplex_two_point_norm_le_of_high_temp
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] {i j : ι} (hij : i ≠ j)
    (J : ℝ) (Δ : ℕ) (hΔ : G.maxDegree ≤ Δ) :
    ∃ r > 0, ∀ β ∈ Metric.ball (0 : ℂ) r,
      ‖correlationComplex G ({i, j} : Finset ι) (J : ℂ) 0 β‖
        ≤ twoPointHTBoundValue Δ := by
  classical
  set R : ℝ := twoPointHTActivityRadius Δ with hRdef
  set A : ℝ := Real.exp 8 with hAdef
  set a : ℝ := R * Real.exp 8 with hadef
  have hRpos : 0 < R := by simpa [hRdef] using twoPointHTActivityRadius_pos Δ
  have hRnonneg : 0 ≤ R := le_of_lt hRpos
  have hApos : 0 < A := by
    rw [hAdef]
    exact Real.exp_pos 8
  have hAnonneg : 0 ≤ A := le_of_lt hApos
  have hanonneg : 0 ≤ a := by positivity
  have hΔcast : (G.maxDegree : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hRkpΔ : (Δ : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 64 := by
    simpa [hRdef] using twoPointHTActivityRadius_kp_threshold Δ
  have hRkpG64 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 64 := by
    have hle : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)
        ≤ (Δ : ℝ) ^ 2 * (Real.exp 1 * R) := by gcongr
    exact lt_of_le_of_lt hle hRkpΔ
  have hRkpG6 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6 := by
    linarith [hRkpG64]
  obtain ⟨hkpR, hρR⟩ := kp_tail_conditions_of_lt hRkpG6
  have hqΔ : a * ((Δ : ℝ) ^ 2) < 1 := by
    simpa [hRdef, hadef, mul_assoc, mul_left_comm, mul_comm] using
      twoPointHTActivityRadius_hq_threshold Δ
  have hqG : a * ((G.maxDegree : ℝ) ^ 2) < 1 := by
    have hle : a * ((G.maxDegree : ℝ) ^ 2) ≤ a * ((Δ : ℝ) ^ 2) := by gcongr
    exact lt_of_le_of_lt hle hqΔ
  have hdenΔpos : 0 < 1 - a * ((Δ : ℝ) ^ 2) := by linarith
  obtain ⟨rExp, hrExp, hExp⟩ :=
    correlationComplex_high_temp_expansion_h_zero_closed_on_ball_htSubgraphSum
      G ({i, j} : Finset ι) J
  have h_tanh0 : Complex.tanh ((0 : ℂ) * (J : ℂ)) = 0 := by
    rw [zero_mul, Complex.tanh_zero]
  have h_cosh0 : Complex.cosh ((0 : ℂ) * (J : ℂ)) ≠ 0 := by
    rw [zero_mul, Complex.cosh_zero]
    exact one_ne_zero
  have h_tanh_cont : ContinuousAt (fun β : ℂ => Complex.tanh (β * (J : ℂ))) 0 := by
    have hsinh : ContinuousAt (fun β : ℂ => Complex.sinh (β * (J : ℂ))) 0 :=
      (Complex.continuous_sinh.comp (continuous_id.mul continuous_const)).continuousAt
    have hcosh : ContinuousAt (fun β : ℂ => Complex.cosh (β * (J : ℂ))) 0 :=
      (Complex.continuous_cosh.comp (continuous_id.mul continuous_const)).continuousAt
    exact hsinh.div hcosh h_cosh0
  have h_tanh_ev : ∀ᶠ β : ℂ in 𝓝 (0 : ℂ), ‖Complex.tanh (β * (J : ℂ))‖ < R := by
    have htend : Filter.Tendsto (fun β : ℂ => ‖Complex.tanh (β * (J : ℂ))‖)
        (𝓝 0) (𝓝 0) := by
      have h2 := h_tanh_cont.norm.tendsto
      rwa [h_tanh0, norm_zero] at h2
    exact htend.eventually (gt_mem_nhds hRpos)
  rw [Metric.eventually_nhds_iff_ball] at h_tanh_ev
  obtain ⟨rt, hrt, htanhr⟩ := h_tanh_ev
  refine ⟨min rExp rt, lt_min hrExp hrt, ?_⟩
  intro β hβ
  have hβdist : dist β 0 < min rExp rt := Metric.mem_ball.mp hβ
  have hβExp : β ∈ Metric.ball (0 : ℂ) rExp :=
    Metric.mem_ball.mpr (lt_of_lt_of_le hβdist (min_le_left _ _))
  have hβt : β ∈ Metric.ball (0 : ℂ) rt :=
    Metric.mem_ball.mpr (lt_of_lt_of_le hβdist (min_le_right _ _))
  set t : ℂ := Complex.tanh (β * (J : ℂ)) with htdef
  have htRlt : ‖t‖ < R := by simpa [htdef] using htanhr β hβt
  have htRle : ‖t‖ ≤ R := le_of_lt htRlt
  have htz : t ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact htRlt
  have httG64 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖t‖) < 1 / 64 := by
    have hle : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖t‖)
        ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) := by gcongr
    exact lt_of_le_of_lt hle hRkpG64
  have httG6 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖t‖) < 1 / 6 := by
    linarith [httG64]
  obtain ⟨hkpt, hρt⟩ := kp_tail_conditions_of_lt httG6
  have hper : ∀ C ∈ connectingComponents G i j,
      ‖t‖ ^ C.card * ‖htSubgraphSumAvoiding G C t / htSubgraphSum G (∅ : Finset ι) t‖
        ≤ A * a ^ C.card := by
    intro C hC
    have hCdata := hC
    rw [connectingComponents, Finset.mem_filter, Finset.mem_powerset] at hCdata
    have hCsub : C ⊆ G.edgeFinset := hCdata.1
    have hCne : C.Nonempty := hCdata.2.1
    have hCconn : IsEdgeConnected C := hCdata.2.2.1
    set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖t‖) with hrrdef
    set κ : ℝ := (1 / (1 - rr)) * (1 - 4 * rr / (1 - rr) ^ 2)⁻¹ ^ 2 with hκdef
    have hrr_nonneg : 0 ≤ rr := by positivity
    have hκle : κ ≤ 8 := by
      simpa [κ, rr] using kpCoeff_le_eight hrr_nonneg (by simpa [rr] using httG64)
    have hdiff :=
      norm_mayerExpansionTermComplex_tsum_sub_Gavoid_le_support_card_complex
        (G := G) (C := C) (z := t) hkpt hρt
    have hdiff8 :
        ‖(∑' n : ℕ, mayerExpansionTermComplex G n t)
            - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n t)‖
          ≤ 8 * ((polymerSupport C).card : ℝ) := by
      calc
        ‖(∑' n : ℕ, mayerExpansionTermComplex G n t)
            - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n t)‖
          ≤ κ * ((polymerSupport C).card : ℝ) := by simpa [κ, rr] using hdiff
        _ ≤ 8 * ((polymerSupport C).card : ℝ) := by
          exact mul_le_mul_of_nonneg_right hκle (by positivity)
    have hratio :=
      norm_htSubgraphSumAvoiding_div_htSubgraphSum_empty_le
        (G := G) (C := C) (R := R) hRpos hkpR hρR htz
    have hsupp_nat : (polymerSupport C).card ≤ C.card + 1 :=
      polymerSupport_card_le_card_add_one_of_isEdgeConnected G hCsub hCne hCconn
    have hsupp_real : ((polymerSupport C).card : ℝ) ≤ (C.card : ℝ) + 1 := by
      exact_mod_cast hsupp_nat
    have hratio8 :
        ‖htSubgraphSumAvoiding G C t / htSubgraphSum G (∅ : Finset ι) t‖
          ≤ Real.exp (8 * ((C.card : ℝ) + 1)) := by
      calc
        ‖htSubgraphSumAvoiding G C t / htSubgraphSum G (∅ : Finset ι) t‖
          ≤ Real.exp ‖(∑' n : ℕ, mayerExpansionTermComplex G n t)
              - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n t)‖ := hratio
        _ ≤ Real.exp (8 * ((polymerSupport C).card : ℝ)) := by
          exact Real.exp_le_exp.mpr hdiff8
        _ ≤ Real.exp (8 * ((C.card : ℝ) + 1)) := by
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsupp_real (by norm_num))
    have htpow : ‖t‖ ^ C.card ≤ R ^ C.card :=
      pow_le_pow_left₀ (norm_nonneg t) htRle C.card
    calc
      ‖t‖ ^ C.card * ‖htSubgraphSumAvoiding G C t / htSubgraphSum G (∅ : Finset ι) t‖
        ≤ R ^ C.card * Real.exp (8 * ((C.card : ℝ) + 1)) := by
          exact mul_le_mul htpow hratio8 (norm_nonneg _) (pow_nonneg hRnonneg _)
      _ = A * a ^ C.card := by
          rw [hAdef, hadef]
          exact activity_exp_card_identity R C.card
  have hratioBound :=
    twoPointRatio_norm_le_geometric (G := G) (i := i) (j := j) hij t A a hAnonneg hanonneg hper hqG
  have hcompare :
      A / (1 - a * ((G.maxDegree : ℝ) ^ 2)) ≤ twoPointHTBoundValue Δ := by
    have hgΔ : a * ((G.maxDegree : ℝ) ^ 2) ≤ a * ((Δ : ℝ) ^ 2) := by gcongr
    have hdenle : 1 - a * ((Δ : ℝ) ^ 2) ≤ 1 - a * ((G.maxDegree : ℝ) ^ 2) := by
      linarith
    have hinv : (1 - a * ((G.maxDegree : ℝ) ^ 2))⁻¹ ≤
        (1 - a * ((Δ : ℝ) ^ 2))⁻¹ := by
      exact inv_anti₀ hdenΔpos hdenle
    have hmul : A * (1 - a * ((G.maxDegree : ℝ) ^ 2))⁻¹ ≤
        A * (1 - a * ((Δ : ℝ) ^ 2))⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hAnonneg
    calc
      A / (1 - a * ((G.maxDegree : ℝ) ^ 2))
          = A * (1 - a * ((G.maxDegree : ℝ) ^ 2))⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ A * (1 - a * ((Δ : ℝ) ^ 2))⁻¹ := hmul
      _ = twoPointHTBoundValue Δ := by
        rw [twoPointHTBoundValue, hAdef, hadef, hRdef, div_eq_mul_inv]
  calc
    ‖correlationComplex G ({i, j} : Finset ι) (J : ℂ) 0 β‖
      = ‖htSubgraphSum G ({i, j} : Finset ι) t / htSubgraphSum G (∅ : Finset ι) t‖ := by
        rw [hExp β hβExp]
    _ ≤ A / (1 - a * ((G.maxDegree : ℝ) ^ 2)) := hratioBound
    _ ≤ twoPointHTBoundValue Δ := hcompare

end IsingModel
