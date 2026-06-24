import IsingModel.ClusterExpansion.TwoPointCorrelationInfiniteAnalytic
import Mathlib.Topology.Connected.LocallyConnected

/-!
# The complex high-temperature convergence region for the two-point cluster expansion

Toward eliminating the last declared axiom (§17.5 derivative-limit provider, Issue #4289): this file
defines the open connected complex domain on which the degree-uniform two-point cluster expansion
converges, namely the connected component of `0` of
`{β : ‖tanh(βJ)‖ < twoPointHTActivityRadius (2d) ∧ cosh(βJ) ≠ 0}`, and proves it is open,
preconnected, contains `0`, carries the `cosh≠0`/activity-radius conditions, and contains the real
high-temperature sub-interval.

This is the natural domain on which the connected-domain ratio identity and norm bound
(#4290/#4291) apply, feeding the Vitali–Porter analyticity bridge (`#4235`, now axiom-free) to give
locally-uniform convergence on a genuine sub-window of the high-temperature interval.

**Reference:** Glimm–Jaffe, 2nd ed., §18.6–18.7; §17.5 pp. 311–312. -/

namespace IsingModel
namespace ConvergenceRegion

open Filter Topology Set

variable (d : ℕ) (J : ℝ)

/-- The degree-uniform two-point activity radius (abbreviation). -/
noncomputable def R : ℝ := twoPointHTActivityRadius (2 * d)

/-- The base high-temperature set: activity inside the radius and `cosh ≠ 0`. -/
def S : Set ℂ :=
  {β : ℂ | ‖Complex.tanh (β * (J : ℂ))‖ < R d ∧ Complex.cosh (β * (J : ℂ)) ≠ 0}

/-- The convergence region: the connected component of `0` in `S`. -/
def U : Set ℂ := connectedComponentIn (S d J) 0

/-- `Real.tanh` is monotone (derived from `sinh` monotonicity and the subtraction formula). -/
private theorem real_tanh_monotone : Monotone Real.tanh := by
  intro a b hab
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_le_div_iff₀ (Real.cosh_pos a) (Real.cosh_pos b)]
  have hsub : Real.sinh (a - b) ≤ 0 := by
    rw [← Real.sinh_zero]
    exact Real.sinh_strictMono.monotone (by linarith)
  have hform := Real.sinh_sub a b
  nlinarith [hform, hsub]

/-- `0 ∈ S`. -/
theorem zero_mem_S : (0 : ℂ) ∈ S d J := by
  refine ⟨?_, ?_⟩
  · rw [zero_mul, Complex.tanh_zero, norm_zero]
    simpa [R] using twoPointHTActivityRadius_pos (2 * d)
  · rw [zero_mul, Complex.cosh_zero]; exact one_ne_zero

/-- `S` is open. -/
theorem isOpen_S : IsOpen (S d J) := by
  rw [isOpen_iff_mem_nhds]
  intro β₀ hβ₀
  obtain ⟨htβ₀, hcβ₀⟩ := hβ₀
  have hc_cont : Continuous (fun β : ℂ => Complex.cosh (β * (J : ℂ))) :=
    Complex.continuous_cosh.comp (continuous_id.mul continuous_const)
  have hcosh_nbhd : {β : ℂ | Complex.cosh (β * (J : ℂ)) ≠ 0} ∈ 𝓝 β₀ :=
    hc_cont.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hcβ₀)
  have htanh_contAt : ContinuousAt (fun β : ℂ => Complex.tanh (β * (J : ℂ))) β₀ := by
    have hsinh : ContinuousAt (fun β : ℂ => Complex.sinh (β * (J : ℂ))) β₀ :=
      (Complex.continuous_sinh.comp (continuous_id.mul continuous_const)).continuousAt
    have hcosh : ContinuousAt (fun β : ℂ => Complex.cosh (β * (J : ℂ))) β₀ :=
      (Complex.continuous_cosh.comp (continuous_id.mul continuous_const)).continuousAt
    have heq : (fun β : ℂ => Complex.tanh (β * (J : ℂ))) =
        fun β : ℂ => Complex.sinh (β * (J : ℂ)) / Complex.cosh (β * (J : ℂ)) := by
      funext β; rw [Complex.tanh_eq_sinh_div_cosh]
    rw [heq]
    exact hsinh.div hcosh hcβ₀
  have hnorm_nbhd : {β : ℂ | ‖Complex.tanh (β * (J : ℂ))‖ < R d} ∈ 𝓝 β₀ :=
    htanh_contAt.norm.preimage_mem_nhds (isOpen_Iio.mem_nhds htβ₀)
  exact Filter.mem_of_superset (Filter.inter_mem hnorm_nbhd hcosh_nbhd)
    (fun β hβ => ⟨hβ.1, hβ.2⟩)

/-- The convergence region is open (`ℂ` is locally connected). -/
theorem isOpen_U : IsOpen (U d J) := (isOpen_S d J).connectedComponentIn

/-- The convergence region is preconnected. -/
theorem isPreconnected_U : IsPreconnected (U d J) := isPreconnected_connectedComponentIn

/-- `0` lies in the convergence region. -/
theorem zero_mem_U : (0 : ℂ) ∈ U d J := mem_connectedComponentIn (zero_mem_S d J)

/-- The convergence region is contained in the base set. -/
theorem U_subset_S : U d J ⊆ S d J := connectedComponentIn_subset (S d J) 0

/-- On the convergence region, `cosh(βJ) ≠ 0`. -/
theorem cosh_ne_zero_of_mem_U {z : ℂ} (hz : z ∈ U d J) :
    Complex.cosh (z * (J : ℂ)) ≠ 0 := (U_subset_S d J hz).2

/-- On the convergence region, the activity stays strictly inside the radius. -/
theorem norm_tanh_lt_of_mem_U {z : ℂ} (hz : z ∈ U d J) :
    ‖Complex.tanh (z * (J : ℂ))‖ < R d := (U_subset_S d J hz).1

/-- **Real membership.** A nonnegative real inverse temperature whose activity is inside the radius
lies in the convergence region, provided `0 ≤ J`. The embedded segment `[0, β] ↪ ℂ` is a
preconnected subset of `S` through `0`, hence inside the component `U`. -/
theorem ofReal_mem_U {β : ℝ} (hβ : 0 ≤ β)
    (hβR : ‖Complex.tanh ((β : ℂ) * (J : ℂ))‖ < R d) (hJ : 0 ≤ J) :
    (β : ℂ) ∈ U d J := by
  have hTpre : IsPreconnected (Complex.ofReal '' Set.Icc 0 β) :=
    (isPreconnected_Icc).image _ Complex.continuous_ofReal.continuousOn
  have h0T : (0 : ℂ) ∈ Complex.ofReal '' Set.Icc 0 β :=
    ⟨0, Set.left_mem_Icc.mpr hβ, Complex.ofReal_zero⟩
  have hTS : Complex.ofReal '' Set.Icc 0 β ⊆ S d J := by
    rintro _ ⟨s, ⟨hs0, hsβ⟩, rfl⟩
    have hcast : (s : ℂ) * (J : ℂ) = ((s * J : ℝ) : ℂ) := by rw [Complex.ofReal_mul]
    have ha : (0 : ℝ) ≤ s * J := mul_nonneg hs0 hJ
    have hab : s * J ≤ β * J := mul_le_mul_of_nonneg_right hsβ hJ
    have hβcast : (β : ℂ) * (J : ℂ) = ((β * J : ℝ) : ℂ) := by rw [Complex.ofReal_mul]
    have hβR' : |Real.tanh (β * J)| < R d := by
      rwa [hβcast, ← Complex.ofReal_tanh, Complex.norm_real, Real.norm_eq_abs] at hβR
    refine ⟨?_, ?_⟩
    · rw [hcast, ← Complex.ofReal_tanh, Complex.norm_real, Real.norm_eq_abs]
      have h1 : (0 : ℝ) ≤ Real.tanh (s * J) := by
        rw [← Real.tanh_zero]; exact real_tanh_monotone ha
      calc |Real.tanh (s * J)| = Real.tanh (s * J) := abs_of_nonneg h1
        _ ≤ Real.tanh (β * J) := real_tanh_monotone hab
        _ ≤ |Real.tanh (β * J)| := le_abs_self _
        _ < R d := hβR'
    · rw [hcast, ← Complex.ofReal_cosh]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.cosh_pos _))
  exact (hTpre.subset_connectedComponentIn h0T hTS) ⟨β, Set.right_mem_Icc.mpr hβ, rfl⟩

end ConvergenceRegion
end IsingModel
