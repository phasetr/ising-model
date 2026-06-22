import IsingModel.AmbientComplexAnalyticity.VolumeUniformHZ
import IsingModel.ComplexAnalyticity.HighTempExpansion

/-!
# Volume-uniform complex `Z` polymer identity (GJ §18.4–18.6)

Discharges the structural input `VolumeUniformZComplexIdentity` of the volume-uniform `hZ` provider
(`AmbientComplexAnalyticity/VolumeUniformHZ.lean`), the easier half of the volume-uniform complex
partition-function non-vanishing (Issue #4230, item D of #4214).

The complex high-temperature polymer factorization
`Z_ℂ = 2^{|V|}·cosh(βJ)^{|E|}·∑_Γ ∏_P tanh(βJ)^{|P|}` holds (per fixed volume) on the disc where
`Complex.cosh (βJ) ≠ 0` (the per-volume
`partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_near_zero_beta`).
That disc is governed only by the zeros of `cosh(βJ)`, which depend on `β, J` but **not** on the
volume `n` — so a *single* radius works for every exhaustion stage simultaneously, giving the
volume-uniform identity.

## Main result
* `volumeUniformZComplexIdentity_of_forall` — `VolumeUniformZComplexIdentity G Λ J` for every `G`,
  `Λ`, `J`.

This is Ising-side content and is fully proven.  Combined with the volume-uniform lower bound
`VolumeUniformComplexHTBound` (a follow-up PR) it discharges, via
`volume_uniform_Z_ne_zero_of_HT_bound_and_identity`, the volume-uniform partition non-vanishing
needed for the infinite-volume correlation analyticity.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.4–18.6.
-/

namespace IsingModel

namespace Ambient

open Filter Topology

variable {V : Type*} [DecidableEq V]

/-- **Volume-uniform complex `Z` polymer identity** (GJ §18.4–18.6): the complex high-temperature
polymer factorization of the along-exhaustion partition function holds on a *single* disc
`closedBall 0 r` for every exhaustion stage `n`.  The radius `r` is chosen `n`-independently so that
`Complex.cosh (βJ) ≠ 0` there; the per-volume identity
(the per-volume `_near_zero_beta` identity) then extends to
the whole disc by the identity theorem, stage by stage. -/
theorem volumeUniformZComplexIdentity_of_forall
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) :
    VolumeUniformZComplexIdentity G Λ J := by
  classical
  -- an `n`-independent disc around `0` on which `cosh (βJ) ≠ 0`
  have h_cosh0 : Complex.cosh ((0 : ℂ) * (J : ℂ)) ≠ 0 := by
    rw [zero_mul, Complex.cosh_zero]; exact one_ne_zero
  have h_cosh_ev : ∀ᶠ β : ℂ in 𝓝 (0 : ℂ), Complex.cosh (β * (J : ℂ)) ≠ 0 :=
    (Complex.continuous_cosh.comp (continuous_id.mul continuous_const)).continuousAt.eventually_ne
      h_cosh0
  rw [Metric.eventually_nhds_iff_ball] at h_cosh_ev
  obtain ⟨ρ, hρ, h_cosh_ne⟩ := h_cosh_ev
  refine ⟨ρ / 2, by linarith, ?_⟩
  intro n β hβ
  set U : Set ℂ := Metric.ball (0 : ℂ) ρ with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUpre : IsPreconnected U := (convex_ball (0 : ℂ) ρ).isPreconnected
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self hρ
  have hβU : β ∈ U := by
    rw [Metric.mem_closedBall] at hβ
    rw [hU, Metric.mem_ball]; linarith
  have hcoshU : ∀ z ∈ U, Complex.cosh (z * (J : ℂ)) ≠ 0 := by
    intro z hz; exact h_cosh_ne z (by rwa [hU] at hz)
  -- the RHS of the factorization, as a function of `β`
  set g : ℂ → ℂ := fun β => (2 : ℂ) ^ Fintype.card (↑(Λ.volume n) : Type _) *
      Complex.cosh (β * (J : ℂ)) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
      ∑ Γ ∈ vdCompatiblePolymerFamilies (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Complex.tanh (β * (J : ℂ)) ^ P.card with hg
  -- LHS analytic on `U`
  have hZanal : AnalyticOnNhd ℂ
      (fun β : ℂ => partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) 0 β n) U := by
    intro z _
    simpa [partitionFunctionComplexAlongExhaustion_apply] using
      partitionFunctionComplex_analyticAt_beta (inducedGraph G (Λ.volume n)) (J : ℂ) 0 z
  -- RHS analytic on `U` (cosh entire, tanh analytic where cosh ≠ 0)
  have hGanal : AnalyticOnNhd ℂ g U := by
    intro z hz
    have hcosh_z : Complex.cosh (z * (J : ℂ)) ≠ 0 := hcoshU z hz
    have h_poly_tanh : AnalyticAt ℂ (fun β' : ℂ =>
        ∑ Γ ∈ vdCompatiblePolymerFamilies (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Complex.tanh (β' * (J : ℂ)) ^ P.card) z :=
      vdPolymerFamilies_sum_tanh_analyticAt_complex_beta
        (inducedGraph G (Λ.volume n)) (J : ℂ) z hcosh_z
    have h_cosh_pow : AnalyticAt ℂ (fun β' : ℂ =>
        Complex.cosh (β' * (J : ℂ)) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card) z := by
      have h_mul : AnalyticAt ℂ (fun β' : ℂ => β' * (J : ℂ)) z :=
        analyticAt_id.mul analyticAt_const
      have h_cosh_at : AnalyticAt ℂ Complex.cosh (z * (J : ℂ)) :=
        Complex.analyticOnNhd_cosh (s := Set.univ) (z * (J : ℂ)) (Set.mem_univ _)
      have h_comp : AnalyticAt ℂ (Complex.cosh ∘ (fun β' : ℂ => β' * (J : ℂ))) z := by
        refine AnalyticAt.comp ?_ h_mul
        exact h_cosh_at
      exact h_comp.pow _
    have h_two_pow : AnalyticAt ℂ
        (fun _ : ℂ => (2 : ℂ) ^ Fintype.card (↑(Λ.volume n) : Type _)) z := analyticAt_const
    simpa only [hg] using (h_two_pow.mul h_cosh_pow).mul h_poly_tanh
  -- the per-volume identity gives eventual agreement near `0`
  have hev : (fun β : ℂ => partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) 0 β n)
      =ᶠ[𝓝 (0 : ℂ)] g := by
    filter_upwards
      [partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_near_zero_beta
        (inducedGraph G (Λ.volume n)) J] with β hβ'
    simpa [hg, partitionFunctionComplexAlongExhaustion_apply] using hβ'
  -- identity theorem on the uniform disc, then `Fintype.card ↑s = s.card`
  have hEqOn := hZanal.eqOn_of_preconnected_of_eventuallyEq hGanal hUpre h0U hev
  have := hEqOn hβU
  simpa [hg, Fintype.card_coe] using this

end Ambient

end IsingModel
