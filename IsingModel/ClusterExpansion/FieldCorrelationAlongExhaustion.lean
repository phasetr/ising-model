import IsingModel.ClusterExpansion.FieldCorrelationBallUniform
import IsingModel.ClusterExpansion.MayerTsumPerSiteAmbient

/-!
# Along-exhaustion complex field correlation: the F5b exhaustion wrap (GJ §17.6.1, brick F5b-2)

This file assembles the **exhaustion wrap** of the field cluster expansion, completing
brick F5b of Glimm–Jaffe Theorem 17.6.1 (the `∂/∂h` infinite-volume derivative).  It
packages the degree-bound ball-&-volume-uniform bound
`fieldCorrelationℂ_norm_le_ball_uniform_of_degree_le` (F5b-2(b),
`FieldCorrelationBallUniform.lean`) along a lattice exhaustion, and records the
per-stage holomorphy — the two inputs that the (gated, research-level) Vitali/Montel
brick F6 consumes.

These are the field (`∂/∂h`) transcriptions of the `β`-route along-exhaustion
templates (`correlationComplexAlongExhaustion`,
`correlationComplexAlongExhaustion_two_point_norm_le_uniform`,
`AmbientComplexAnalyticity/Vitali/CorrelationBridge.lean` and
`ClusterExpansion/TwoPointCorrelationInfiniteAnalytic.lean`), with the varying
complex parameter changed from the inverse temperature `β` to the field `b` (the
coupling `a` is held fixed).  No new mathematics beyond F5b-2(b): (a)/(c)/(d) are
pure `β → b` transcriptions.

## Main results
* `fieldCorrelationℂAlongExhaustion` (F5b-2(a)) — the per-stage complex field
  correlation along the exhaustion (`= 0` before the observable's support is
  engulfed), the field analogue of `correlationComplexAlongExhaustion`.
* `fieldCorrelationℂAlongExhaustion_norm_le_uniform` (F5b-2(c)) — for the lattice
  exhaustion, feeding `induced_latticeGraph_maxDegree_le` (`Δ = 2d`) into F5b-2(b),
  every stage is bounded by a single `n`-independent (and `b`-independent on the
  ball) constant.  This is the volume-uniform `hbdd` datum for F6.
* `fieldCorrelationℂAlongExhaustion_analyticOnNhd` (F5b-2(d)) — each stage is
  `AnalyticOnNhd` in the field `b` on the ball, provided the per-stage complex field
  polymer partition function is non-vanishing (`hden`, gated, discharged in F6 by
  `fieldPolymerZℂ_ne_zero_of_degree_window`).

## Scope
F5b is completed by this file.  The infinite-volume capstone — a field-specific
Vitali/Montel consumer, the uniform `hden` discharge, and GJ Theorem 17.6.1 itself —
is brick F6 (gated, research-level) and is **not** in scope here.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.6,
Theorem 17.6.1, eq. (17.6.1), p. 313.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Complex field correlation along an exhaustion** (GJ §17.6.1, brick F5b-2(a)):
the finite-volume complex field correlation `fieldCorrelationℂ` on the induced
subgraph of the stage-`n` volume, evaluated on the lifted observable `liftFinset A`
once `A ⊆ Λ.volume n` (and `0` before).  The field (`b`-varying, `a` fixed) analogue
of `correlationComplexAlongExhaustion`. -/
noncomputable def fieldCorrelationℂAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (a : ℝ) (b : ℂ) : ℕ → ℂ :=
  fun n =>
    if hsub : A ⊆ Λ.volume n then
      fieldCorrelationℂ (inducedGraph G (Λ.volume n)) (liftFinset A hsub) a b
    else 0

/-- **Per-stage holomorphy of the along-exhaustion complex field correlation**
(GJ §17.6.1, brick F5b-2(d)): on `Metric.ball 0 r` with `r ≤ π/2`, each stage
`b ↦ fieldCorrelationℂAlongExhaustion G Λ A a b n` is `AnalyticOnNhd ℂ`, provided the
per-stage complex field polymer partition function is non-vanishing on the ball
(`hden`).  The `dite` branch depends only on `n` (not `b`), so we split on it and
apply F4b (`fieldCorrelationℂ_analyticOnNhd`) on the engulfed branch, or use the
constant `0` on the pre-engulfment branch.  The field (`b`-varying) transcription of
the `β`-route per-stage analyticity; `hden` is the (gated) F6 input, discharged there
by `fieldPolymerZℂ_ne_zero_of_degree_window`. -/
theorem fieldCorrelationℂAlongExhaustion_analyticOnNhd
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (a : ℝ) {r : ℝ} (hrpi : r ≤ Real.pi / 2)
    (hden : ∀ n : ℕ, ∀ w ∈ Metric.ball (0 : ℂ) r,
        fieldPolymerZℂ (inducedGraph G (Λ.volume n)) a w ≠ 0) :
    ∀ n : ℕ, AnalyticOnNhd ℂ
        (fun b : ℂ => fieldCorrelationℂAlongExhaustion G Λ A a b n)
        (Metric.ball 0 r) := by
  intro n
  unfold fieldCorrelationℂAlongExhaustion
  by_cases hsub : A ⊆ Λ.volume n
  · simp only [dif_pos hsub]
    exact fieldCorrelationℂ_analyticOnNhd (inducedGraph G (Λ.volume n))
      (liftFinset A hsub) a hrpi (hden n)
  · simp only [dif_neg hsub]
    exact analyticOnNhd_const

/-- **Volume-uniform along-exhaustion complex field correlation bound**
(GJ §17.6.1, brick F5b-2(c), exhaustion wrap; TeX §F5b-2).  Along a lattice
exhaustion of `ℤ^d`, each stage is the induced subgraph of `latticeGraph d`, whose
maximum degree is `≤ 2d` (`induced_latticeGraph_maxDegree_le`).  Feeding `Δ = 2d`
into the degree-bound F5b-2(b) bound
(`fieldCorrelationℂ_norm_le_ball_uniform_of_degree_le`) gives, for **every** stage
`n` and every field `b` in the `π/2`-ball, a single bound independent of both `n`
(volume-uniform) and `b` (ball-uniform).  This is exactly the volume-uniform `hbdd`
datum required by the Montel/Vitali brick F6.

The observable `A` is required nonempty (`hA`): on the engulfed branch this supplies
`Nonempty ↑(Λ.volume n)`, which F5b-2(b) needs; on the pre-engulfment branch the
correlation is `0`, bounded by the (nonnegative) constant.  `DecidableRel` for the
induced graph is supplied by `classical`; `liftFinset_card` transports `A.card`.  The
real-number window conditions `hkpstar`/`hρwinstar`/`hqstar` stay as hypotheses
(hyp-gated at `Δ = 2d`, as in F5b-1 and the `β` wrap). -/
theorem fieldCorrelationℂAlongExhaustion_norm_le_uniform
    (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (latticeGraph d) (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty)
    {a Awin r Mrb ρ : ℝ} {b : ℂ}
    (ha : a ∈ Set.Ico 0 Awin) (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mrb)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mrb) (hbr : b ∈ Metric.ball 0 r)
    (hρ0 : 0 < ρ) (htanhA : Real.tanh Awin < ρ)
    (hkpstar : ((2 * d : ℕ) : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ)) < 1)
    (hρwinstar : 8 * (((2 * d : ℕ) : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ)))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ))) ^ 2 < 1)
    (hqstar : (max 1 Mrb) ^ 2 *
          Real.exp (2 * fieldCEKappaOfActivity (((2 * d : ℕ) : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
          |Real.tanh a| * (2 ^ A.card * ((2 * d : ℕ) : ℝ) ^ 2) < 1) :
    ∀ n : ℕ,
      ‖fieldCorrelationℂAlongExhaustion (latticeGraph d) Λ A a b n‖
        ≤ (max 1 Mrb) ^ A.card *
              Real.exp (fieldCEKappaOfActivity (((2 * d : ℕ) : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))) * (A.card : ℝ)) /
            (1 - (max 1 Mrb) ^ 2 *
              Real.exp (2 * fieldCEKappaOfActivity (((2 * d : ℕ) : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
              |Real.tanh a| * (2 ^ A.card * ((2 * d : ℕ) : ℝ) ^ 2)) := by
  classical
  intro n
  unfold fieldCorrelationℂAlongExhaustion
  by_cases hsub : A ⊆ Λ.volume n
  · simp only [dif_pos hsub]
    obtain ⟨v, hv⟩ := hA
    haveI : Nonempty (↑(Λ.volume n) : Type _) := ⟨⟨v, hsub hv⟩⟩
    have hcard : (liftFinset A hsub).card = A.card := liftFinset_card hsub
    have hbound :=
      fieldCorrelationℂ_norm_le_ball_uniform_of_degree_le
        (G := inducedGraph (latticeGraph d) (Λ.volume n))
        (liftFinset A hsub) (2 * d)
        (induced_latticeGraph_maxDegree_le d (Λ.volume n))
        ha hr0 hrpi hMr1 hMr hbr hρ0 htanhA hkpstar hρwinstar (by rw [hcard]; exact hqstar)
    rw [hcard] at hbound
    exact hbound
  · rw [dif_neg hsub, norm_zero]
    have hden : (0 : ℝ) < 1 - (max 1 Mrb) ^ 2 *
        Real.exp (2 * fieldCEKappaOfActivity (((2 * d : ℕ) : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
        |Real.tanh a| * (2 ^ A.card * ((2 * d : ℕ) : ℝ) ^ 2) := by linarith [hqstar]
    exact div_nonneg
      (mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (Real.exp_nonneg _))
      (le_of_lt hden)

end Ambient

end IsingModel
