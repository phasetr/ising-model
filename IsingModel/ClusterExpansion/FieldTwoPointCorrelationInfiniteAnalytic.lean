import IsingModel.ClusterExpansion.FieldCorrelationVitali
import IsingModel.ClusterExpansion.FieldVolumeUniformZNonvanishing
import IsingModel.ClusterExpansion.FieldPolymerComplexNonvanishing
import IsingModel.ClusterExpansion.FieldCorrelationBallUniform
import IsingModel.RealTanhAux

/-!
# High-temperature `∂/∂h` analyticity capstone (GJ §17.6.1, brick F6c)

This file discharges, **at high temperature** (small coupling `a = β·J`), the two shared
hypotheses of the field (`∂/∂h`) Vitali/Montel consumer (brick F6a,
`fieldCorrelationℂAlongExhaustion_analytic_of_volume_uniform_bound`), yielding the
unconditional Glimm–Jaffe Theorem 17.6.1 `∂/∂h` analyticity of the infinite-volume field
correlation.  It is the field analogue of the `β`-route high-temperature capstone
`correlationInfinite_latticeGraph_two_point_analytic_high_temp`
(`TwoPointCorrelationInfiniteAnalytic.lean`).  The `β` Vitali/analyticity stack and the
already-merged field bricks are **not** modified — this is a pure addition.

## Variable roles (field vs `β`)
For the field route the varying complex parameter is the field `b` (`= β·h`); the coupling
`a` (`= β·J`) is held fixed and made small (high temperature).  The radius `r` bounds the
varying field `b`; the high-temperature parameter `a` and the accumulation field `b₀` are
therefore **separated** (`∀ r, ∃ a₀, ∀ a < a₀, ∀ b₀ < r`), one quantifier layer deeper than
the `β` route where the small parameter and the accumulation point coincided.

## Main results
* `exists_ctanh_ball_bound` (private) — a ball-uniform bound `Mr` for `‖Complex.tanh z‖` on
  `‖z‖ ≤ r` (`r < π/2`), from compactness of the closed ball and continuity of `Complex.tanh`.
* `kpRegion8_of_le_sixteenth` (private) — the factor-`8` Kotecký–Preiss tail threshold: for
  `0 ≤ X ≤ 1/16`, both `X < 1` and `8·X/(1-X)² < 1`.  The `1/16` cutoff is a convenient
  conservative bound, not the sharp one: the sharp cutoff is the smaller positive root
  `5 - √24 ≈ 0.101` of `X² - 10X + 1` (any `X ≤ 5 - √24` works); `1/16 = 0.0625` sits safely
  below it, whereas the factor-`4` `β`-tail's `1/9 ≈ 0.111` already exceeds it and fails here.
* `exists_field_high_temp_window` (private) — the sole new mathematics: existence of a
  simultaneous high-temperature window `(ρ, Awin, a₀)` meeting the shared KP conditions
  (`hkpstar`, `hρwinstar`) and, for `a ∈ [0, a₀)`, the field-specific `hqstar`.
* `fieldCorrelationInfinite_latticeGraph_analytic_high_temp` — the capstone: for `r < π/2`
  there is an `a₀ > 0` such that for every high-temperature coupling `a ∈ [0, a₀)` and every
  real accumulation field `b₀ ∈ [0, r)`, the per-stage complex field correlations converge
  locally uniformly on `Metric.ball 0 r` to a holomorphic `f` agreeing with
  `correlationInfinite … ⟨a, b₀, 1⟩ …` on the real axis — the unconditional GJ Theorem 17.6.1
  `∂/∂h` analyticity, closing the field cluster-expansion thread.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.6, Theorem 17.6.1,
eq. (17.6.1), p. 313; §18.3, Theorem 18.3.1, eq. (18.3.3), p. 330.  Friedli–Velenik,
*Statistical Mechanics of Lattice Systems* (CUP, 2017), §5.4, Theorem 5.4 (Kotecký–Preiss).
-/

namespace IsingModel

open Filter Topology

/-- **Ball-uniform bound for `Complex.tanh`** (GJ §17.6.1, brick F6c(i)).  For `r < π/2`
there is `Mr ≥ 1` with `‖Complex.tanh z‖ ≤ Mr` for all `‖z‖ ≤ r`.  If `r < 0` the bound is
vacuous (`Mr = 1`); otherwise the closed ball `closedBall 0 r ⊆ ball 0 (π/2)` is compact and
`Complex.tanh` is continuous on it (`differentiableOn_ctanh_ball`), so `‖Complex.tanh ·‖`
attains a maximum (`IsCompact.exists_isMaxOn`); take `Mr = max 1` of that maximum. -/
private theorem exists_ctanh_ball_bound {r : ℝ} (hrpi : r < Real.pi / 2) :
    ∃ Mr : ℝ, 1 ≤ Mr ∧ ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mr := by
  rcases lt_or_ge r 0 with hrneg | hr
  · refine ⟨1, le_refl 1, ?_⟩
    intro z hz
    exact absurd (le_trans (norm_nonneg z) hz) (not_le.mpr hrneg)
  · have hsub : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) (Real.pi / 2) := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hcont : ContinuousOn (fun z : ℂ => ‖Complex.tanh z‖)
        (Metric.closedBall (0 : ℂ) r) :=
      continuous_norm.comp_continuousOn
        (differentiableOn_ctanh_ball.continuousOn.mono hsub)
    obtain ⟨x₀, hx₀mem, hx₀max⟩ :=
      (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn
        ⟨0, by rw [Metric.mem_closedBall, dist_self]; exact hr⟩ hcont
    refine ⟨max 1 ‖Complex.tanh x₀‖, le_max_left _ _, ?_⟩
    intro z hz
    have hzmem : z ∈ Metric.closedBall (0 : ℂ) r := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz
    calc ‖Complex.tanh z‖ ≤ ‖Complex.tanh x₀‖ := hx₀max hzmem
      _ ≤ max 1 ‖Complex.tanh x₀‖ := le_max_right _ _

/-- **Factor-`8` Kotecký–Preiss tail threshold** (GJ §17.6.1, brick F6c(ii)).  For
`0 ≤ X ≤ 1/16`, both `X < 1` and `8·X/(1-X)² < 1`.  The bound `8X ≤ (1-X)²` reduces to
`X² - 10X + 1 ≥ 0`, whose two positive roots are `5 ± √24`; the sharp cutoff is the smaller
root `5 - √24 ≈ 0.101`, so `8X/(1-X)² < 1` holds throughout `X ≤ 5 - √24` (at `X = 1/16 =
0.0625`: `8X/(1-X)² = 128/225 ≈ 0.569 < 1`).  The `1/16` value is a convenient conservative
bound below the sharp cutoff, not the sharp one; the factor-`4` `β`-tail's `1/9 ≈ 0.111`
lies above `5 - √24` and gives `8/9·(81/64) ≈ 1.125 > 1`, so it fails here. -/
private theorem kpRegion8_of_le_sixteenth {X : ℝ} (_h0 : 0 ≤ X) (h16 : X ≤ 1 / 16) :
    X < 1 ∧ 8 * X / (1 - X) ^ 2 < 1 := by
  have hX1 : X < 1 := by linarith
  refine ⟨hX1, ?_⟩
  have hpos : (0 : ℝ) < (1 - X) ^ 2 := pow_pos (by linarith) 2
  rw [div_lt_one hpos]
  nlinarith [sq_nonneg X, h16]

/-- **High-temperature window existence** (GJ §17.6.1, brick F6c(ii); TeX §F6c, the sole new
mathematics of the `∂/∂h` capstone).  Given `d`, an observable cardinality `Acard`, and a
ball-uniform bound `Mr ≥ 1` for `Complex.tanh`, there is a simultaneous window
`(ρ, Awin, a₀)` with `0 < ρ`, `0 < Awin`, `0 < a₀ ≤ Awin`, `tanh Awin < ρ`, meeting the two
shared Kotecký–Preiss conditions
`X := (2d)²·e·((max 1 Mr)²·ρ) < 1` (`hkpstar`) and `8X/(1-X)² < 1` (`hρwinstar`), and, for
every `a ∈ [0, a₀)`, the field-specific window
`(max 1 Mr)²·e^{2κ(D*(a))}·|tanh a|·(2^{Acard}·(2d)²) < 1` (`hqstar`), where
`κ = fieldCEKappaOfActivity` and `D*(a) = (2d)²·e·((max 1 Mr)²·|tanh a|)`.

Construction (three successive steps, TeX §F6c — not independent: `Awin`/`a_C` depend on the
`ρ` (hence `κ(X)`) fixed at the first step):
* `ρ := 1/(16·e·(max 1 Mr)²·((2d)²+1))` makes `X = (2d)²/((2d)²+1)·(1/16) ≤ 1/16`, so
  `kpRegion8_of_le_sixteenth` gives both KP conditions (the `+1` avoids division by zero at
  `d = 0`);
* `Awin := ε/2` from continuity of `tanh` at `0` (`tanh 0 = 0 < ρ`) gives `tanh Awin < ρ`,
  and `|tanh a| < ρ` for `a ∈ [0, Awin)`;
* on `[0, Awin)`, `D*(a) ≤ X ≤ 1/16` secures the `κ`-monotone downcast
  `κ(D*(a)) ≤ κ(X) =: κ₀` (`fieldCEKappaOfActivity_mono`), so `hqstar`'s left side is
  `≤ C·|tanh a|` with a constant `C`; continuity of `a ↦ C·|tanh a|` at `0` (value `0 < 1`)
  gives `a_C`, and `a₀ := min Awin a_C`. -/
private theorem exists_field_high_temp_window (d Acard : ℕ) (Mr : ℝ) (_hMr1 : 1 ≤ Mr) :
    ∃ ρ Awin a₀ : ℝ, 0 < ρ ∧ 0 < Awin ∧ 0 < a₀ ∧ a₀ ≤ Awin ∧
      Real.tanh Awin < ρ ∧
      (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mr) ^ 2 * ρ)) < 1) ∧
      (8 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mr) ^ 2 * ρ)))
          / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mr) ^ 2 * ρ))) ^ 2 < 1) ∧
      (∀ a : ℝ, 0 ≤ a → a < a₀ →
        (max 1 Mr) ^ 2 *
            Real.exp (2 * fieldCEKappaOfActivity (((2 * d : ℕ) : ℝ) ^ 2 *
              (Real.exp 1 * ((max 1 Mr) ^ 2 * |Real.tanh a|)))) *
            |Real.tanh a| * (2 ^ Acard * ((2 * d : ℕ) : ℝ) ^ 2) < 1) := by
  classical
  have hE : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  set M : ℝ := max 1 Mr with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
  have hM2pos : (0 : ℝ) < M ^ 2 := pow_pos hM0 2
  set Δ2 : ℝ := ((2 * d : ℕ) : ℝ) ^ 2 with hΔ2def
  have hΔ0 : (0 : ℝ) ≤ Δ2 := by rw [hΔ2def]; positivity
  have hΔ1pos : (0 : ℝ) < Δ2 + 1 := by linarith
  -- (a) small `ρ` ⟹ both KP-window conditions
  set ρ₀ : ℝ := 1 / (16 * Real.exp 1 * M ^ 2 * (Δ2 + 1)) with hρ₀def
  have hden0 : (0 : ℝ) < 16 * Real.exp 1 * M ^ 2 * (Δ2 + 1) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hE) hM2pos) hΔ1pos
  have hρ₀0 : 0 < ρ₀ := by rw [hρ₀def]; exact div_pos one_pos hden0
  have hEne : Real.exp 1 ≠ 0 := ne_of_gt hE
  have hM2ne : M ^ 2 ≠ 0 := ne_of_gt hM2pos
  have hΔ1ne : Δ2 + 1 ≠ 0 := ne_of_gt hΔ1pos
  have hXeq : Δ2 * (Real.exp 1 * (M ^ 2 * ρ₀)) = Δ2 / (16 * (Δ2 + 1)) := by
    rw [hρ₀def]; field_simp
  have hX0 : 0 ≤ Δ2 * (Real.exp 1 * (M ^ 2 * ρ₀)) := by
    rw [hXeq]
    exact div_nonneg hΔ0 (le_of_lt (mul_pos (by norm_num) hΔ1pos))
  have hX16 : Δ2 * (Real.exp 1 * (M ^ 2 * ρ₀)) ≤ 1 / 16 := by
    rw [hXeq, div_le_div_iff₀ (mul_pos (by norm_num) hΔ1pos) (by norm_num : (0 : ℝ) < 16)]
    nlinarith [hΔ0]
  obtain ⟨hkpstarFact, hρwinFact⟩ := kpRegion8_of_le_sixteenth hX0 hX16
  -- continuity of the real hyperbolic tangent (mathlib-only, avoids a heavy import)
  have htanh_cont : Continuous Real.tanh := by
    rw [show Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x from
      funext Real.tanh_eq_sinh_div_cosh]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  -- (b) an `Awin > 0` with `tanh Awin < ρ₀`
  have hev : ∀ᶠ x in nhds (0 : ℝ), Real.tanh x < ρ₀ :=
    (htanh_cont.tendsto 0).eventually_lt tendsto_const_nhds
      (by rw [Real.tanh_zero]; exact hρ₀0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set Awin : ℝ := ε / 2 with hAwindef
  have hAwin0 : 0 < Awin := by rw [hAwindef]; linarith
  have htanhAwin : Real.tanh Awin < ρ₀ := by
    apply hball
    rw [Real.dist_eq, sub_zero, hAwindef, abs_of_pos (by linarith)]
    linarith
  -- (c) small `a` ⟹ `hqstar`: `κ`-monotone downcast and `|tanh a| → 0`
  set κ0 : ℝ := fieldCEKappaOfActivity (Δ2 * (Real.exp 1 * (M ^ 2 * ρ₀))) with hκ0def
  set C : ℝ := M ^ 2 * Real.exp (2 * κ0) * (2 ^ Acard * Δ2) with hCdef
  have hgcont : Continuous (fun a : ℝ => C * |Real.tanh a|) :=
    continuous_const.mul htanh_cont.abs
  have hev2 : ∀ᶠ a in nhds (0 : ℝ), C * |Real.tanh a| < 1 :=
    (hgcont.tendsto 0).eventually_lt tendsto_const_nhds
      (by norm_num [Real.tanh_zero])
  obtain ⟨ε', hε', hball'⟩ := Metric.eventually_nhds_iff.mp hev2
  set aC : ℝ := ε' / 2 with haCdef
  have haC0 : 0 < aC := by rw [haCdef]; linarith
  set a₀ : ℝ := min Awin aC with ha₀def
  have ha₀0 : 0 < a₀ := lt_min hAwin0 haC0
  have ha₀Awin : a₀ ≤ Awin := min_le_left _ _
  refine ⟨ρ₀, Awin, a₀, hρ₀0, hAwin0, ha₀0, ha₀Awin, htanhAwin,
    hkpstarFact, hρwinFact, ?_⟩
  intro a ha0 halt
  have haw : a < Awin := lt_of_lt_of_le halt ha₀Awin
  have hac : a < aC := lt_of_lt_of_le halt (min_le_right _ _)
  -- `|tanh a| < ρ₀`
  have htanh_ρ : |Real.tanh a| < ρ₀ := by
    rw [abs_of_nonneg (real_tanh_nonneg ha0)]
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ha0]
    rw [hAwindef] at haw; linarith
  -- `D*(a) ≤ X` and the `κ`-monotone downcast
  have hDa0 : 0 ≤ Δ2 * (Real.exp 1 * (M ^ 2 * |Real.tanh a|)) :=
    mul_nonneg hΔ0
      (mul_nonneg (Real.exp_nonneg 1) (mul_nonneg (sq_nonneg M) (abs_nonneg _)))
  have hDaX : Δ2 * (Real.exp 1 * (M ^ 2 * |Real.tanh a|))
      ≤ Δ2 * (Real.exp 1 * (M ^ 2 * ρ₀)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (le_of_lt htanh_ρ) (sq_nonneg M))
        (Real.exp_nonneg 1))
      hΔ0
  have hκle : fieldCEKappaOfActivity (Δ2 * (Real.exp 1 * (M ^ 2 * |Real.tanh a|))) ≤ κ0 := by
    rw [hκ0def]
    exact fieldCEKappaOfActivity_mono hDa0 hDaX hkpstarFact hρwinFact
  have hexp : Real.exp (2 * fieldCEKappaOfActivity
        (Δ2 * (Real.exp 1 * (M ^ 2 * |Real.tanh a|))))
      ≤ Real.exp (2 * κ0) := Real.exp_le_exp.mpr (by linarith [hκle])
  have hCtanh : C * |Real.tanh a| < 1 := by
    apply hball'
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ha0]
    rw [haCdef] at hac; linarith
  have hP0 : 0 ≤ M ^ 2 * (2 ^ Acard * Δ2) * |Real.tanh a| :=
    mul_nonneg
      (mul_nonneg (sq_nonneg M) (mul_nonneg (pow_nonneg (by norm_num) Acard) hΔ0))
      (abs_nonneg _)
  calc M ^ 2 * Real.exp (2 * fieldCEKappaOfActivity
          (Δ2 * (Real.exp 1 * (M ^ 2 * |Real.tanh a|)))) *
        |Real.tanh a| * (2 ^ Acard * Δ2)
      = (M ^ 2 * (2 ^ Acard * Δ2) * |Real.tanh a|) *
          Real.exp (2 * fieldCEKappaOfActivity
            (Δ2 * (Real.exp 1 * (M ^ 2 * |Real.tanh a|)))) := by ring
    _ ≤ (M ^ 2 * (2 ^ Acard * Δ2) * |Real.tanh a|) * Real.exp (2 * κ0) :=
        mul_le_mul_of_nonneg_left hexp hP0
    _ = C * |Real.tanh a| := by rw [hCdef]; ring
    _ < 1 := hCtanh

namespace Ambient

/-- **Unconditional `∂/∂h` analyticity of the infinite-volume field correlation at high
temperature** (GJ §17.6.1, brick F6c capstone; Theorem 17.6.1, eq. (17.6.1), p. 313).  Fix a
nonempty observable `A` and a radius `r < π/2`.  Then there is `a₀ > 0` such that for every
high-temperature coupling `a ∈ [0, a₀)` and every real accumulation field `b₀ ∈ [0, r)`, the
per-stage complex field correlations `fun n b => fieldCorrelationℂAlongExhaustion
(latticeGraph d) Λ A a b n` converge **locally uniformly** on `Metric.ball 0 r` to a
holomorphic `f`, with `f (b₀) = ↑(correlationInfinite (latticeGraph d) Λ ⟨a, b₀, 1⟩ A)` on
the real axis.  Since `b = β·h` with `β = 1` and `J = a` fixed, holomorphy in `b` is the
`∂/∂h` analyticity of the infinite-volume correlation.

Proof (assembly of the merged bricks):
* `exists_ctanh_ball_bound` supplies the ball-uniform `Mr`;
* `exists_field_high_temp_window` supplies the shared window `(ρ, Awin, a₀)` discharging both
  `hden` (F6b, via `hkpstar`/`hρwinstar`) and `hbdd` (F5b, additionally `hqstar`);
* `hbdd` is sphered locally (each `z ∈ ball 0 r` gets radius `(r - ‖z‖)/2` and the single
  volume-uniform constant of F5b), mirroring the `β` route verbatim;
* the F6a Vitali/Montel consumer `fieldCorrelationℂAlongExhaustion_analytic_of_volume_uniform_bound`
  then returns the holomorphic limit.

The field analogue of `correlationInfinite_latticeGraph_two_point_analytic_high_temp`. -/
theorem fieldCorrelationInfinite_latticeGraph_analytic_high_temp
    (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (latticeGraph d) (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) {r : ℝ} (hr0 : 0 < r)
    (hrpi : r < Real.pi / 2) :
    ∃ a₀ > 0, ∀ a : ℝ, 0 ≤ a → a < a₀ →
      ∀ b₀ : ℝ, 0 ≤ b₀ → b₀ < r →
        ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 r) ∧
          TendstoLocallyUniformlyOn
            (fun n b => fieldCorrelationℂAlongExhaustion (latticeGraph d) Λ A a b n)
            f Filter.atTop (Metric.ball 0 r) ∧
          f (b₀ : ℂ) = ((correlationInfinite (latticeGraph d) Λ
            (⟨a, b₀, 1⟩ : IsingParams ℝ) A : ℝ) : ℂ) := by
  classical
  obtain ⟨Mr, hMr1, hMr⟩ := exists_ctanh_ball_bound hrpi
  obtain ⟨ρ, Awin, a₀, hρ0, hAwin0, ha₀0, ha₀Awin, htanhA, hkpstar, hρwinstar, hqstar⟩ :=
    exists_field_high_temp_window d A.card Mr hMr1
  refine ⟨a₀, ha₀0, ?_⟩
  intro a ha0 halt b₀ hb₀0 hb₀r
  have ha : a ∈ Set.Ico 0 Awin := ⟨ha0, lt_of_lt_of_le halt ha₀Awin⟩
  -- `hden`: volume-uniform non-vanishing of the complex field partition function (F6b)
  have hden : ∀ n : ℕ, ∀ w ∈ Metric.ball (0 : ℂ) r,
      fieldPolymerZℂ (inducedGraph (latticeGraph d) (Λ.volume n)) a w ≠ 0 :=
    fieldPolymerZℂAlongExhaustion_ne_zero_on_ball_uniform_latticeGraph
      d Λ ha hr0 hrpi hMr1 hMr hρ0 htanhA hkpstar hρwinstar
  -- `hbdd`: local sphering of the F5b volume-uniform norm bound (verbatim `β` mirror)
  have hbdd : ∀ z ∈ Metric.ball (0 : ℂ) r, ∃ ρ' M : ℝ, 0 < ρ' ∧
      Metric.ball z ρ' ⊆ Metric.ball 0 r ∧
      ∀ n, ∀ w ∈ Metric.ball z ρ',
        ‖fieldCorrelationℂAlongExhaustion (latticeGraph d) Λ A a w n‖ ≤ M := by
    intro z hz
    have hz_norm : ‖z‖ < r := by
      rw [Metric.mem_ball, dist_zero_right] at hz; exact hz
    refine ⟨(r - ‖z‖) / 2,
      (max 1 Mr) ^ A.card *
          Real.exp (fieldCEKappaOfActivity (((2 * d : ℕ) : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mr) ^ 2 * |Real.tanh a|))) * (A.card : ℝ)) /
        (1 - (max 1 Mr) ^ 2 *
          Real.exp (2 * fieldCEKappaOfActivity (((2 * d : ℕ) : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mr) ^ 2 * |Real.tanh a|)))) *
          |Real.tanh a| * (2 ^ A.card * ((2 * d : ℕ) : ℝ) ^ 2)),
      by linarith, ?_, ?_⟩
    · intro w hw
      have hwz : dist w z < (r - ‖z‖) / 2 := Metric.mem_ball.mp hw
      rw [Metric.mem_ball, dist_zero_right]
      calc ‖w‖ = dist w 0 := by rw [dist_zero_right]
        _ ≤ dist w z + dist z 0 := dist_triangle w z 0
        _ = dist w z + ‖z‖ := by rw [dist_zero_right]
        _ < (r - ‖z‖) / 2 + ‖z‖ := by linarith
        _ < r := by linarith
    · intro n w hw
      have hwU : w ∈ Metric.ball (0 : ℂ) r := by
        have hwz : dist w z < (r - ‖z‖) / 2 := Metric.mem_ball.mp hw
        rw [Metric.mem_ball, dist_zero_right]
        calc ‖w‖ = dist w 0 := by rw [dist_zero_right]
          _ ≤ dist w z + dist z 0 := dist_triangle w z 0
          _ = dist w z + ‖z‖ := by rw [dist_zero_right]
          _ < (r - ‖z‖) / 2 + ‖z‖ := by linarith
          _ < r := by linarith
      exact fieldCorrelationℂAlongExhaustion_norm_le_uniform d Λ A hA ha hr0 hrpi
        hMr1 hMr hwU hρ0 htanhA hkpstar hρwinstar (hqstar a ha0 halt) n
  -- the real accumulation field lies in the ball
  have hb₀U : (b₀ : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hb₀0]
    exact hb₀r
  exact fieldCorrelationℂAlongExhaustion_analytic_of_volume_uniform_bound
    (latticeGraph d) Λ A a ha0 (le_of_lt hrpi) hden hbdd hb₀0 hb₀U

end Ambient

end IsingModel
