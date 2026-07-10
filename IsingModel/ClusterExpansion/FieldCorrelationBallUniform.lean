import IsingModel.ClusterExpansion.FieldCorrelationUniformBound

/-!
# Ball-&-volume-uniform complex field correlation bound (GJ §17.6.1, brick F5b-1)

This file upgrades the **pointwise-in-`b`** volume-uniform bound of brick F5a-3
(`fieldCorrelationℂ_norm_le_uniform`, `FieldCorrelationUniformBound.lean`) into a
bound that is additionally **uniform over the whole `π/2`-ball** in the complex
field `b`.  It is the field (`∂/∂h`) analogue of the ball-uniform two-point ratio
control needed to feed the Montel/Vitali brick F6.  No new analytic content is
required beyond F5a-3; the content is the monotonicity of the Kotecký–Preiss
closed form in the single polymer **activity** scalar
`D = Δ²·e·(M²·|tanh a|)` (math-before-code
`.self-local/tex/thm-17-6-1-h-F5a1-per-source-weight-bound.tex`, §F5b-1
`sec:f5b1`).

## The activity `D` and the closed form `κ(D)`
Every constant in the F5a-3 bound `A₀/(1-q)` factors through the single scalar
`D` (`fieldCEActivity`):
* `κ_Δ = fieldCEKappaDelta G a b = κ(D)` where
  `κ(D) = (1-D)⁻¹·((1 - 8D/(1-D)²)⁻¹)²` (`fieldCEKappaOfActivity`),
* `A₀ = M^{|A|}·e^{κ_Δ|A|}`, `q = M²·e^{2κ_Δ}·|tanh a|·(2^{|A|}·Δ²)`,
with `M = max 1 ‖Complex.tanh b‖`, `Δ = G.maxDegree`.  On the F5-pre-2a degree
window (`0 ≤ D < 1`, `8D/(1-D)² < 1`) the closed form `κ(D)` is monotone
increasing in `D` (`fieldCEKappaOfActivity_mono`), and so is the whole constant
`A₀/(1-q)`.

## The two headlines
* `fieldCEKappaDelta_le_of_activity_le` (the crux, `D`-monotonicity): if the
  pointwise activity `fieldCEActivity G a b` is `≤ D*` (a larger, `b`-free
  activity), then `κ_Δ ≤ κ(D*)`.
* `fieldCorrelationℂ_norm_le_ball_uniform` (the ball-uniform bound): with
  `Mstar = max 1 Mrb` the F5-pre-2a ball-uniform envelope of `‖tanh b‖`, and the
  strengthened `Mstar`-window, `‖fieldCorrelationℂ G A a b‖ ≤ A₀*/(1-q*)` with
  `A₀*, q*` the constants at the `Mstar`-activity — a bound **independent of `b`**
  over the whole ball.

## Pitfalls (TeX §F5b-1, `rem:f5b1-pitfalls`)
`Mstar = max 1 Mrb` is the uniform *envelope* of the pointwise
`M = max 1 ‖tanh b‖`; it is used **only** to bound the activity `D ≤ D*`, and is
never substituted into the pointwise `κ_Δ` that already embeds `M` (doing so would
desynchronise the activity from its own KP exponent).  Window positivity
(`1-D* > 0`, `1-ρ*(D*) > 0`, `1-q* > 0`) is load-bearing at the extremum and
downcasts to the pointwise positivity of F5a-3 via `D ≤ D*`.  The scalars `D` and
`q` are distinct (`q = 2^{|A|}·e^{2κ_Δ-1}·D`); monotonicity of `q` in `D` is
derived, not definitional.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.6,
Theorem 17.6.1, eq. (17.6.1), p. 313, and §18.3, Theorem 18.3.1, eq. (18.3.3),
p. 330; Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (CUP, 2017),
§5.4, Theorem 5.4 (Kotecký–Preiss criterion), and §3.7.3, pp. 116–118.
-/

namespace IsingModel

/-- **The Kotecký–Preiss closed-form exponent as a function of the activity `D`**
(GJ §17.6.1, brick F5b-1; TeX §F5b-1).  `κ(D) = (1-D)⁻¹·((1 - 8D/(1-D)²)⁻¹)²` is
the volume-free local KP exponent expressed purely in terms of the single polymer
activity scalar `D = Δ²·e·(M²·|tanh a|)`.  It is definitionally the exponent
`fieldCEKappaDelta` evaluated at the pointwise activity (`fieldCEActivity`), so
that the pointwise `κ_Δ` and its ball-uniform majorant `κ(D*)` are two evaluations
of the same monotone closed form. -/
noncomputable def fieldCEKappaOfActivity (D : ℝ) : ℝ :=
  (1 / (1 - D)) * (1 - 8 * D / (1 - D) ^ 2)⁻¹ ^ 2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The pointwise polymer activity** (GJ §17.6.1, brick F5b-1; TeX §F5b-1).
`D = Δ²·e·(M²·|tanh a|)` with `Δ = G.maxDegree`, `M = max 1 ‖Complex.tanh b‖`.
This single scalar bundles the two data that must be made uniform: the degree
`Δ²` (uniform along a lattice exhaustion) and the field magnitude `M²` (uniform
over the `π/2`-ball).  It is definitionally the inner activity of
`fieldCEKappaDelta`. -/
noncomputable def fieldCEActivity (G : SimpleGraph ι) [DecidableRel G.Adj]
    (a : ℝ) (b : ℂ) : ℝ :=
  (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))

omit [DecidableEq ι] in
/-- **The local KP exponent is the closed form at the pointwise activity**
(GJ §17.6.1, brick F5b-1).  `fieldCEKappaDelta G a b = κ(fieldCEActivity G a b)`,
by definitional unfolding of both sides. -/
theorem fieldCEKappaDelta_eq_kappaOfActivity (G : SimpleGraph ι) [DecidableRel G.Adj]
    (a : ℝ) (b : ℂ) :
    fieldCEKappaDelta G a b = fieldCEKappaOfActivity (fieldCEActivity G a b) := rfl

omit [DecidableEq ι] in
/-- **The pointwise activity is nonnegative** (GJ §17.6.1, brick F5b-1).  A product
of a square, a positive exponential, a square, and an absolute value. -/
theorem fieldCEActivity_nonneg (G : SimpleGraph ι) [DecidableRel G.Adj] (a : ℝ)
    (b : ℂ) : 0 ≤ fieldCEActivity G a b := by
  unfold fieldCEActivity
  positivity

/-- **Monotonicity in `M` of the raw activity expression** (GJ §17.6.1, brick
F5b-1; TeX §F5b-1 substitution).  For `M ≤ M'` with `0 ≤ M`, `0 ≤ ρ`, the raw
activity `Δ²·(e·(M²·ρ))` increases with `M`.  Used both with `ρ := |tanh a|` (to
bound the correlation activity `D ≤ D*`) and with the degree-window auxiliary
`ρ` (to downcast the F5-pre-2a window hypotheses). -/
theorem fieldCEActivity_monotone_aux {Δ ρ M M' : ℝ} (hMM : M ≤ M') (hM0 : 0 ≤ M)
    (hρ0 : 0 ≤ ρ) :
    Δ ^ 2 * (Real.exp 1 * (M ^ 2 * ρ)) ≤ Δ ^ 2 * (Real.exp 1 * (M' ^ 2 * ρ)) :=
  mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM0 hMM 2) hρ0)
      (Real.exp_nonneg 1))
    (sq_nonneg Δ)

/-- **Monotonicity of `ρ*(D) = 8D/(1-D)²` in the activity `D`** (GJ §17.6.1, brick
F5b-1; TeX Lemma `lem:kappa-mono`, step (ii)).  On `0 ≤ D ≤ D' < 1` the KP
auxiliary `8D/(1-D)²` increases: the numerator `8D` increases and the positive
denominator `(1-D)²` decreases. -/
theorem rhoStar_mono {D D' : ℝ} (hD0 : 0 ≤ D) (hle : D ≤ D') (hD'1 : D' < 1) :
    8 * D / (1 - D) ^ 2 ≤ 8 * D' / (1 - D') ^ 2 := by
  have hD1 : D < 1 := lt_of_le_of_lt hle hD'1
  have hp : (0 : ℝ) < (1 - D) ^ 2 := pow_pos (by linarith) 2
  have hp' : (0 : ℝ) < (1 - D') ^ 2 := pow_pos (by linarith) 2
  rw [div_le_div_iff₀ hp hp']
  have hnum : (8 : ℝ) * D ≤ 8 * D' := by linarith
  have hden : (1 - D') ^ 2 ≤ (1 - D) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hstep1 : 8 * D * (1 - D') ^ 2 ≤ 8 * D' * (1 - D') ^ 2 :=
    mul_le_mul_of_nonneg_right hnum (le_of_lt hp')
  have hstep2 : 8 * D' * (1 - D') ^ 2 ≤ 8 * D' * (1 - D) ^ 2 :=
    mul_le_mul_of_nonneg_left hden
      (mul_nonneg (by norm_num) (le_trans hD0 hle))
  linarith

/-- **`D`-monotonicity of the closed-form exponent `κ(D)`** (GJ §17.6.1, brick
F5b-1; TeX Lemma `lem:kappa-mono`).  On the KP window `0 ≤ D ≤ D' < 1` with
`8D'/(1-D')² < 1`, `κ(D) ≤ κ(D')`.  Both closed-form factors `(1-D)⁻¹` and
`((1 - 8D/(1-D)²)⁻¹)²` are nonnegative and increasing in `D`; window positivity
(`1-D > 0`, `1 - 8D/(1-D)² > 0`) is preserved throughout via `D ≤ D'`. -/
theorem fieldCEKappaOfActivity_mono {D D' : ℝ} (hD0 : 0 ≤ D) (hle : D ≤ D')
    (hD'1 : D' < 1) (hρ' : 8 * D' / (1 - D') ^ 2 < 1) :
    fieldCEKappaOfActivity D ≤ fieldCEKappaOfActivity D' := by
  have hD1 : D < 1 := lt_of_le_of_lt hle hD'1
  have h1D : (0 : ℝ) < 1 - D := by linarith
  have h1D' : (0 : ℝ) < 1 - D' := by linarith
  have hρle : 8 * D / (1 - D) ^ 2 ≤ 8 * D' / (1 - D') ^ 2 := rhoStar_mono hD0 hle hD'1
  have h1ρ' : (0 : ℝ) < 1 - 8 * D' / (1 - D') ^ 2 := by linarith
  have h1ρ : (0 : ℝ) < 1 - 8 * D / (1 - D) ^ 2 := by linarith
  unfold fieldCEKappaOfActivity
  have hf1 : 1 / (1 - D) ≤ 1 / (1 - D') := one_div_le_one_div_of_le h1D' (by linarith)
  have hinv : (1 - 8 * D / (1 - D) ^ 2)⁻¹ ≤ (1 - 8 * D' / (1 - D') ^ 2)⁻¹ :=
    inv_anti₀ h1ρ' (by linarith)
  have hinvsq : ((1 - 8 * D / (1 - D) ^ 2)⁻¹) ^ 2 ≤ ((1 - 8 * D' / (1 - D') ^ 2)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (inv_pos.mpr h1ρ)) hinv 2
  exact mul_le_mul hf1 hinvsq (sq_nonneg _) (le_of_lt (div_pos one_pos h1D'))

omit [DecidableEq ι] in
/-- **`D`-monotonicity crux for the KP exponent** (GJ §17.6.1, brick F5b-1; TeX
Lemma `lem:kappa-mono`).  If the pointwise activity `fieldCEActivity G a b` is at
most a larger, `b`-free activity `D*` lying in the KP window
(`D* < 1`, `8D*/(1-D*)² < 1`), then the pointwise local KP exponent is at most the
closed-form exponent at `D*`: `fieldCEKappaDelta G a b ≤ κ(D*)`.  This is the
mechanism by which the pointwise-`b` exponent is majorised by a single
ball-and-volume-uniform constant.  Proof: rewrite `fieldCEKappaDelta` as `κ` at
the pointwise activity (`fieldCEKappaDelta_eq_kappaOfActivity`) and apply
`fieldCEKappaOfActivity_mono`. -/
theorem fieldCEKappaDelta_le_of_activity_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    (a : ℝ) (b : ℂ) {Dstar : ℝ} (hle : fieldCEActivity G a b ≤ Dstar)
    (hDstar1 : Dstar < 1) (hρstar : 8 * Dstar / (1 - Dstar) ^ 2 < 1) :
    fieldCEKappaDelta G a b ≤ fieldCEKappaOfActivity Dstar := by
  rw [fieldCEKappaDelta_eq_kappaOfActivity]
  exact fieldCEKappaOfActivity_mono (fieldCEActivity_nonneg G a b) hle hDstar1 hρstar

/-- **Ball-&-volume-uniform complex field correlation bound** (GJ §17.6.1, brick
F5b-1, capstone; TeX §F5b-1 `prop:const-mono`).  On the F5-pre-2a field degree
window (target coupling `a ∈ Set.Ico 0 Awin`, field `b` in the `π/2`-ball
`Metric.ball 0 r` with a ball-uniform bound `Mrb`), and under the **strengthened
`Mstar`-window** (`Mstar = max 1 Mrb`) — the window hypotheses `hkpstar`,
`hρwinstar`, `hqstar` phrased at the ball-uniform envelope `Mstar` rather than the
pointwise `‖tanh b‖` — the complex field correlation obeys the `b`-independent
bound
\[
  \bigl\|\mathrm{fieldCorrelation}^{\mathbb C}\,G\,A\,a\,b\bigr\|
    \;\le\; \frac{M_\ast^{|A|}\,e^{\kappa(D_\ast)|A|}}
                 {1 - M_\ast^{2}\,e^{2\kappa(D_\ast)}\,|\tanh a|\,2^{|A|}\Delta^{2}},
\]
with `D* = Δ²·e·(Mstar²·|tanh a|)` and `κ(D*) = fieldCEKappaOfActivity D*`.  The
right-hand constant depends only on `(Δ, a, Mstar, |A|)`, neither on `b` (within
the ball) nor on the vertex count `|ι|` — exactly the ball-and-volume-uniform
`hbdd` datum required by the Montel/Vitali brick F6.  Proof: F5a-3
(`fieldCorrelationℂ_norm_le_uniform`) supplies the pointwise bound `A₀/(1-q)`
after downcasting the `Mstar`-window to the pointwise window (via
`fieldCEActivity_monotone_aux` and `rhoStar_mono`); then the `D`-monotonicity
crux `fieldCEKappaDelta_le_of_activity_le` gives `κ_Δ ≤ κ(D*)`, and
`prop:const-mono` (numerator increases, positive denominator decreases) closes
`A₀/(1-q) ≤ A₀*/(1-q*)`.  The `Mstar`-window is strictly stronger than the
pointwise F5a-3 window (it must hold at the ball/exhaustion extremum). -/
theorem fieldCorrelationℂ_norm_le_ball_uniform (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] [Nonempty ι] (A : Finset ι)
    {a Awin r Mrb ρ : ℝ} {b : ℂ}
    (ha : a ∈ Set.Ico 0 Awin) (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mrb)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mrb) (hbr : b ∈ Metric.ball 0 r)
    (hρ0 : 0 < ρ) (htanhA : Real.tanh Awin < ρ)
    (hkpstar : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ)) < 1)
    (hρwinstar : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ))) ^ 2 < 1)
    (hqstar : (max 1 Mrb) ^ 2 *
          Real.exp (2 * fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
          |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2) < 1) :
    ‖fieldCorrelationℂ G A a b‖
      ≤ (max 1 Mrb) ^ A.card *
            Real.exp (fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
              (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))) * (A.card : ℝ)) /
          (1 - (max 1 Mrb) ^ 2 *
            Real.exp (2 * fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
              (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
            |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2)) := by
  -- Pointwise/uniform field-magnitude comparison `M ≤ Mstar`.
  have hbnorm : ‖b‖ < r := mem_ball_zero_iff.mp hbr
  have htanhb_le : ‖Complex.tanh b‖ ≤ Mrb := hMr b (le_of_lt hbnorm)
  have hM_le : max 1 ‖Complex.tanh b‖ ≤ max 1 Mrb := max_le_max le_rfl htanhb_le
  have hM0 : (0 : ℝ) ≤ max 1 ‖Complex.tanh b‖ := le_trans zero_le_one (le_max_left _ _)
  have hMstar0 : (0 : ℝ) ≤ max 1 Mrb := le_trans zero_le_one (le_max_left _ _)
  have htanha_le : |Real.tanh a| ≤ ρ := by
    rw [abs_of_nonneg (real_tanh_nonneg ha.1)]
    exact le_of_lt (lt_of_le_of_lt (real_tanh_le_tanh (le_of_lt ha.2)) htanhA)
  -- The correlation activity `D*` and the degree-window activity comparisons.
  have hDstar_le_Dρstar :
      (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))
        ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htanha_le (sq_nonneg _)) (Real.exp_nonneg 1))
      (sq_nonneg _)
  have hDstar0 :
      (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)) := by
    positivity
  have hDstar1 :
      (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)) < 1 :=
    lt_of_le_of_lt hDstar_le_Dρstar hkpstar
  have hρstar :
      8 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))) ^ 2 < 1 :=
    lt_of_le_of_lt (rhoStar_mono hDstar0 hDstar_le_Dρstar hkpstar) hρwinstar
  -- `D`-monotonicity of the KP exponent: `κ_Δ(b) ≤ κ(D*)`.
  have hle : fieldCEActivity G a b
      ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)) := by
    unfold fieldCEActivity
    exact fieldCEActivity_monotone_aux hM_le hM0 (abs_nonneg _)
  have hκle : fieldCEKappaDelta G a b
      ≤ fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))) :=
    fieldCEKappaDelta_le_of_activity_le G a b hle hDstar1 hρstar
  -- Downcast the `Mstar`-window to the pointwise F5a-3 window at `b`.
  have hkp : (G.maxDegree : ℝ) ^ 2 *
      (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) < 1 :=
    lt_of_le_of_lt (fieldCEActivity_monotone_aux hM_le hM0 (le_of_lt hρ0)) hkpstar
  have hMρ0 : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 *
      (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) :=
    mul_nonneg (sq_nonneg _)
      (mul_nonneg (Real.exp_nonneg _) (mul_nonneg (sq_nonneg _) (le_of_lt hρ0)))
  have hρwin : 8 * ((G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)))
      / (1 - (G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ))) ^ 2 < 1 :=
    lt_of_le_of_lt
      (rhoStar_mono hMρ0 (fieldCEActivity_monotone_aux hM_le hM0 (le_of_lt hρ0)) hkpstar)
      hρwinstar
  -- Monotone comparison of the field-specific window scalar `q(b) ≤ q*`.
  have hMsq : (max 1 ‖Complex.tanh b‖) ^ 2 ≤ (max 1 Mrb) ^ 2 :=
    pow_le_pow_left₀ hM0 hM_le 2
  have hexp : Real.exp (2 * fieldCEKappaDelta G a b)
      ≤ Real.exp (2 * fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) :=
    Real.exp_le_exp.mpr (by linarith [hκle])
  have hqle : (max 1 ‖Complex.tanh b‖) ^ 2 * Real.exp (2 * fieldCEKappaDelta G a b) *
        |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2)
      ≤ (max 1 Mrb) ^ 2 *
          Real.exp (2 * fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
          |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact mul_le_mul hMsq hexp (Real.exp_nonneg _) (pow_nonneg hMstar0 2)
  have hq : (max 1 ‖Complex.tanh b‖) ^ 2 * Real.exp (2 * fieldCEKappaDelta G a b) *
        |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2) < 1 :=
    lt_of_le_of_lt hqle hqstar
  -- F5a-3 pointwise capstone.
  have hcap := fieldCorrelationℂ_norm_le_uniform G A ha hr0 hrpi hMr1 hMr hbr hρ0 htanhA
    hkp hρwin hq
  refine hcap.trans ?_
  -- Constant monotonicity (`prop:const-mono`): `A₀(b)/(1-q(b)) ≤ A₀*/(1-q*)`.
  have hA0 : (max 1 ‖Complex.tanh b‖) ^ A.card *
        Real.exp (fieldCEKappaDelta G a b * (A.card : ℝ))
      ≤ (max 1 Mrb) ^ A.card *
          Real.exp (fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))) * (A.card : ℝ)) :=
    mul_le_mul (pow_le_pow_left₀ hM0 hM_le _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hκle (Nat.cast_nonneg _)))
      (Real.exp_nonneg _) (pow_nonneg hMstar0 _)
  have hA0star0 : (0 : ℝ) ≤ (max 1 Mrb) ^ A.card *
      Real.exp (fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))) * (A.card : ℝ)) :=
    mul_nonneg (pow_nonneg hMstar0 _) (Real.exp_nonneg _)
  have hden_b : (0 : ℝ) < 1 - (max 1 ‖Complex.tanh b‖) ^ 2 *
      Real.exp (2 * fieldCEKappaDelta G a b) *
      |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2) := by linarith [hq]
  have hden_star : (0 : ℝ) < 1 - (max 1 Mrb) ^ 2 *
      Real.exp (2 * fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
      |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2) := by linarith [hqstar]
  rw [div_le_div_iff₀ hden_b hden_star]
  have hstep1 := mul_le_mul_of_nonneg_right hA0 (le_of_lt hden_star)
  have hstep2 := mul_le_mul_of_nonneg_left (by linarith [hqle] :
      (1 : ℝ) - (max 1 Mrb) ^ 2 *
          Real.exp (2 * fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
          |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2)
        ≤ 1 - (max 1 ‖Complex.tanh b‖) ^ 2 * Real.exp (2 * fieldCEKappaDelta G a b) *
            |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2)) hA0star0
  linarith [hstep1, hstep2]

/-- **Degree-bound ball-&-volume-uniform complex field correlation bound**
(GJ §17.6.1, brick F5b-2; TeX §F5b-2 `prop:f5b2`).  A degree-uniform generalization
of `fieldCorrelationℂ_norm_le_ball_uniform` (F5b-1): both the window hypotheses and
the closed constant are phrased with an **external** degree bound `Δ` and a
hypothesis `hΔ : G.maxDegree ≤ Δ`, rather than the concrete `G.maxDegree`.  This is
essential for the exhaustion wrap, where each induced stage satisfies only
`maxDegree ≤ 2d` (not equality); phrasing the constant with `Δ = 2d` makes the bound
independent of the exhaustion stage `n`.

No new analytic content beyond F5b-1: the whole proof is the two monotonicities of
F5b-1 (`fieldCEKappaOfActivity_mono`, `rhoStar_mono`, and the `prop:const-mono`
`div_le_div_iff₀` crux) applied **in the degree variable** `(Δ:ℝ)²` instead of the
field variable.  The sole new numeric input is `(∗)`:
`(G.maxDegree:ℝ)² ≤ (Δ:ℝ)²` (from `hΔ`, via `Nat.cast_le` and `pow_le_pow_left₀`),
read in **two opposite senses**:
* **window downcast** (`Δ → G.maxDegree`): the `Δ`-window hypotheses `hkpstar`,
  `hρwinstar`, `hqstar` (the larger arguments, all `< 1`) are downcast to the
  smaller `G.maxDegree`-arguments that F5b-1 literally consumes;
* **RHS upcast** (`G.maxDegree → Δ`): the F5b-1 output constant at `G.maxDegree`
  (smaller) is upcast to the `Δ`-constant (larger, since the constant increases in
  the degree).

Substituting `Δ = G.maxDegree` (with `hΔ = le_rfl`) makes `(∗)` an equality and
collapses this back to F5b-1 verbatim, so F5b-2 **contains** F5b-1 as a special
case.  The ball envelope `Mstar = max 1 Mrb` is identical on both sides (only the
degree varies), so the two-`Mr` duality of F5b-1 is untouched. -/
theorem fieldCorrelationℂ_norm_le_ball_uniform_of_degree_le (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] [Nonempty ι] (A : Finset ι)
    (Δ : ℕ) (hΔ : G.maxDegree ≤ Δ)
    {a Awin r Mrb ρ : ℝ} {b : ℂ}
    (ha : a ∈ Set.Ico 0 Awin) (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mrb)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mrb) (hbr : b ∈ Metric.ball 0 r)
    (hρ0 : 0 < ρ) (htanhA : Real.tanh Awin < ρ)
    (hkpstar : (Δ : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ)) < 1)
    (hρwinstar : 8 * ((Δ : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ)))
        / (1 - (Δ : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ))) ^ 2 < 1)
    (hqstar : (max 1 Mrb) ^ 2 *
          Real.exp (2 * fieldCEKappaOfActivity ((Δ : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
          |Real.tanh a| * (2 ^ A.card * (Δ : ℝ) ^ 2) < 1) :
    ‖fieldCorrelationℂ G A a b‖
      ≤ (max 1 Mrb) ^ A.card *
            Real.exp (fieldCEKappaOfActivity ((Δ : ℝ) ^ 2 *
              (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))) * (A.card : ℝ)) /
          (1 - (max 1 Mrb) ^ 2 *
            Real.exp (2 * fieldCEKappaOfActivity ((Δ : ℝ) ^ 2 *
              (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
            |Real.tanh a| * (2 ^ A.card * (Δ : ℝ) ^ 2)) := by
  have hMstar0 : (0 : ℝ) ≤ max 1 Mrb := le_trans zero_le_one (le_max_left _ _)
  -- (∗): the degree² comparison, read in both senses below.
  have hDeg2 : (G.maxDegree : ℝ) ^ 2 ≤ (Δ : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hΔ) 2
  -- The two activities at each degree; both nonnegative, both monotone via (∗).
  have hX0 : (0 : ℝ) ≤ Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ) := by positivity
  have hY0 : (0 : ℝ) ≤ Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|) := by positivity
  have hDρ_G_le : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ))
      ≤ (Δ : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ)) :=
    mul_le_mul_of_nonneg_right hDeg2 hX0
  have hD_G_le : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))
      ≤ (Δ : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)) :=
    mul_le_mul_of_nonneg_right hDeg2 hY0
  have hDρ_G0 : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ)) := by
    positivity
  have hD_G0 : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 *
      (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)) := by positivity
  have hD_Δ0 : (0 : ℝ) ≤ (Δ : ℝ) ^ 2 *
      (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)) := by positivity
  -- `|tanh a| ≤ ρ`, hence the `|tanh a|`-activity is below the `ρ`-window activity.
  have htanha_le : |Real.tanh a| ≤ ρ := by
    rw [abs_of_nonneg (real_tanh_nonneg ha.1)]
    exact le_of_lt (lt_of_le_of_lt (real_tanh_le_tanh (le_of_lt ha.2)) htanhA)
  have hD_Δ_le_Dρ_Δ :
      (Δ : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))
        ≤ (Δ : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htanha_le (sq_nonneg _)) (Real.exp_nonneg 1))
      (sq_nonneg _)
  have hD_Δ1 : (Δ : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)) < 1 :=
    lt_of_le_of_lt hD_Δ_le_Dρ_Δ hkpstar
  have hρ_Δ : 8 * ((Δ : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))
        / (1 - (Δ : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))) ^ 2 < 1 :=
    lt_of_le_of_lt (rhoStar_mono hD_Δ0 hD_Δ_le_Dρ_Δ hkpstar) hρwinstar
  -- Degree-monotonicity of the KP exponent: `κ(D_G) ≤ κ(D_Δ)`.
  have hκ_GΔ :
      fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))
        ≤ fieldCEKappaOfActivity ((Δ : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))) :=
    fieldCEKappaOfActivity_mono hD_G0 hD_G_le hD_Δ1 hρ_Δ
  -- **Window downcast** (`Δ → G.maxDegree`): produce the F5b-1 hypotheses.
  have hkp_G : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ)) < 1 :=
    lt_of_le_of_lt hDρ_G_le hkpstar
  have hρwin_G : 8 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ)))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mrb) ^ 2 * ρ))) ^ 2 < 1 :=
    lt_of_le_of_lt (rhoStar_mono hDρ_G0 hDρ_G_le hkpstar) hρwinstar
  have hexp : Real.exp (2 * fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))))
      ≤ Real.exp (2 * fieldCEKappaOfActivity ((Δ : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) :=
    Real.exp_le_exp.mpr (by linarith [hκ_GΔ])
  have hq_G_le : (max 1 Mrb) ^ 2 *
        Real.exp (2 * fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
        |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2)
      ≤ (max 1 Mrb) ^ 2 *
          Real.exp (2 * fieldCEKappaOfActivity ((Δ : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
          |Real.tanh a| * (2 ^ A.card * (Δ : ℝ) ^ 2) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (pow_nonneg hMstar0 2)) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left hDeg2 (by positivity)
    · positivity
    · positivity
  have hq_G : (max 1 Mrb) ^ 2 *
        Real.exp (2 * fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
        |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2) < 1 :=
    lt_of_le_of_lt hq_G_le hqstar
  -- Feed F5b-1 at the actual `G.maxDegree`.
  have hcap := fieldCorrelationℂ_norm_le_ball_uniform G A ha hr0 hrpi hMr1 hMr hbr hρ0
    htanhA hkp_G hρwin_G hq_G
  refine hcap.trans ?_
  -- **RHS upcast** (`G.maxDegree → Δ`): the F5b-1 constant increases in the degree.
  have hA0 : (max 1 Mrb) ^ A.card *
        Real.exp (fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))) * (A.card : ℝ))
      ≤ (max 1 Mrb) ^ A.card *
          Real.exp (fieldCEKappaOfActivity ((Δ : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))) * (A.card : ℝ)) :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hκ_GΔ (Nat.cast_nonneg _)))
      (pow_nonneg hMstar0 _)
  have hA0star0 : (0 : ℝ) ≤ (max 1 Mrb) ^ A.card *
      Real.exp (fieldCEKappaOfActivity ((Δ : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|))) * (A.card : ℝ)) :=
    mul_nonneg (pow_nonneg hMstar0 _) (Real.exp_nonneg _)
  have hden_G : (0 : ℝ) < 1 - (max 1 Mrb) ^ 2 *
      Real.exp (2 * fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
      |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2) := by linarith [hq_G]
  have hden_Δ : (0 : ℝ) < 1 - (max 1 Mrb) ^ 2 *
      Real.exp (2 * fieldCEKappaOfActivity ((Δ : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
      |Real.tanh a| * (2 ^ A.card * (Δ : ℝ) ^ 2) := by linarith [hqstar]
  rw [div_le_div_iff₀ hden_G hden_Δ]
  have hstep1 := mul_le_mul_of_nonneg_right hA0 (le_of_lt hden_Δ)
  have hstep2 := mul_le_mul_of_nonneg_left (by linarith [hq_G_le] :
      (1 : ℝ) - (max 1 Mrb) ^ 2 *
          Real.exp (2 * fieldCEKappaOfActivity ((Δ : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
          |Real.tanh a| * (2 ^ A.card * (Δ : ℝ) ^ 2)
        ≤ 1 - (max 1 Mrb) ^ 2 *
            Real.exp (2 * fieldCEKappaOfActivity ((G.maxDegree : ℝ) ^ 2 *
              (Real.exp 1 * ((max 1 Mrb) ^ 2 * |Real.tanh a|)))) *
            |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2)) hA0star0
  linarith [hstep1, hstep2]

end IsingModel
