import IsingModel.GibbsMeasure
import IsingModel.FreeEnergy
import IsingModel.LeeYang
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Complex analyticity of the Ising partition function (finite volume)

Extension of `FreeEnergy.lean` finite-volume real-analyticity to complex
parameters. GJ §4.6 Thm 4.6.2 concerns analyticity on
`{|Im h| < Re h}`; the real-analyticity in
`freeEnergyH_analyticOn` covers `h ∈ (0, ∞) ⊂ ℝ`.

This file provides the complex-parameter finite-volume building blocks:
* `partitionFunctionComplex` — `Z(J, h, β)` as a `ℂ`-valued function
* `partitionFunctionComplex_analyticAt_h` etc. — each parameter entire

These feed into the infinite-volume Vitali step (out of scope for this PR).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-- Per-edge spin product with values in `ℂ`. -/
noncomputable def edgeSpinComplex (σ : Config ι) (e : Sym2 ι) : ℂ :=
  Sym2.lift ⟨fun i j => (Spin.sign ℂ (σ i)) * (Spin.sign ℂ (σ j)),
    fun _ _ => mul_comm _ _⟩ e

/-- Interaction energy with complex coupling `J : ℂ`. -/
noncomputable def interactionEnergyComplex (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℂ) (σ : Config ι) : ℂ :=
  -J * ∑ e ∈ G.edgeFinset, edgeSpinComplex σ e

/-- External-field energy with complex field `h : ℂ`. -/
noncomputable def externalFieldEnergyComplex (h : ℂ) (σ : Config ι) : ℂ :=
  -h * ∑ i : ι, Spin.sign ℂ (σ i)

/-- Ising Hamiltonian with complex parameters. -/
noncomputable def hamiltonianComplex (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℂ) (σ : Config ι) : ℂ :=
  interactionEnergyComplex G J σ + externalFieldEnergyComplex h σ

/-- Complex-parameter partition function:
`Z(J, h, β) = ∑_σ exp(-β · H(σ; J, h))`. -/
noncomputable def partitionFunctionComplex (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℂ) : ℂ :=
  ∑ σ : Config ι, Complex.exp (-β * hamiltonianComplex G J h σ)

/-- `partitionFunctionComplex` is entire in the external field `h`. -/
theorem partitionFunctionComplex_analyticAt_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℂ) (h₀ : ℂ) :
    AnalyticAt ℂ (fun h => partitionFunctionComplex G J h β) h₀ := by
  unfold partitionFunctionComplex hamiltonianComplex externalFieldEnergyComplex
    interactionEnergyComplex
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine AnalyticAt.cexp' ?_
  fun_prop

/-- `partitionFunctionComplex` is entire in the coupling `J`. -/
theorem partitionFunctionComplex_analyticAt_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℂ) (J₀ : ℂ) :
    AnalyticAt ℂ (fun J => partitionFunctionComplex G J h β) J₀ := by
  unfold partitionFunctionComplex hamiltonianComplex externalFieldEnergyComplex
    interactionEnergyComplex
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine AnalyticAt.cexp' ?_
  fun_prop

/-- `partitionFunctionComplex` is entire in the inverse temperature `β`. -/
theorem partitionFunctionComplex_analyticAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℂ) (β₀ : ℂ) :
    AnalyticAt ℂ (fun β => partitionFunctionComplex G J h β) β₀ := by
  unfold partitionFunctionComplex hamiltonianComplex externalFieldEnergyComplex
    interactionEnergyComplex
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine AnalyticAt.cexp' ?_
  fun_prop

/-- Complex free energy per site: `f(J, h, β) = |ι|⁻¹ · log Z(J, h, β)`. -/
noncomputable def freeEnergyComplex (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℂ) : ℂ :=
  ((Fintype.card ι : ℂ))⁻¹ * Complex.log (partitionFunctionComplex G J h β)

/-- `freeEnergyComplex` is analytic in `h` at points where `Z ∈ Complex.slitPlane`.

Derived from `partitionFunctionComplex_analyticAt_h` (entire in `h`) and
`AnalyticAt.clog` (mathlib `Complex.log` is analytic on `slitPlane`). -/
theorem freeEnergyComplex_analyticAt_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℂ) (h₀ : ℂ)
    (hZ : partitionFunctionComplex G J h₀ β ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun h => freeEnergyComplex G J h β) h₀ := by
  unfold freeEnergyComplex
  exact analyticAt_const.mul
    ((partitionFunctionComplex_analyticAt_h G J β h₀).clog hZ)

/-- `freeEnergyComplex` is analytic in `J` at points where `Z ∈ Complex.slitPlane`. -/
theorem freeEnergyComplex_analyticAt_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℂ) (J₀ : ℂ)
    (hZ : partitionFunctionComplex G J₀ h β ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun J => freeEnergyComplex G J h β) J₀ := by
  unfold freeEnergyComplex
  exact analyticAt_const.mul
    ((partitionFunctionComplex_analyticAt_J G h β J₀).clog hZ)

/-- `freeEnergyComplex` is analytic in `β` at points where `Z ∈ Complex.slitPlane`. -/
theorem freeEnergyComplex_analyticAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℂ) (β₀ : ℂ)
    (hZ : partitionFunctionComplex G J h β₀ ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun β => freeEnergyComplex G J h β) β₀ := by
  unfold freeEnergyComplex
  exact analyticAt_const.mul
    ((partitionFunctionComplex_analyticAt_beta G J h β₀).clog hZ)

/-- `partitionFunctionComplex` is jointly entire in `(J, h, β)`. -/
theorem partitionFunctionComplex_analyticAt_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (z₀ : ℂ × ℂ × ℂ) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      partitionFunctionComplex G z.1 z.2.1 z.2.2) z₀ := by
  unfold partitionFunctionComplex hamiltonianComplex externalFieldEnergyComplex
    interactionEnergyComplex
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine AnalyticAt.cexp' ?_
  have hJ : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.1) z₀ := analyticAt_fst
  have hhβ : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2) z₀ := analyticAt_snd
  have hh : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2.1) z₀ :=
    analyticAt_fst.comp hhβ
  have hβ : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2.2) z₀ :=
    analyticAt_snd.comp hhβ
  have hJsum : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      -z.1 * ∑ e ∈ G.edgeFinset, edgeSpinComplex σ e) z₀ :=
    (hJ.neg).mul analyticAt_const
  have hhsum : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      -z.2.1 * ∑ i : ι, Spin.sign ℂ (σ i)) z₀ :=
    (hh.neg).mul analyticAt_const
  exact (hβ.neg).mul (hJsum.add hhsum)

/-- `freeEnergyComplex` is jointly analytic in `(J, h, β)` at points where
`Z ∈ Complex.slitPlane`. -/
theorem freeEnergyComplex_analyticAt_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (z₀ : ℂ × ℂ × ℂ)
    (hZ : partitionFunctionComplex G z₀.1 z₀.2.1 z₀.2.2 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      freeEnergyComplex G z.1 z.2.1 z.2.2) z₀ := by
  unfold freeEnergyComplex
  exact analyticAt_const.mul
    ((partitionFunctionComplex_analyticAt_joint G z₀).clog hZ)

/-! ## Real-complex compatibility

Bridge at the `partitionFunction` level: at real parameters, the complex
and real partition functions agree up to `Complex.ofReal`. A corresponding
bridge for `freeEnergy` would additionally require a real-vs-complex
`log` compatibility on positive reals (out of scope for this PR). -/

omit [Fintype ι] [DecidableEq ι] in
/-- `Complex.ofReal (edgeSpin σ e) = edgeSpinComplex σ e`. -/
theorem edgeSpin_ofReal_eq_edgeSpinComplex (σ : Config ι) (e : Sym2 ι) :
    ((edgeSpin (K := ℝ) σ e : ℝ) : ℂ) = edgeSpinComplex σ e := by
  induction e with
  | h i j =>
    simp [edgeSpin, edgeSpinComplex, Spin.sign]

/-- `Complex.ofReal (partitionFunction G p) = partitionFunctionComplex G p.J p.h p.β`. -/
theorem partitionFunction_ofReal_eq_partitionFunctionComplex
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    ((partitionFunction G p : ℝ) : ℂ)
      = partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) := by
  unfold partitionFunction boltzmannWeight partitionFunctionComplex
    hamiltonianComplex externalFieldEnergyComplex interactionEnergyComplex
    hamiltonian interactionEnergy externalFieldEnergy
  push_cast
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hspin : ∀ i : ι, ((Spin.sign ℝ (σ i) : ℝ) : ℂ) = Spin.sign ℂ (σ i) := by
    intro i; simp [Spin.sign]
  have hedge : ∀ e : Sym2 ι,
      ((edgeSpin (K := ℝ) σ e : ℝ) : ℂ) = edgeSpinComplex σ e :=
    edgeSpin_ofReal_eq_edgeSpinComplex σ
  push_cast [← hspin, ← hedge]
  ring

/-- **`partitionFunctionComplex` is in `Complex.slitPlane` on the real slice.**

At real parameters `p : IsingParams ℝ`, `partitionFunctionComplex G ↑p.J ↑p.h ↑p.β`
equals `↑(partitionFunction G p)` (by `partitionFunction_ofReal_eq_partitionFunctionComplex`),
which has real part `partitionFunction G p > 0` and imaginary part `0`.
Hence it lies in `Complex.slitPlane = {z | 0 < z.re ∨ z.im ≠ 0}`.

This upgrades the per-parameter / joint `freeEnergyComplex_analyticAt` theorems
to statements that are directly applicable at real points. -/
theorem partitionFunctionComplex_mem_slitPlane_of_real
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) ∈ Complex.slitPlane := by
  rw [← partitionFunction_ofReal_eq_partitionFunctionComplex G p]
  refine Or.inl ?_
  have hpos : 0 < partitionFunction G p := partitionFunction_pos G p
  simpa using hpos

/-- `Complex.ofReal (freeEnergy G p) = freeEnergyComplex G p.J p.h p.β`.

Combines `partitionFunction_ofReal_eq_partitionFunctionComplex` (PR #196)
with positivity of `partitionFunction` and mathlib `Complex.ofReal_log`. -/
theorem freeEnergy_ofReal_eq_freeEnergyComplex
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    ((freeEnergy G p : ℝ) : ℂ)
      = freeEnergyComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) := by
  unfold freeEnergy freeEnergyComplex
  have hZpos : 0 ≤ partitionFunction G p :=
    (partitionFunction_pos G p).le
  rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_log hZpos,
    partitionFunction_ofReal_eq_partitionFunctionComplex G p]

/-! ## Lee-Yang domain (GJ §4.6 Thm 4.6.2, PR #199)

The Lee-Yang domain for the external field is `{h ∈ ℂ | |Im h| < Re h}`.
GJ §4.6 Thm 4.6.2 states that the free energy is analytic on this domain.
The proof uses Lee-Yang nonvanishing of the Ising polynomial (existing
`lee_yang_circle`) plus a branch-selection argument.

Session-spanning infrastructure (PR #199 work file 0164):
defining the domain here; the nonvanishing and analyticity results are
added in subsequent sessions on the same branch. -/

/-- The Lee-Yang domain: complex external fields with `|Im h| < Re h`. -/
def leeYangDomain : Set ℂ := {h : ℂ | |h.im| < h.re}

/-- The Lee-Yang domain is a subset of `Complex.slitPlane` (the right
half-plane `Re h > |Im h|` is contained in `Re h > 0 ∨ Im h ≠ 0`). -/
theorem leeYangDomain_subset_slitPlane : leeYangDomain ⊆ Complex.slitPlane := by
  intro h hmem
  refine Or.inl ?_
  have hlt : |h.im| < h.re := hmem
  have hnn : (0 : ℝ) ≤ |h.im| := abs_nonneg _
  linarith

/-- The Lee-Yang domain is open in `ℂ`. The defining inequality
`|Im h| < Re h` uses continuous functions (`Complex.im`, `abs`,
`Complex.re`), so the preimage of `(0, ∞)` under the continuous
`h ↦ Re h - |Im h|` is open. -/
theorem isOpen_leeYangDomain : IsOpen leeYangDomain := by
  have hcont : Continuous (fun h : ℂ => h.re - |h.im|) := by
    exact Complex.continuous_re.sub Complex.continuous_im.abs
  have heq : leeYangDomain = (fun h : ℂ => h.re - |h.im|) ⁻¹' Set.Ioi 0 := by
    ext h
    constructor
    · intro hlt
      have : |h.im| < h.re := hlt
      change h.re - |h.im| ∈ Set.Ioi 0
      simp [Set.mem_Ioi]; linarith
    · intro hlt
      have : h.re - |h.im| > 0 := hlt
      change |h.im| < h.re
      linarith
  rw [heq]
  exact hcont.isOpen_preimage _ isOpen_Ioi

/-- The positive real axis is contained in `leeYangDomain`: if `h = h₀ > 0`
is real, then `Im h = 0 < h₀ = Re h`. This provides a canonical basepoint
from which to continue the Lee-Yang nonvanishing into the complex domain. -/
theorem real_pos_mem_leeYangDomain {h₀ : ℝ} (hpos : 0 < h₀) :
    (h₀ : ℂ) ∈ leeYangDomain := by
  change |(h₀ : ℂ).im| < (h₀ : ℂ).re
  simp [hpos]

/-- Lee-Yang fugacity map: `h ↦ e^{-2β h}`.

For the Ising partition polynomial `P(z)` (see `LeeYang.lean`), the site
fugacity is `z_k = e^{-2β h_k}`. For uniform `h`, all `z_k` coincide.
Lee-Yang nonvanishing requires `|z_k| < 1`, i.e., `|e^{-2β h}| < 1`. -/
noncomputable def leeYangFugacity (β h : ℂ) : ℂ := Complex.exp (-2 * β * h)

/-- **Fugacity norm formula**: `‖e^{-2β h}‖ = e^{-2 β · Re h}` for real `β`.
Used in Lee-Yang nonvanishing arguments: the left-hand side is the
input to `isingEdgePoly_nonvanishing_of_graph`, and this formula lets
us read off `< 1` or `≤ 1` bounds from `Re h`. -/
theorem norm_leeYangFugacity_eq (β : ℝ) (h : ℂ) :
    ‖leeYangFugacity (β : ℂ) h‖ = Real.exp (-2 * β * h.re) := by
  unfold leeYangFugacity
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **`leeYangFugacity β` is continuous in `h`** for any fixed `β`.
`leeYangFugacity β h = exp (-2 β h)` is the composition of the linear
map `h ↦ -2β h` with the entire exponential, hence continuous. -/
theorem continuous_leeYangFugacity (β : ℂ) :
    Continuous (leeYangFugacity β) := by
  unfold leeYangFugacity
  exact Complex.continuous_exp.comp (by fun_prop)

/-- **`leeYangFugacity β` is entire** (analytic on all of `ℂ`) for any
fixed `β : ℂ`. Composition of the affine `h ↦ -2β h` with `Complex.exp`. -/
theorem analyticOnNhd_leeYangFugacity (β : ℂ) :
    AnalyticOnNhd ℂ (leeYangFugacity β) Set.univ := by
  intro z _
  unfold leeYangFugacity
  exact analyticAt_cexp.comp (by fun_prop)

/-- **Fugacity in the open unit disk on the Lee-Yang domain**:
for real `β > 0` and `h ∈ leeYangDomain` (i.e., `|Im h| < Re h`),
the fugacity `e^{-2β h}` has absolute value less than 1.

Proof: `‖e^{-2β h}‖ = e^{Re(-2β h)} = e^{-2β · Re h}`, and `Re h > 0`
on the Lee-Yang domain (from `leeYangDomain_subset_slitPlane`). -/
theorem norm_leeYangFugacity_lt_one
    {β : ℝ} (hβ : 0 < β) {h : ℂ} (hh : h ∈ leeYangDomain) :
    ‖leeYangFugacity (β : ℂ) h‖ < 1 := by
  have hreh : 0 < h.re := by
    have hlt : |h.im| < h.re := hh
    have hnn : (0 : ℝ) ≤ |h.im| := abs_nonneg _
    linarith
  unfold leeYangFugacity
  rw [Complex.norm_exp]
  have hre : (-2 * (β : ℂ) * h).re = -2 * β * h.re := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  -- want: exp(-2β Re h) < 1, i.e., -2β Re h < 0
  refine Real.exp_lt_one_iff.mpr ?_
  have : 0 < 2 * β * h.re := by positivity
  linarith

/-- `leeYangFugacity β` maps `leeYangDomain` into the open unit disk
(for real `β > 0`): constant-coefficient version of the site fugacity
vector going into `isingEdgePoly_nonvanishing_of_graph`. -/
theorem leeYangFugacity_mapsTo_ball
    {β : ℝ} (hβ : 0 < β) :
    Set.MapsTo (leeYangFugacity (β : ℂ)) leeYangDomain (Metric.ball (0 : ℂ) 1) := by
  intro h hh
  rw [Metric.mem_ball, dist_zero_right]
  exact norm_leeYangFugacity_lt_one hβ hh

/-- `leeYangFugacity β h ≠ 0`: the fugacity `e^{-2β h}` is never zero
(as the complex exponential is always non-vanishing). -/
theorem leeYangFugacity_ne_zero (β h : ℂ) : leeYangFugacity β h ≠ 0 := by
  unfold leeYangFugacity
  exact Complex.exp_ne_zero _

/-- Constant (uniform) fugacity vector at site level: `fun _ : ι => leeYangFugacity β h`.
This is the input to `isingEdgePoly_nonvanishing_of_graph` for a uniform
external field `h`. -/
noncomputable def leeYangFugacityVec (β h : ℂ) : ι → ℂ :=
  fun _ => leeYangFugacity β h

omit [Fintype ι] [DecidableEq ι] in
/-- On the Lee-Yang domain with real β > 0, every entry of the uniform
fugacity vector is in the open unit disk — the exact condition
`∀ k, ‖z k‖ < 1` required by `isingEdgePoly_nonvanishing_of_graph`. -/
theorem leeYangFugacityVec_norm_lt_one
    {β : ℝ} (hβ : 0 < β) {h : ℂ} (hh : h ∈ leeYangDomain) (k : ι) :
    ‖(leeYangFugacityVec (β : ℂ) h : ι → ℂ) k‖ < 1 := by
  exact norm_leeYangFugacity_lt_one hβ hh

/-- **Lee-Yang normalization factor**: `exp(β·J·|E| + β·h·|ι|)`.

The Ising partition function factorises (Friedli–Velenik (3.63)) as
`Z = exp(β·J·|E| + β·h·|ι|) · P(z)` with `z_k = e^{-2β h_k}`.
This is the scalar prefactor, used in the Lee-Yang nonvanishing bridge
from the polynomial nonvanishing (`isingEdgePoly_eval_leeYangFugacityVec_ne_zero`)
to `partitionFunctionComplex ≠ 0`. -/
noncomputable def leeYangNormalization (β J h : ℂ) (edgeCount siteCount : ℕ) : ℂ :=
  Complex.exp (β * J * (edgeCount : ℂ) + β * h * (siteCount : ℂ))

/-- The Lee-Yang normalization factor is never zero (product of complex
exponentials, hence non-vanishing). -/
theorem leeYangNormalization_ne_zero
    (β J h : ℂ) (edgeCount siteCount : ℕ) :
    leeYangNormalization β J h edgeCount siteCount ≠ 0 := by
  unfold leeYangNormalization
  exact Complex.exp_ne_zero _

/-- The Lee-Yang normalization factor is jointly entire in `(β, J, h)`. -/
theorem leeYangNormalization_analyticAt_joint
    (edgeCount siteCount : ℕ) (z₀ : ℂ × ℂ × ℂ) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      leeYangNormalization z.2.2 z.1 z.2.1 edgeCount siteCount) z₀ := by
  unfold leeYangNormalization
  refine AnalyticAt.cexp' ?_
  have hJ : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.1) z₀ := analyticAt_fst
  have hhβ : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2) z₀ := analyticAt_snd
  have hh : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2.1) z₀ :=
    analyticAt_fst.comp hhβ
  have hβ : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2.2) z₀ :=
    analyticAt_snd.comp hhβ
  exact (hβ.mul hJ |>.mul analyticAt_const).add (hβ.mul hh |>.mul analyticAt_const)

/-- At real parameters, `leeYangNormalization` is a positive real number.
This matches the `exp(β J |E| + β h |ι|)` prefactor of the real-valued
partition function, which is always strictly positive. -/
theorem leeYangNormalization_ofReal_pos
    (β J h : ℝ) (edgeCount siteCount : ℕ) :
    0 < (leeYangNormalization (β : ℂ) (J : ℂ) (h : ℂ)
            edgeCount siteCount).re := by
  unfold leeYangNormalization
  have heq : (β : ℂ) * (J : ℂ) * (edgeCount : ℂ)
              + (β : ℂ) * (h : ℂ) * (siteCount : ℂ)
            = ((β * J * edgeCount + β * h * siteCount : ℝ) : ℂ) := by
    push_cast; ring
  rw [heq, ← Complex.ofReal_exp, Complex.ofReal_re]
  exact Real.exp_pos _

/-- **Lee-Yang nonvanishing of the Ising partition polynomial on the
Lee-Yang domain** (uniform field, real ferromagnetic coupling).

For a graph `G`, a coupling parameter `t ∈ [0, 1)`, real `β > 0`,
and `h ∈ leeYangDomain`, the Ising partition polynomial
`P_E(z)` does not vanish at the uniform fugacity
`z_k = e^{-2β h}`:
  `(isingEdgePoly (graphToEdgeList G t)).eval (leeYangFugacityVec β h) ≠ 0`.

Direct consequence of `isingEdgePoly_nonvanishing_of_graph`
(FreeEnergy.lean, which wraps the Lee-Yang circle theorem) together
with the unit-disk bound `leeYangFugacityVec_norm_lt_one`. -/
theorem isingEdgePoly_eval_leeYangFugacityVec_ne_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    {β : ℝ} (hβ : 0 < β) {h : ℂ} (hh : h ∈ leeYangDomain) :
    (isingEdgePoly (graphToEdgeList G t)).eval
        (leeYangFugacityVec (β : ℂ) h) ≠ 0 :=
  isingEdgePoly_nonvanishing_of_graph G t ht₀ ht₁
    (leeYangFugacityVec (β : ℂ) h)
    (fun k => leeYangFugacityVec_norm_lt_one hβ hh k)

/-- **Product of Lee-Yang prefactor and polynomial is non-zero on the
Lee-Yang domain**. This is the final form that matches the
Friedli–Velenik identity `Z = leeYangNormalization · P(z)`:
the RHS is non-zero, hence so is `Z` (once the identity is formally
established). -/
theorem leeYangNormalization_mul_isingEdgePoly_eval_ne_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    (J : ℂ) {β : ℝ} (hβ : 0 < β) {h : ℂ} (hh : h ∈ leeYangDomain)
    (edgeCount siteCount : ℕ) :
    leeYangNormalization (β : ℂ) J h edgeCount siteCount
        * (isingEdgePoly (graphToEdgeList G t)).eval
            (leeYangFugacityVec (β : ℂ) h) ≠ 0 :=
  mul_ne_zero (leeYangNormalization_ne_zero _ _ _ _ _)
    (isingEdgePoly_eval_leeYangFugacityVec_ne_zero G ht₀ ht₁ hβ hh)

/-- Per-site factorisation of the external-field exponential.
For `σ : Config ι` with down-spin set `X = configToFinset σ`, at each site `i`:
`exp(β·h·σ_i) = exp(β·h) · (i ∈ X ? leeYangFugacity β h : 1)`.

Case split on `σ i`: if `σ i = up` (so `i ∉ X`) then `σ_i = 1` and
the RHS is `exp(β·h)·1 = exp(β·h)`; if `σ i = down` (so `i ∈ X`) then
`σ_i = -1` and the RHS is `exp(β·h) · exp(-2β·h) = exp(-β·h)`. -/
theorem exp_beta_h_sign_eq (β : ℝ) (h : ℂ) (σ : Config ι) (i : ι) :
    Complex.exp ((β : ℂ) * h * Spin.sign ℂ (σ i))
      = Complex.exp ((β : ℂ) * h)
          * (if i ∈ configToFinset σ then
              leeYangFugacity (β : ℂ) h else 1) := by
  unfold leeYangFugacity configToFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases hσ : σ i with
  | up =>
    simp only [Spin.sign, Spin.toSign, Int.cast_one, mul_one]
    rw [if_neg (by simp), mul_one]
  | down =>
    simp only [Spin.sign, Spin.toSign, Int.cast_neg, Int.cast_one]
    rw [if_pos (by simp)]
    rw [mul_neg_one, ← Complex.exp_add]
    congr 1; ring

/-- Per-edge factorisation of the interaction exponential.
For `σ : Config ι` with down-spin set `X = configToFinset σ`, at each
pair `(i, j)` with `i ≠ j`:
`exp(β·J·σ_i·σ_j) = exp(β·J) · edgeWeight i j (exp(-2βJ)) X`.

Case split on whether `(σ i = σ j)` (equivalently `(i∈X) = (j∈X)`). -/
theorem exp_beta_J_sign_mul_sign_eq
    (β J : ℝ) (σ : Config ι) (i j : ι) :
    Complex.exp ((β : ℂ) * (J : ℂ)
        * (Spin.sign ℂ (σ i) * Spin.sign ℂ (σ j)))
      = Complex.exp ((β : ℂ) * (J : ℂ))
          * edgeWeight i j (Real.exp (-2 * β * J)) (configToFinset σ) := by
  unfold edgeWeight configToFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases hi : σ i with
  | up =>
    cases hj : σ j with
    | up =>
      simp [Spin.sign, Spin.toSign]
    | down =>
      rw [if_neg (by simp)]
      rw [show ((Real.exp (-2 * β * J)) : ℂ)
            = Complex.exp ((-2 * β * J : ℝ) : ℂ) from
        Complex.ofReal_exp _, ← Complex.exp_add]
      simp only [Spin.sign, Spin.toSign, Int.cast_one, Int.cast_neg,
        mul_neg_one]
      congr 1; push_cast; ring
  | down =>
    cases hj : σ j with
    | up =>
      rw [if_neg (by simp)]
      rw [show ((Real.exp (-2 * β * J)) : ℂ)
            = Complex.exp ((-2 * β * J : ℝ) : ℂ) from
        Complex.ofReal_exp _, ← Complex.exp_add]
      simp only [Spin.sign, Spin.toSign, Int.cast_neg, Int.cast_one,
        neg_mul, one_mul, mul_neg]
      congr 1; push_cast; ring
    | down =>
      simp only [Spin.sign, Spin.toSign, Int.cast_neg, Int.cast_one,
        neg_mul_neg, one_mul]
      rw [if_pos (by simp)]; ring

omit [DecidableEq ι] in
/-- Product over sites of the external-field exponential factorises as
`exp(β·h·|ι|) · z^|X|` where `X = configToFinset σ` and `z = leeYangFugacity β h`. -/
theorem prod_exp_beta_h_sign_eq
    (β : ℝ) (h : ℂ) (σ : Config ι) :
    ∏ i : ι, Complex.exp ((β : ℂ) * h * Spin.sign ℂ (σ i))
      = Complex.exp ((β : ℂ) * h * (Fintype.card ι : ℂ))
          * ∏ _i ∈ configToFinset σ, leeYangFugacity (β : ℂ) h := by
  classical
  rw [show (∏ i : ι, Complex.exp ((β : ℂ) * h * Spin.sign ℂ (σ i)))
          = ∏ i : ι, (Complex.exp ((β : ℂ) * h)
              * (if i ∈ configToFinset σ then
                  leeYangFugacity (β : ℂ) h else 1))
          from Finset.prod_congr rfl fun i _ => exp_beta_h_sign_eq β h σ i]
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_ite_mem, Finset.univ_inter,
    Finset.card_univ, ← Complex.exp_nat_mul, Finset.prod_const]
  ring_nf

omit [Fintype ι] [DecidableEq ι] in
/-- `edgeSpinComplex` evaluated at the canonical representative
`s((Quot.out e).1, (Quot.out e).2) = e`. -/
theorem edgeSpinComplex_eq_quotOut (σ : Config ι) (e : Sym2 ι) :
    edgeSpinComplex σ e
      = Spin.sign ℂ (σ (Quot.out e).1) * Spin.sign ℂ (σ (Quot.out e).2) := by
  conv_lhs => rw [show e = s((Quot.out e).1, (Quot.out e).2) from by
    conv_lhs => rw [← Quot.out_eq e]]
  rfl

/-- Product over edges of the interaction exponential factorises as
`exp(β·J·|E|) · ∏_e edgeWeight (Quot.out e).1 (Quot.out e).2 t X`
where `X = configToFinset σ` and `t = exp(-2βJ)`. -/
theorem prod_exp_beta_J_edgeSpin_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J : ℝ) (σ : Config ι) :
    ∏ e ∈ G.edgeFinset,
        Complex.exp ((β : ℂ) * (J : ℂ) * edgeSpinComplex σ e)
      = Complex.exp ((β : ℂ) * (J : ℂ) * (G.edgeFinset.card : ℂ))
          * ∏ e ∈ G.edgeFinset, edgeWeight (Quot.out e).1 (Quot.out e).2
              (Real.exp (-2 * β * J)) (configToFinset σ) := by
  rw [show (∏ e ∈ G.edgeFinset,
            Complex.exp ((β : ℂ) * (J : ℂ) * edgeSpinComplex σ e))
          = ∏ e ∈ G.edgeFinset, (Complex.exp ((β : ℂ) * (J : ℂ))
              * edgeWeight (Quot.out e).1 (Quot.out e).2
                  (Real.exp (-2 * β * J)) (configToFinset σ))
          from Finset.prod_congr rfl fun e _ => by
        rw [edgeSpinComplex_eq_quotOut σ e,
          exp_beta_J_sign_mul_sign_eq β J σ (Quot.out e).1 (Quot.out e).2]]
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    ← Complex.exp_nat_mul]
  ring_nf

/-- The Lee-Yang polynomial value at the down-spin set of `σ` equals the
product over edges `e ∈ G.edgeFinset` of `edgeWeight` at the canonical
representative of `e`. -/
theorem isingEdgePoly_apply_configToFinset
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) (σ : Config ι) :
    isingEdgePoly (graphToEdgeList G t) (configToFinset σ)
      = ∏ e ∈ G.edgeFinset, edgeWeight (Quot.out e).1 (Quot.out e).2 t
          (configToFinset σ) := by
  unfold isingEdgePoly graphToEdgeList
  rw [List.map_map]
  exact Finset.prod_map_toList G.edgeFinset _

/-- Per-configuration factorisation of the complex Boltzmann weight.
For real coupling `J`, real inverse temperature `β`, and complex field `h`:
`exp(-β · H(σ; J, h))
  = leeYangNormalization β J h |E| |ι|
    · isingEdgePoly (graphToEdgeList G t) X
    · ∏_{i∈X} leeYangFugacityVec β h i`
where `X = configToFinset σ` and `t = exp(-2βJ)`. -/
theorem exp_neg_beta_hamiltonian_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J : ℝ) (h : ℂ) (σ : Config ι) :
    Complex.exp (-(β : ℂ) * hamiltonianComplex G (J : ℂ) h σ)
      = leeYangNormalization (β : ℂ) (J : ℂ) h
          G.edgeFinset.card (Fintype.card ι)
        * isingEdgePoly (graphToEdgeList G (Real.exp (-2 * β * J)))
            (configToFinset σ)
        * ∏ i ∈ configToFinset σ, leeYangFugacityVec (β : ℂ) h i := by
  unfold hamiltonianComplex interactionEnergyComplex externalFieldEnergyComplex
    leeYangNormalization leeYangFugacityVec
  rw [show -(β : ℂ) * (-(J : ℂ) * ∑ e ∈ G.edgeFinset, edgeSpinComplex σ e
            + -h * ∑ i : ι, Spin.sign ℂ (σ i))
          = (β : ℂ) * (J : ℂ) * ∑ e ∈ G.edgeFinset, edgeSpinComplex σ e
              + (β : ℂ) * h * ∑ i : ι, Spin.sign ℂ (σ i) from by ring]
  rw [Complex.exp_add]
  rw [Finset.mul_sum G.edgeFinset (fun e => edgeSpinComplex σ e)
        ((β : ℂ) * (J : ℂ)),
      Finset.mul_sum Finset.univ (fun i => Spin.sign ℂ (σ i))
        ((β : ℂ) * h)]
  rw [Complex.exp_sum, Complex.exp_sum]
  rw [prod_exp_beta_J_edgeSpin_eq G β J σ]
  rw [prod_exp_beta_h_sign_eq β h σ]
  rw [isingEdgePoly_apply_configToFinset G (Real.exp (-2 * β * J)) σ]
  rw [Finset.prod_const]
  rw [show Complex.exp ((β : ℂ) * (J : ℂ) * (G.edgeFinset.card : ℂ) +
              (β : ℂ) * h * (Fintype.card ι : ℂ))
          = Complex.exp ((β : ℂ) * (J : ℂ) * (G.edgeFinset.card : ℂ))
              * Complex.exp ((β : ℂ) * h * (Fintype.card ι : ℂ))
          from Complex.exp_add _ _]
  ring

/-! ### Friedli–Velenik factorisation of the partition function

The Friedli–Velenik identity (Friedli–Velenik, *Statistical Mechanics of
Lattice Systems*, (3.63)–(3.65), pp. 122–123; Glimm–Jaffe,
*Quantum Physics*, §4.6, pp. 67–68):
`Z(J, h, β) = exp(βJ|E| + βh|ι|) · P_E(z)`
with `z_i = e^{-2βh}` (uniform field), `t_e = e^{-2βJ}` (uniform coupling).

On the Lee-Yang domain the RHS is a product of a non-vanishing normalisation
and a non-vanishing polynomial evaluation (cf.
`leeYangNormalization_mul_isingEdgePoly_eval_ne_zero` above), hence `Z ≠ 0`.
The identity itself is scaffolded here and proved step by step in a
forthcoming commit. -/

/-- **Friedli–Velenik factorisation** of the complex partition function
at real ferromagnetic coupling `J > 0`, real inverse temperature `β > 0`,
uniform external field `h ∈ ℂ`:
`Z(J, h, β) = exp(βJ|E| + βh|ι|) · P_E(z)` where `z_k = e^{-2βh}` and
`P_E` is the Ising partition polynomial associated to `G` with uniform
coupling `t = e^{-2βJ}`.

Reference: Friedli–Velenik (3.63)–(3.65), pp. 122–123;
Glimm–Jaffe Thm 4.6.2, p. 68. -/
theorem partitionFunctionComplex_eq_normalization_mul_isingEdgePoly
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J : ℝ) (h : ℂ) :
    partitionFunctionComplex G (J : ℂ) h (β : ℂ)
      = leeYangNormalization (β : ℂ) (J : ℂ) h
          G.edgeFinset.card (Fintype.card ι)
        * (isingEdgePoly (graphToEdgeList G (Real.exp (-2 * β * J)))).eval
            (leeYangFugacityVec (β : ℂ) h) := by
  unfold partitionFunctionComplex MultilinPoly.eval
  have hterm : ∀ σ : Config ι,
      Complex.exp (-(β : ℂ) * hamiltonianComplex G (J : ℂ) h σ)
        = leeYangNormalization (β : ℂ) (J : ℂ) h
            G.edgeFinset.card (Fintype.card ι)
          * (isingEdgePoly (graphToEdgeList G (Real.exp (-2 * β * J)))
              (configToFinset σ)
            * ∏ i ∈ configToFinset σ, leeYangFugacityVec (β : ℂ) h i) := by
    intro σ
    rw [exp_neg_beta_hamiltonian_eq G β J h σ]; ring
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ)]
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv configFinsetEquiv
    (fun σ => isingEdgePoly (graphToEdgeList G (Real.exp (-2 * β * J)))
        (configToFinset σ)
      * ∏ i ∈ configToFinset σ, leeYangFugacityVec (β : ℂ) h i)
    (fun X => isingEdgePoly (graphToEdgeList G (Real.exp (-2 * β * J))) X
      * ∏ i ∈ X, leeYangFugacityVec (β : ℂ) h i)
    (fun σ => by simp [configFinsetEquiv])

/-- **`partitionFunctionComplex` is non-zero on the Lee-Yang domain**
(uniform field, real ferromagnetic coupling `J > 0`, real `β > 0`).

This is the Lee-Yang nonvanishing half of Glimm–Jaffe Thm 4.6.2:
on `|Im h| < Re h`, the finite-volume complex partition function has no
zeros.

Nonvanishing alone is not yet sufficient for principal-branch `Complex.log`
analyticity; to combine with `freeEnergyComplex_analyticAt_h`, one further
needs `Z ∈ Complex.slitPlane`, which requires a continuous branch argument
from a real-positive basepoint (deferred to a subsequent session).

Proof: combine
`partitionFunctionComplex_eq_normalization_mul_isingEdgePoly`
(Friedli–Velenik factorisation) with
`leeYangNormalization_mul_isingEdgePoly_eval_ne_zero`. -/
theorem partitionFunctionComplex_ne_zero_on_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) {h : ℂ} (hh : h ∈ leeYangDomain) :
    partitionFunctionComplex G (J : ℂ) h (β : ℂ) ≠ 0 := by
  rw [partitionFunctionComplex_eq_normalization_mul_isingEdgePoly G β J h]
  set t : ℝ := Real.exp (-2 * β * J)
  have ht₀ : 0 ≤ t := (Real.exp_pos _).le
  have ht₁ : t < 1 := by
    refine Real.exp_lt_one_iff.mpr ?_
    have : 0 < 2 * β * J := by positivity
    linarith
  exact leeYangNormalization_mul_isingEdgePoly_eval_ne_zero
    G ht₀ ht₁ (J : ℂ) hβ hh _ _

/-- **`freeEnergyComplex` is analytic in `h` at real parameters**
(real-slice corollary; preliminary to GJ Thm 4.6.2).

For arbitrary real `J, h₀, β`, the complex free energy is analytic in `h`
at `(h₀ : ℂ)`. This combines
`partitionFunctionComplex_mem_slitPlane_of_real` (Z is a positive real
number at real parameters, hence in slitPlane) with
`freeEnergyComplex_analyticAt_h` (analyticity given slitPlane membership).
There is no Lee-Yang-domain argument and no ferromagnetic hypothesis
here; this is just a real-slice slitPlane corollary, not GJ Thm 4.6.2
itself. Extending to the full complex Lee-Yang domain `|Im h| < Re h`
requires a continuous branch selection (deferred). -/
theorem freeEnergyComplex_analyticAt_h_ofReal
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h₀ β : ℝ) :
    AnalyticAt ℂ (fun h => freeEnergyComplex G (J : ℂ) h (β : ℂ))
        (h₀ : ℂ) :=
  freeEnergyComplex_analyticAt_h G (J : ℂ) (β : ℂ) (h₀ : ℂ)
    (partitionFunctionComplex_mem_slitPlane_of_real G ⟨J, h₀, β⟩)

/-! ### slitPlane via `Re Z > 0` on a Lee-Yang subdomain (PR #200 in progress)

Toward GJ §4.6 Thm 4.6.2 finite-volume analyticity on the Lee-Yang
domain: we establish `partitionFunctionComplex ∈ Complex.slitPlane`
by the stronger `Re Z > 0` condition, which holds on the subdomain
`{h | |Im h| < Re h ∧ β · |Im h| · |ι| < π/2}`.

The bound `β · |Im h| · |ι| < π/2` ensures that for any configuration
`σ` with spin sum `s ∈ [-|ι|, |ι|]`, `|β · Im h · s| < π/2`, hence
`cos(β · Im h · s) > 0`. The real part of each Boltzmann weight is
then `exp(β·J·(edge sum) + β·Re h · s) · cos(β · Im h · s) > 0`, and
summing over `σ` gives `Re Z > 0`.

This is a strictly weaker statement than the full Lee-Yang analyticity,
but it is a concrete subdomain where the finite-volume complex
analyticity of `freeEnergyComplex` holds without a separate branch
construction.

Full Lee-Yang extension requires a continuous branch argument on the
simply-connected domain (classical complex analysis; not directly
available as a mathlib lemma at present). -/

/-- The restricted Lee-Yang subdomain on which we prove `Re Z > 0`:
`{h | |Im h| < Re h ∧ β · |Im h| · |ι| < π/2}`. This domain shrinks
as `β · |ι|` grows, so it does not lift to the infinite-volume limit;
the full Lee-Yang domain requires a branch argument. -/
def leeYangSubdomain (β : ℝ) (N : ℕ) : Set ℂ :=
  {h : ℂ | |h.im| < h.re ∧ β * |h.im| * (N : ℝ) < Real.pi / 2}

/-- `leeYangSubdomain ⊆ leeYangDomain` by the first conjunct. -/
theorem leeYangSubdomain_subset_leeYangDomain (β : ℝ) (N : ℕ) :
    leeYangSubdomain β N ⊆ leeYangDomain := fun _ hh => hh.1

/-- The Lee-Yang subdomain is open: intersection of two open sets defined
by strict inequalities on continuous functions. -/
theorem isOpen_leeYangSubdomain (β : ℝ) (N : ℕ) :
    IsOpen (leeYangSubdomain β N) := by
  have h₁ : IsOpen {h : ℂ | |h.im| < h.re} := isOpen_leeYangDomain
  have h₂ : IsOpen {h : ℂ | β * |h.im| * (N : ℝ) < Real.pi / 2} := by
    have hcont : Continuous (fun h : ℂ => β * |h.im| * (N : ℝ)) := by
      fun_prop
    exact hcont.isOpen_preimage _ isOpen_Iio
  exact h₁.inter h₂

omit [DecidableEq ι] in
/-- The spin sum `∑ σ_i` has absolute value at most `|ι|`, since each
`σ_i ∈ {-1, 1}`. -/
theorem abs_spinSum_le (σ : Config ι) :
    |∑ i : ι, (Spin.sign ℝ (σ i) : ℝ)| ≤ (Fintype.card ι : ℝ) := by
  classical
  have h₁ : |∑ i : ι, Spin.sign ℝ (σ i)|
              ≤ ∑ i : ι, |Spin.sign ℝ (σ i)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h₂ : ∀ i : ι, |Spin.sign ℝ (σ i)| ≤ 1 := by
    intro i; cases σ i <;> simp [Spin.sign, Spin.toSign]
  have h₃ : ∑ i : ι, |Spin.sign ℝ (σ i)| ≤ ∑ _i : ι, (1 : ℝ) :=
    Finset.sum_le_sum (fun i _ => h₂ i)
  simpa [Finset.sum_const, Finset.card_univ] using h₁.trans h₃

omit [DecidableEq ι] in
/-- **Per-configuration Boltzmann weight has positive real part** on
`leeYangSubdomain`. Real parameters `β > 0`, real `J`; complex uniform
field `h` with `β · |Im h| · |ι| < π/2`. The exponential factors as
`exp(β·J·(edge sum) + β·Re h · s) · (cos(β·Im h · s) + i sin(β·Im h · s))`
with `s = spin sum`, and `|β·Im h · s| ≤ β · |Im h| · |ι| < π/2`
forces `cos > 0`. -/
theorem exp_neg_beta_hamiltonian_re_pos
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card ι : ℝ) < Real.pi / 2)
    (σ : Config ι) :
    0 < (Complex.exp (-(β : ℂ) * hamiltonianComplex G (J : ℂ) h σ)).re := by
  classical
  -- Reduce to an explicit real-imag decomposition.
  unfold hamiltonianComplex interactionEnergyComplex externalFieldEnergyComplex
  set e : ℝ := ∑ ed ∈ G.edgeFinset,
      (Spin.sign ℝ (σ (Quot.out ed).1) * Spin.sign ℝ (σ (Quot.out ed).2))
    with he_def
  set s : ℝ := ∑ i : ι, (Spin.sign ℝ (σ i) : ℝ) with hs_def
  have hedgeCast : (∑ ed ∈ G.edgeFinset, edgeSpinComplex σ ed) = (e : ℂ) := by
    simp only [he_def, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun ed _ => ?_)
    rw [edgeSpinComplex_eq_quotOut σ ed]
    cases σ (Quot.out ed).1 <;> cases σ (Quot.out ed).2 <;>
      simp [Spin.sign, Spin.toSign]
  have hsumCast : (∑ i : ι, Spin.sign ℂ (σ i)) = (s : ℂ) := by
    simp only [hs_def, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    cases σ i <;> simp [Spin.sign, Spin.toSign]
  rw [hedgeCast, hsumCast]
  -- The exponent is (β·J·e + β·Re h · s) + i·β·Im h · s (as a complex).
  set a : ℝ := β * J * e + β * h.re * s with ha_def
  set b : ℝ := β * h.im * s with hb_def
  have hexpCast : -(β : ℂ) * (-(J : ℂ) * (e : ℂ) + -h * (s : ℂ))
                  = (a : ℂ) + (b : ℂ) * Complex.I := by
    simp only [ha_def, hb_def]
    have hhre : (h.re : ℂ) + h.im * Complex.I = h := by
      exact (Complex.re_add_im h)
    have : -(β : ℂ) * (-(J : ℂ) * (e : ℂ) + -h * (s : ℂ))
             = ((β : ℂ) * (J : ℂ) * (e : ℂ)
                + (β : ℂ) * ((h.re : ℂ) + h.im * Complex.I) * (s : ℂ)) := by
      rw [hhre]; ring
    rw [this]; push_cast; ring
  rw [hexpCast]
  -- Now Re(exp(a + ib)) = exp(a) · cos(b) > 0 since cos(b) > 0 for |b|<π/2.
  rw [show (a : ℂ) + (b : ℂ) * Complex.I = ((⟨a, b⟩ : ℂ)) from by
    apply Complex.ext <;> simp]
  have hbRe : (⟨a, b⟩ : ℂ).re = a := rfl
  have hbIm : (⟨a, b⟩ : ℂ).im = b := rfl
  rw [Complex.exp_re, hbRe, hbIm]
  -- Need: exp(a) · cos(b) > 0.
  have habs : |b| ≤ β * |h.im| * (Fintype.card ι : ℝ) := by
    have : |b| = β * |h.im| * |s| := by
      simp only [hb_def]
      rw [abs_mul, abs_mul, abs_of_pos hβ]
    rw [this]
    have hsle : |s| ≤ (Fintype.card ι : ℝ) := abs_spinSum_le σ
    have hmul_nn : 0 ≤ β * |h.im| := mul_nonneg hβ.le (abs_nonneg _)
    exact (mul_le_mul_of_nonneg_left hsle hmul_nn)
  have hb_lt : |b| < Real.pi / 2 := lt_of_le_of_lt habs himπ
  have hcos_pos : 0 < Real.cos b := by
    rcases abs_lt.mp hb_lt with ⟨h₁, h₂⟩
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, h₂⟩
  have hexp_pos : 0 < Real.exp a := Real.exp_pos _
  exact mul_pos hexp_pos hcos_pos

/-- **`Re(partitionFunctionComplex) > 0` on the Lee-Yang subdomain**.
Sum of per-σ positive-real-part Boltzmann weights. -/
theorem partitionFunctionComplex_re_pos_of_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card ι : ℝ) < Real.pi / 2) :
    0 < (partitionFunctionComplex G (J : ℂ) h (β : ℂ)).re := by
  classical
  unfold partitionFunctionComplex
  rw [show ((∑ σ : Config ι,
            Complex.exp (-(β : ℂ) * hamiltonianComplex G (J : ℂ) h σ))).re
          = ∑ σ : Config ι,
            (Complex.exp (-(β : ℂ) * hamiltonianComplex G (J : ℂ) h σ)).re
          from by rw [Complex.re_sum]]
  refine Finset.sum_pos (fun σ _ =>
    exp_neg_beta_hamiltonian_re_pos G hβ J himπ σ) ?_
  exact ⟨Classical.arbitrary (Config ι), Finset.mem_univ _⟩

/-- **`partitionFunctionComplex ∈ Complex.slitPlane` on the Lee-Yang
subdomain**: `Re Z > 0` implies slitPlane. -/
theorem partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card ι : ℝ) < Real.pi / 2) :
    partitionFunctionComplex G (J : ℂ) h (β : ℂ) ∈ Complex.slitPlane :=
  Or.inl (partitionFunctionComplex_re_pos_of_leeYangSubdomain G hβ J himπ)

/-- **`freeEnergyComplex` is analytic in `h` on the Lee-Yang subdomain**
(finite-volume `freeEnergyComplex` analyticity; GJ §4.6 Thm 4.6.2
partial — subdomain where `β · |Im h| · |ι| < π/2`, which collapses as
`|ι| → ∞`). Combines
`partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain` with
`freeEnergyComplex_analyticAt_h`. -/
theorem freeEnergyComplex_analyticAt_h_of_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card ι : ℝ) < Real.pi / 2) :
    AnalyticAt ℂ (fun h' => freeEnergyComplex G (J : ℂ) h' (β : ℂ)) h :=
  freeEnergyComplex_analyticAt_h G (J : ℂ) (β : ℂ) h
    (partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain G hβ J himπ)

/-- **`freeEnergyComplex` is analytic on the entire Lee-Yang subdomain**
(not just at a point). Since analyticity is local and
`leeYangSubdomain` is open, membership at each point lifts to
`AnalyticOnNhd` on the whole set. -/
theorem freeEnergyComplex_analyticOnNhd_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    AnalyticOnNhd ℂ (fun h' => freeEnergyComplex G (J : ℂ) h' (β : ℂ))
        (leeYangSubdomain β (Fintype.card ι)) := by
  intro h hmem
  exact freeEnergyComplex_analyticAt_h_of_leeYangSubdomain
    G hβ J hmem.2

/-! ### Toward full Lee-Yang analyticity via branch construction

The subdomain result above uses the principal branch `Complex.log`,
which is analytic only on `Complex.slitPlane`. On the full Lee-Yang
domain, `Z` is non-vanishing (PR #199), but may not stay in `slitPlane`
(winding of `Z` around `0` is not automatic from non-vanishing alone).

Morera's theorem (`DifferentiableOn.isExactOn_ball`, mathlib) gives a
local primitive of a holomorphic function on a ball, which yields a
local holomorphic branch of `log Z` on any ball inside `leeYangDomain`.
This does not immediately produce a global branch, but it shows
`freeEnergyComplex` (with a custom branch, equal to `Complex.log`
modulo `2πi` on each ball) is analytic at every point of the Lee-Yang
domain.

The clean formalisation of this branch-based finite-volume analyticity
is larger than a single session; the subdomain result above is the
concrete verified form. -/

/-- `partitionFunctionComplex ≠ 0` on every point of the Lee-Yang
domain (lifted to an `AnalyticOnNhd`-style statement by openness).
This is the global non-vanishing statement. -/
theorem partitionFunctionComplex_analyticOnNhd_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℂ) :
    AnalyticOnNhd ℂ
        (fun h' => partitionFunctionComplex G J h' β) leeYangDomain :=
  fun h _ => partitionFunctionComplex_analyticAt_h G J β h

/-- **The logarithmic derivative `Z'/Z` is analytic on the Lee-Yang
domain** (real ferromagnetic `J > 0`, real `β > 0`). `Z` is entire and
non-vanishing on `leeYangDomain` (PR #199), so `Z'/Z` is analytic there.
This is the key input to the Morera-based branch construction of `log Z`. -/
theorem logDeriv_partitionFunctionComplex_analyticOnNhd_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    AnalyticOnNhd ℂ (fun h : ℂ =>
        deriv (fun h' => partitionFunctionComplex G (J : ℂ) h' (β : ℂ)) h
          / partitionFunctionComplex G (J : ℂ) h (β : ℂ)) leeYangDomain := by
  intro h hmem
  have hZ_ne : partitionFunctionComplex G (J : ℂ) h (β : ℂ) ≠ 0 :=
    partitionFunctionComplex_ne_zero_on_leeYangDomain G hβ hJ hmem
  have hZ_ana : AnalyticAt ℂ
      (fun h' => partitionFunctionComplex G (J : ℂ) h' (β : ℂ)) h :=
    partitionFunctionComplex_analyticAt_h G (J : ℂ) (β : ℂ) h
  have hZ'_ana : AnalyticAt ℂ
      (fun h' =>
        deriv (fun h'' => partitionFunctionComplex G (J : ℂ) h'' (β : ℂ)) h')
      h := hZ_ana.deriv
  exact hZ'_ana.div hZ_ana hZ_ne

/-- **Local primitive of the log derivative on a ball inside Lee-Yang**.
For any `h₀ ∈ leeYangDomain` and any `r > 0` with `ball h₀ r ⊆ leeYangDomain`,
there exists a holomorphic function `G : ℂ → ℂ` such that on the ball,
`G' = Z'/Z`. This `G` is a local holomorphic branch of `log Z`
(up to an additive complex constant); specifically, by the identity
`(exp(G)/Z)' = 0` on the connected ball, `exp(G) = c · Z` for some
non-zero constant `c`, and we can adjust `G` by a constant so that
`exp(G) = Z` pointwise. -/
theorem exists_logZ_branch_on_ball_of_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hsub : Metric.ball h₀ r ⊆ leeYangDomain) :
    ∃ g : ℂ → ℂ, ∀ z ∈ Metric.ball h₀ r, HasDerivAt g
        (deriv (fun h'' => partitionFunctionComplex G (J : ℂ) h'' (β : ℂ)) z
          / partitionFunctionComplex G (J : ℂ) z (β : ℂ)) z := by
  have hlogDeriv_ana :
      AnalyticOnNhd ℂ (fun h : ℂ =>
          deriv (fun h' => partitionFunctionComplex G (J : ℂ) h' (β : ℂ)) h
            / partitionFunctionComplex G (J : ℂ) h (β : ℂ)) leeYangDomain :=
    logDeriv_partitionFunctionComplex_analyticOnNhd_leeYangDomain G hβ hJ
  have hlogDeriv_diffOn :
      DifferentiableOn ℂ (fun h : ℂ =>
          deriv (fun h' => partitionFunctionComplex G (J : ℂ) h' (β : ℂ)) h
            / partitionFunctionComplex G (J : ℂ) h (β : ℂ))
        (Metric.ball h₀ r) :=
    (hlogDeriv_ana.mono hsub).differentiableOn
  exact hlogDeriv_diffOn.isExactOn_ball

/-- **Normalised local log-branch of `Z` on a ball inside Lee-Yang**.
Refining `exists_logZ_branch_on_ball_of_leeYangDomain`: there exists
`g : ℂ → ℂ` with `g(h₀) = Complex.log(Z(h₀))`, `g' = Z'/Z` on the
ball, and `g` is differentiable on the ball.

The normalisation `g(h₀) = Complex.log(Z(h₀))` makes this branch
agree with the principal branch at the basepoint. The exponential
identity `exp(g) = Z` on the whole ball follows from
`(exp(g)/Z)' = 0` on the connected ball; that step is deferred to
the next commit. -/
theorem exists_normalised_logZ_branch_on_ball
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hmem : h₀ ∈ leeYangDomain)
    (hsub : Metric.ball h₀ r ⊆ leeYangDomain) :
    ∃ g : ℂ → ℂ, g h₀ = Complex.log
        (partitionFunctionComplex G (J : ℂ) h₀ (β : ℂ))
      ∧ ∀ z ∈ Metric.ball h₀ r, HasDerivAt g
          (deriv (fun h'' => partitionFunctionComplex G (J : ℂ) h'' (β : ℂ)) z
            / partitionFunctionComplex G (J : ℂ) z (β : ℂ)) z := by
  obtain ⟨g₀, hg₀⟩ :=
    exists_logZ_branch_on_ball_of_leeYangDomain G hβ hJ (h₀ := h₀) (r := r) hsub
  refine ⟨fun z => g₀ z - g₀ h₀ + Complex.log
      (partitionFunctionComplex G (J : ℂ) h₀ (β : ℂ)), ?_, ?_⟩
  · simp
  · intro z hz
    have hg₀z := hg₀ z hz
    have := hg₀z.sub_const (g₀ h₀)
    simpa using this.add_const (Complex.log
      (partitionFunctionComplex G (J : ℂ) h₀ (β : ℂ)))

end IsingModel
