import IsingModel.GibbsMeasure
import IsingModel.FreeEnergy
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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

end IsingModel
