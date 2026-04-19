import IsingModel.Hamiltonian
import Mathlib.Analysis.Analytic.Constructions
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

end IsingModel
