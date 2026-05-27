import IsingModel.CouplingDerivative
import IsingModel.BetaDerivative.CorrelationFormulas

/-!
# β-derivative of the scaled Boltzmann weight (Issue #2965, Phase C)

The `s`-coupling-scaled Boltzmann weight
`scaledBoltzmannWeight G E₀ ⟨J,0,β⟩ s σ = boltzmannWeight G ⟨J,0,β⟩ σ ·
exp(-β(1-s)J·∑_{E₀} σ_e)` depends on `β` through both the base weight and the
scaling exponent. This module computes its `β`-derivative — the first piece of the
`β`-derivative chain for the scaled correlation, the mixed `∂_β∂_s` route to the
finite-volume β-derivative increment required by the GJ §17.5 Lemma 17.5.2 capstone.

## Main declaration

* `IsingModel.hasDerivAt_scaledBoltzmannWeight_beta`.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **β-derivative of the scaled Boltzmann weight**: by the product rule on
`boltzmannWeight G ⟨J,0,β'⟩ σ · exp(-β'(1-s)J·X)` (`X = ∑_{E₀} σ_e`), with the base
weight's β-derivative `-H·w` (`hasDerivAt_boltzmannWeight_beta`) and the scaling
exponent's β-derivative `-(1-s)J·X`,
`∂_β (scaledBoltzmannWeight …) = (-H - (1-s)J·X) · scaledBoltzmannWeight …`, where
`H = hamiltonian G ⟨J,0,β⟩ σ`. First piece of the scaled-correlation β-derivative
chain (Issue #2965, Phase C, mixed `∂_β∂_s` route). -/
theorem hasDerivAt_scaledBoltzmannWeight_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (J s β : ℝ) (σ : Config ι) :
    HasDerivAt (fun β' => scaledBoltzmannWeight G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s σ)
      ((- hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
          - (1 - s) * J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e)) *
        scaledBoltzmannWeight G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s σ) β := by
  set X := ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e with hX
  set H := hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ with hH
  -- scaledBoltzmannWeight G E₀ ⟨J,0,β'⟩ s σ = boltzmannWeight G ⟨J,0,β'⟩ σ · exp(-β'(1-s)J·X)
  have hsbw : ∀ β' : ℝ,
      scaledBoltzmannWeight G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s σ
        = boltzmannWeight G (⟨J, 0, β'⟩ : IsingParams ℝ) σ *
            Real.exp (-β' * (1 - s) * J * X) := fun β' => rfl
  simp_rw [hsbw]
  -- base β-derivative: ∂_β boltzmannWeight = -H · w
  have hf := hasDerivAt_boltzmannWeight_beta G J 0 β σ
  -- scaling exponent β-derivative
  have hi : HasDerivAt (fun β' : ℝ => -β' * (1 - s) * J * X) (-(1 - s) * J * X) β := by
    have heq : (fun β' : ℝ => -β' * (1 - s) * J * X)
        = fun β' => (-(1 - s) * J * X) * β' := by funext β'; ring
    rw [heq]
    simpa using (hasDerivAt_id β).const_mul (-(1 - s) * J * X)
  have hmul := hf.mul hi.exp
  convert hmul using 1
  ring

/-- **β-derivative of the scaled partition function**: termwise sum of the scaled
Boltzmann weight β-derivatives (`HasDerivAt.fun_sum`),
`∂_β Z_s = ∑_σ (-H_σ - (1-s)J·X_σ) · scaledBoltzmannWeight … σ`. Second piece of
the scaled-correlation β-derivative chain (Issue #2965, Phase C). -/
theorem hasDerivAt_scaledPartitionFunction_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (J s β : ℝ) :
    HasDerivAt (fun β' => scaledPartitionFunction G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s)
      (∑ σ : Config ι,
        (- hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
            - (1 - s) * J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e)) *
          scaledBoltzmannWeight G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s σ) β := by
  simp only [scaledPartitionFunction]
  exact HasDerivAt.fun_sum
    (fun σ _ => hasDerivAt_scaledBoltzmannWeight_beta G E₀ J s β σ)

end IsingModel
