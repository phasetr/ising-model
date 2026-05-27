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

/-- Weighted scaled-Boltzmann sum is differentiable in β. -/
private theorem hasDerivAt_weightedScaledBoltzmannSum_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (J s β : ℝ) (F : Config ι → ℝ) :
    HasDerivAt
      (fun β' => ∑ σ : Config ι, F σ * scaledBoltzmannWeight G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s σ)
      (∑ σ : Config ι, F σ *
        ((- hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
            - (1 - s) * J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e)) *
          scaledBoltzmannWeight G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s σ)) β :=
  HasDerivAt.fun_sum (fun σ _ =>
    (hasDerivAt_scaledBoltzmannWeight_beta G E₀ J s β σ).const_mul (F σ))

/-- **β-derivative of the scaled Gibbs expectation** (quotient rule): with the
per-configuration β-log-derivative of the weight `D σ = -H σ - (1-s)J·∑_{E₀}σ_e`
(`H` the Hamiltonian),
`∂_β ⟨F⟩_s = ⟨F·D⟩_s − ⟨F⟩_s·⟨D⟩_s`. Third piece of the scaled-correlation
β-derivative chain (Issue #2965, Phase C). -/
theorem hasDerivAt_scaledGibbsExpectation_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (J s β : ℝ) (F : Config ι → ℝ) :
    HasDerivAt
      (fun β' => scaledGibbsExpectation G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s F)
      (scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s
            (fun σ => F σ * (- hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
              - (1 - s) * J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e))) -
       scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s F *
       scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s
            (fun σ => - hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
              - (1 - s) * J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e)))
      β := by
  have hZpos : 0 < scaledPartitionFunction G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s :=
    scaledPartitionFunction_pos G E₀ _ s
  have hZne : scaledPartitionFunction G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s ≠ 0 := hZpos.ne'
  set Zs : ℝ → ℝ := fun β' => scaledPartitionFunction G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s
    with hZs_def
  set Ns : ℝ → ℝ :=
    fun β' => ∑ σ : Config ι, F σ * scaledBoltzmannWeight G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s σ
    with hNs_def
  have hge_eq : ∀ β', scaledGibbsExpectation G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s F
      = (Zs β')⁻¹ * Ns β' := fun _ => rfl
  simp_rw [hge_eq]
  have hZderiv : HasDerivAt Zs
      (∑ σ : Config ι,
        (- hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
            - (1 - s) * J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e)) *
          scaledBoltzmannWeight G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s σ) β :=
    hasDerivAt_scaledPartitionFunction_beta G E₀ J s β
  have hZinv := hZderiv.inv hZne
  have hNderiv : HasDerivAt Ns
      (∑ σ : Config ι, F σ *
        ((- hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
            - (1 - s) * J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e)) *
          scaledBoltzmannWeight G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s σ)) β :=
    hasDerivAt_weightedScaledBoltzmannSum_beta G E₀ J s β F
  have hprod := hZinv.mul hNderiv
  convert hprod using 1
  simp only [scaledGibbsExpectation, hZs_def, hNs_def]
  set D : Config ι → ℝ := fun σ => - hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
    - (1 - s) * J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) with hD_def
  set w : Config ι → ℝ := fun σ => scaledBoltzmannWeight G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s σ
    with hw_def
  set Z := scaledPartitionFunction G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s with hZ_def
  set NF : ℝ := ∑ σ : Config ι, F σ * w σ with hNF_def
  set ND : ℝ := ∑ σ : Config ι, D σ * w σ with hND_def
  set NFD : ℝ := ∑ σ : Config ι, F σ * (D σ * w σ) with hNFD_def
  have hNFD' : ∑ σ : Config ι, F σ * D σ * w σ = NFD :=
    Finset.sum_congr rfl (fun σ _ => by ring)
  rw [hNFD']
  simp only [Pi.inv_apply]
  rw [← hZ_def]
  field_simp [hZne]
  ring

/-- **β-derivative of the scaled correlation**: specialising the scaled Gibbs
β-derivative to `F = spinProduct A`,
`∂_β ⟨σ^A⟩_s = ⟨σ^A·D⟩_s − ⟨σ^A⟩_s·⟨D⟩_s` with the β-log-derivative of the weight
`D σ = -H σ - (1-s)J·∑_{E₀}σ_e`. Final piece of the scaled-correlation β-derivative
chain (Issue #2965, Phase C, mixed `∂_β∂_s` route): the inner `β`-derivative used
to bound the finite-volume β-derivative increment `g_k'(β) = ∫₀¹ ∂_β∂_s
scaledCorrelation ds` as a shell sum. -/
theorem hasDerivAt_scaledCorrelation_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (J s β : ℝ) (A : Finset ι) :
    HasDerivAt (fun β' => scaledCorrelation G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s A)
      (scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s
            (fun σ => spinProduct A σ * (- hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
              - (1 - s) * J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e))) -
       scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s (spinProduct A) *
       scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s
            (fun σ => - hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
              - (1 - s) * J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e)))
      β :=
  hasDerivAt_scaledGibbsExpectation_beta G E₀ J s β (spinProduct A)

/-- Abbreviation: the per-configuration β-log-derivative of the scaled weight,
`D σ = -H σ - (1-s)J·∑_{E₀} σ_e`. -/
private noncomputable def betaLogDeriv (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (J s β : ℝ) (σ : Config ι) : ℝ :=
  - hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ - (1 - s) * J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e)

/-- **β-derivative of one scaled-correlation truncated (Ursell-like) summand**:
`∂_β [⟨σ^B⟩_s − ⟨σ^A⟩_s·⟨σ^C⟩_s]
   = ⟨σ^B·D⟩_s − ⟨σ^B⟩_s⟨D⟩_s
     − [(⟨σ^A·D⟩_s − ⟨σ^A⟩_s⟨D⟩_s)·⟨σ^C⟩_s + ⟨σ^A⟩_s·(⟨σ^C·D⟩_s − ⟨σ^C⟩_s⟨D⟩_s)]`,
with `D = betaLogDeriv` the β-log-derivative of the weight. Built from
`hasDerivAt_scaledCorrelation_beta` (at `B`, `A`, `C`) via the difference and
product rules. The per-edge building block of the mixed `∂_β∂_s` derivative for the
β-derivative increment (Issue #2965, Phase C, mixed route). -/
theorem hasDerivAt_scaledCorrelation_truncated_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (J s β : ℝ) (A B C : Finset ι) :
    HasDerivAt (fun β' => scaledCorrelation G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s B
        - scaledCorrelation G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s A *
          scaledCorrelation G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s C)
      ((scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s
            (fun σ => spinProduct B σ * betaLogDeriv G E₀ J s β σ) -
          scaledCorrelation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s B *
            scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s (betaLogDeriv G E₀ J s β)) -
        ((scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s
              (fun σ => spinProduct A σ * betaLogDeriv G E₀ J s β σ) -
            scaledCorrelation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s A *
              scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s
                (betaLogDeriv G E₀ J s β)) *
            scaledCorrelation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s C +
          scaledCorrelation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s A *
            (scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s
                (fun σ => spinProduct C σ * betaLogDeriv G E₀ J s β σ) -
              scaledCorrelation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s C *
                scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s
                  (betaLogDeriv G E₀ J s β)))) β := by
  have hB := hasDerivAt_scaledCorrelation_beta G E₀ J s β B
  have hA := hasDerivAt_scaledCorrelation_beta G E₀ J s β A
  have hC := hasDerivAt_scaledCorrelation_beta G E₀ J s β C
  exact hB.sub (hA.mul hC)

end IsingModel
