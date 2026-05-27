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
noncomputable def betaLogDeriv (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (J s β : ℝ) (σ : Config ι) : ℝ :=
  - hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ - (1 - s) * J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e)

omit [DecidableEq ι] in
/-- At `s = 1` (full, unscaled) the β-log-derivative is just minus the Hamiltonian:
`betaLogDeriv … 1 … = -H` (the `(1-s)` scaling term vanishes). -/
theorem betaLogDeriv_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (J β : ℝ) :
    betaLogDeriv G E₀ J 1 β = fun σ => - hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ := by
  funext σ; simp [betaLogDeriv]

omit [DecidableEq ι] in
/-- At `s = 0` (fully bond-deleted) the β-log-derivative is minus the Hamiltonian
plus the full `E₀`-bond energy: `betaLogDeriv … 0 … = -H - J·∑_{E₀}σ_e`. With
`E₀ ⊆ G.edgeFinset` this equals minus the bond-deleted Hamiltonian
`-(H_{G.deleteEdges E₀})`. -/
theorem betaLogDeriv_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (J β : ℝ) :
    betaLogDeriv G E₀ J 0 β
      = fun σ => - hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
          - J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) := by
  funext σ; simp only [betaLogDeriv]; ring

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

/-- **β-derivative of a truncated scaled Gibbs expression** `⟨F₁⟩_s − ⟨F₂⟩_s·⟨F₃⟩_s`
for arbitrary observables, via `hasDerivAt_scaledGibbsExpectation_beta` and the
difference/product rules (`D = betaLogDeriv`). Generalises
`hasDerivAt_scaledCorrelation_truncated_beta`; specialised to `F₁ = σ^A·W`,
`F₂ = σ^A`, `F₃ = W` (`W = ∑_{E₀}σ_e`) it is the inner factor of the mixed
`∂_β∂_s` derivative, since the `s`-derivative of the scaled correlation is
`βJ·(⟨σ^A·W⟩_s − ⟨σ^A⟩_s⟨W⟩_s)`. -/
theorem hasDerivAt_scaledGibbs_truncated_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (J s β : ℝ) (F₁ F₂ F₃ : Config ι → ℝ) :
    HasDerivAt (fun β' => scaledGibbsExpectation G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s F₁
        - scaledGibbsExpectation G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s F₂ *
          scaledGibbsExpectation G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) s F₃)
      ((scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s
            (fun σ => F₁ σ * betaLogDeriv G E₀ J s β σ) -
          scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s F₁ *
            scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s (betaLogDeriv G E₀ J s β)) -
        ((scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s
              (fun σ => F₂ σ * betaLogDeriv G E₀ J s β σ) -
            scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s F₂ *
              scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s (betaLogDeriv G E₀ J s β)) *
            scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s F₃ +
          scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s F₂ *
            (scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s
                (fun σ => F₃ σ * betaLogDeriv G E₀ J s β σ) -
              scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s F₃ *
                scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s
                  (betaLogDeriv G E₀ J s β)))) β :=
  (hasDerivAt_scaledGibbsExpectation_beta G E₀ J s β F₁).sub
    ((hasDerivAt_scaledGibbsExpectation_beta G E₀ J s β F₂).mul
      (hasDerivAt_scaledGibbsExpectation_beta G E₀ J s β F₃))

/-- **β-derivative of the bond-adding (`s=1` minus `s=0`) scaled-correlation
increment**: the increment `g(β) = ⟨σ^A⟩_{s=1} − ⟨σ^A⟩_{s=0}` (full minus
bond-deleted correlation, via `scaledCorrelation_one`/`scaledCorrelation_zero`) has
β-derivative the difference of the two β-derivatives
(`hasDerivAt_scaledCorrelation_beta` at `s=1` and `s=0`), with `D_s = betaLogDeriv`
(`D_1 = -H`, `D_0 = -H - J·∑_{E₀}σ_e`):
`g'(β) = [⟨σ^A·D_1⟩_1 − ⟨σ^A⟩_1⟨D_1⟩_1] − [⟨σ^A·D_0⟩_0 − ⟨σ^A⟩_0⟨D_0⟩_0]`.
Stated for an arbitrary `E₀`. In the per-stage shell application (`E₀ = ` cut shell,
`E₀ ⊆ G.edgeFinset`, plus the `s=0` bond-deleted identification
`scaledCorrelation_zero`) this is the explicit β-derivative increment
`F_{k+1}(β) − F_k(β)` of the finite-volume derivative profiles; bounding it then
requires (at the application level) the shell cancellation of the full-energy
`⟨σ^A·H⟩` covariance terms between the two systems — the remaining quantitative
input of the GJ §17.5 Lemma 17.5.2 capstone (`hincr`). -/
theorem hasDerivAt_scaledCorrelation_increment_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (J β : ℝ) (A : Finset ι) :
    HasDerivAt (fun β' => scaledCorrelation G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) 1 A
        - scaledCorrelation G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) 0 A)
      ((scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 1
            (fun σ => spinProduct A σ * betaLogDeriv G E₀ J 1 β σ) -
          scaledCorrelation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 1 A *
            scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 1 (betaLogDeriv G E₀ J 1 β)) -
        (scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 0
            (fun σ => spinProduct A σ * betaLogDeriv G E₀ J 0 β σ) -
          scaledCorrelation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 0 A *
            scaledGibbsExpectation G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 0
              (betaLogDeriv G E₀ J 0 β))) β :=
  (hasDerivAt_scaledCorrelation_beta G E₀ J 1 β A).sub
    (hasDerivAt_scaledCorrelation_beta G E₀ J 0 β A)

/-- **Additivity of the scaled Gibbs expectation in the observable**:
`⟨F₁ + F₂⟩_s = ⟨F₁⟩_s + ⟨F₂⟩_s` (the normalised sum `Z_s⁻¹·∑_σ · w_s` is linear). -/
theorem scaledGibbsExpectation_add (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (F₁ F₂ : Config ι → ℝ) :
    scaledGibbsExpectation G E₀ p s (fun σ => F₁ σ + F₂ σ)
      = scaledGibbsExpectation G E₀ p s F₁ + scaledGibbsExpectation G E₀ p s F₂ := by
  unfold scaledGibbsExpectation
  have h : ∑ σ : Config ι, (F₁ σ + F₂ σ) * scaledBoltzmannWeight G E₀ p s σ
      = (∑ σ : Config ι, F₁ σ * scaledBoltzmannWeight G E₀ p s σ)
        + ∑ σ : Config ι, F₂ σ * scaledBoltzmannWeight G E₀ p s σ := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro σ _; ring
  rw [h, mul_add]

/-- **Scalar homogeneity of the scaled Gibbs expectation**: `⟨c·F⟩_s = c·⟨F⟩_s`. -/
theorem scaledGibbsExpectation_const_mul (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (c : ℝ) (F : Config ι → ℝ) :
    scaledGibbsExpectation G E₀ p s (fun σ => c * F σ)
      = c * scaledGibbsExpectation G E₀ p s F := by
  unfold scaledGibbsExpectation
  have h : ∑ σ : Config ι, c * F σ * scaledBoltzmannWeight G E₀ p s σ
      = c * ∑ σ : Config ι, F σ * scaledBoltzmannWeight G E₀ p s σ := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro σ _; ring
  rw [h]; ring

/-- **Subtractivity of the scaled Gibbs expectation in the observable**:
`⟨F₁ − F₂⟩_s = ⟨F₁⟩_s − ⟨F₂⟩_s`. -/
theorem scaledGibbsExpectation_sub (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (F₁ F₂ : Config ι → ℝ) :
    scaledGibbsExpectation G E₀ p s (fun σ => F₁ σ - F₂ σ)
      = scaledGibbsExpectation G E₀ p s F₁ - scaledGibbsExpectation G E₀ p s F₂ := by
  unfold scaledGibbsExpectation
  have h : ∑ σ : Config ι, (F₁ σ - F₂ σ) * scaledBoltzmannWeight G E₀ p s σ
      = (∑ σ : Config ι, F₁ σ * scaledBoltzmannWeight G E₀ p s σ)
        - ∑ σ : Config ι, F₂ σ * scaledBoltzmannWeight G E₀ p s σ := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro σ _; ring
  rw [h, mul_sub]

/-- **Scaled covariance** of two observables: `Cov_s(F,K) = ⟨F·K⟩_s − ⟨F⟩_s·⟨K⟩_s`.
The β-derivative of a scaled correlation/Gibbs expectation is `Cov_s(σ^A, D)` with
`D = betaLogDeriv`, so the β-derivative increment decomposes through covariances. -/
noncomputable def scaledCovariance (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (F K : Config ι → ℝ) : ℝ :=
  scaledGibbsExpectation G E₀ p s (fun σ => F σ * K σ)
    - scaledGibbsExpectation G E₀ p s F * scaledGibbsExpectation G E₀ p s K

/-- **Additivity of the scaled covariance in the second observable**:
`Cov_s(F, K₁ + K₂) = Cov_s(F, K₁) + Cov_s(F, K₂)`. -/
theorem scaledCovariance_add_right (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (F K₁ K₂ : Config ι → ℝ) :
    scaledCovariance G E₀ p s F (fun σ => K₁ σ + K₂ σ)
      = scaledCovariance G E₀ p s F K₁ + scaledCovariance G E₀ p s F K₂ := by
  unfold scaledCovariance
  have hFK : (fun σ => F σ * (K₁ σ + K₂ σ)) = (fun σ => F σ * K₁ σ + F σ * K₂ σ) := by
    funext σ; ring
  rw [hFK, scaledGibbsExpectation_add, scaledGibbsExpectation_add, mul_add]; ring

/-- **Scalar homogeneity of the scaled covariance in the second observable**:
`Cov_s(F, c·K) = c·Cov_s(F, K)`. -/
theorem scaledCovariance_const_mul_right (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (c : ℝ) (F K : Config ι → ℝ) :
    scaledCovariance G E₀ p s F (fun σ => c * K σ)
      = c * scaledCovariance G E₀ p s F K := by
  unfold scaledCovariance
  have hFK : (fun σ => F σ * (c * K σ)) = (fun σ => c * (F σ * K σ)) := by funext σ; ring
  rw [hFK, scaledGibbsExpectation_const_mul, scaledGibbsExpectation_const_mul, mul_sub]; ring

/-- **Subtractivity of the scaled covariance in the second observable**:
`Cov_s(F, K₁ − K₂) = Cov_s(F, K₁) − Cov_s(F, K₂)`. -/
theorem scaledCovariance_sub_right (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (F K₁ K₂ : Config ι → ℝ) :
    scaledCovariance G E₀ p s F (fun σ => K₁ σ - K₂ σ)
      = scaledCovariance G E₀ p s F K₁ - scaledCovariance G E₀ p s F K₂ := by
  unfold scaledCovariance
  have hFK : (fun σ => F σ * (K₁ σ - K₂ σ)) = (fun σ => F σ * K₁ σ - F σ * K₂ σ) := by
    funext σ; ring
  rw [hFK, scaledGibbsExpectation_sub, scaledGibbsExpectation_sub, mul_sub]; ring

/-- **Additivity of the scaled covariance over a Finset sum in the second
observable**: `Cov_s(F, ∑_{e∈S} K_e) = ∑_{e∈S} Cov_s(F, K_e)`. By `Finset.induction`
from `scaledCovariance_add_right` (and `Cov_s(F, 0) = 0`). This expresses the
covariance of an energy/edge sum as a sum of per-edge covariances — used to localize
the shell term `J·Cov_0(σ^A, ∑_{E₀}σ_e) = J·∑_{e∈E₀} Cov_0(σ^A, σ_e)` of the
β-derivative increment decomposition (Issue #2965, Phase C). -/
theorem scaledCovariance_sum_right {κ : Type*} (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (F : Config ι → ℝ)
    (S : Finset κ) (K : κ → Config ι → ℝ) :
    scaledCovariance G E₀ p s F (fun σ => ∑ e ∈ S, K e σ)
      = ∑ e ∈ S, scaledCovariance G E₀ p s F (K e) := by
  classical
  induction S using Finset.induction with
  | empty => simp [scaledCovariance, scaledGibbsExpectation]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    rw [show (fun σ => ∑ e ∈ insert a S, K e σ)
        = (fun σ => K a σ + ∑ e ∈ S, K e σ) from by funext σ; rw [Finset.sum_insert ha],
      scaledCovariance_add_right]

end IsingModel
