import IsingModel.CouplingDerivative
import IsingModel.BetaDerivative.CorrelationFormulas
import IsingModel.BetaDerivative.Lebowitz
import IsingModel.BallBoundarySimonLieb.WeakBound

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

/-- **Negation in the second observable of the scaled covariance**:
`Cov_s(F, -K) = -Cov_s(F, K)`. -/
theorem scaledCovariance_neg_right (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (F K : Config ι → ℝ) :
    scaledCovariance G E₀ p s F (fun σ => - K σ) = - scaledCovariance G E₀ p s F K := by
  rw [show (fun σ => - K σ) = (fun σ => (-1 : ℝ) * K σ) from by funext σ; ring,
    scaledCovariance_const_mul_right]
  ring

/-- **Shell-cancellation decomposition of the β-derivative increment** (Issue #2965,
Phase C): the bond-adding increment `g(β) = ⟨σ^A⟩_{s=1} − ⟨σ^A⟩_{s=0}` has
β-derivative
`g'(β) = [Cov_0(σ^A, H) − Cov_1(σ^A, H)] + J·Cov_0(σ^A, ∑_{E₀}σ_e)`,
where `H` is the (full) Hamiltonian and `Cov_s` the scaled covariance. The second
term is localized to the cut set `E₀` (`Cov_0` of the `E₀`-bond energy — a per-edge
truncated-correlation sum via `scaledCovariance_sum_right`); the first is the
full-vs-bond-deleted (`s=1` vs `s=0`) coupling difference of the *same* energy
covariance. Obtained from `hasDerivAt_scaledCorrelation_increment_beta` by folding
into covariance form, the endpoint β-log-derivatives (`betaLogDeriv_one`,
`betaLogDeriv_zero`) and the covariance second-observable linearity. The structural
form on which the capstone's `hincr` bound is built. -/
theorem hasDerivAt_scaledCorrelation_increment_beta_decomposed (G : SimpleGraph ι)
    [Fintype G.edgeSet] (E₀ : Finset (Sym2 ι)) (J β : ℝ) (A : Finset ι) :
    HasDerivAt (fun β' => scaledCorrelation G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) 1 A
        - scaledCorrelation G E₀ (⟨J, 0, β'⟩ : IsingParams ℝ) 0 A)
      ((scaledCovariance G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 0 (spinProduct A)
            (fun σ => hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ) -
          scaledCovariance G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 1 (spinProduct A)
            (fun σ => hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ)) +
        J * scaledCovariance G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 0 (spinProduct A)
          (fun σ => ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e)) β := by
  convert hasDerivAt_scaledCorrelation_increment_beta G E₀ J β A using 1
  change _ = scaledCovariance G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 1 (spinProduct A)
        (betaLogDeriv G E₀ J 1 β) -
      scaledCovariance G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 0 (spinProduct A)
        (betaLogDeriv G E₀ J 0 β)
  rw [betaLogDeriv_one, betaLogDeriv_zero,
    show (fun σ => - hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
          - J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e))
        = (fun σ => (- hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ)
          - (fun σ' => J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ' e)) σ) from rfl,
    scaledCovariance_sub_right, scaledCovariance_neg_right, scaledCovariance_neg_right,
    scaledCovariance_const_mul_right]
  ring

/-- **The `s=0` scaled covariance is the bond-deleted covariance** (Issue #2965,
Phase C): since `scaledGibbsExpectation … 0 = gibbsExpectation (G.deleteEdges E₀)`
(`scaledGibbsExpectation_zero`), `Cov_0(F,K)` equals the truncated correlation
`⟨F·K⟩_{bd} − ⟨F⟩_{bd}⟨K⟩_{bd}` of the bond-deleted graph `G.deleteEdges ↑E₀`. This
moves the localized shell term `J·∑_{e∈E₀} Cov_0(σ^A, σ_e)` of the β-derivative
increment onto the standard (bond-deleted) correlation machinery, where the
Lebowitz / spatial-decay (Part B) bounds apply. -/
theorem scaledCovariance_zero_eq_bondDeleted (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset) (p : IsingParams ℝ)
    (F K : Config ι → ℝ) [Fintype (G.deleteEdges ↑E₀).edgeSet] :
    scaledCovariance G E₀ p 0 F K
      = gibbsExpectation (G.deleteEdges ↑E₀) p (fun σ => F σ * K σ)
        - gibbsExpectation (G.deleteEdges ↑E₀) p F * gibbsExpectation (G.deleteEdges ↑E₀) p K := by
  unfold scaledCovariance
  rw [scaledGibbsExpectation_zero G E₀ hE₀_sub, scaledGibbsExpectation_zero G E₀ hE₀_sub,
    scaledGibbsExpectation_zero G E₀ hE₀_sub]

/-- **Per-edge shell covariance equals the bond-deleted Ursell function** (Issue
#2965, Phase C): for a non-degenerate edge `s(u,v)` (`u ≠ v`), the `s=0` covariance
of `σ^A` with the edge spin is the truncated two-point/Ursell function of the
bond-deleted graph:
`Cov_0(σ^A, σ_uσ_v) = ⟨σ^{A △ {u,v}}⟩_{bd} − ⟨σ^A⟩_{bd}·⟨σ_uσ_v⟩_{bd}`.
Composes `scaledCovariance_zero_eq_bondDeleted` (#3017), `edgeSpin = spinProduct`,
`spinProduct_mul` (`σ^A·σ_{u,v} = σ^{A△{u,v}}`), and `correlation =
gibbsExpectation ∘ spinProduct`. This puts each summand of the localized shell term
`J·∑_{e∈E₀} Cov_0(σ^A, σ_e)` into the standard truncated-correlation form, where the
Lebowitz cross bound (`summand_le_lebowitz_of_disjoint`) and the Part-B spatial
decay apply on the bond-deleted graph. -/
theorem scaledCovariance_zero_edgeSpin_eq_bondDeleted_ursell (G : SimpleGraph ι)
    [Fintype G.edgeSet] (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (A : Finset ι) {u v : ι} (huv : u ≠ v)
    [Fintype (G.deleteEdges ↑E₀).edgeSet] :
    scaledCovariance G E₀ p 0 (spinProduct A)
        (fun σ => edgeSpin (K := ℝ) σ (Quot.mk _ (u, v)))
      = correlation (G.deleteEdges ↑E₀) p (symmDiff A {u, v})
        - correlation (G.deleteEdges ↑E₀) p A * correlation (G.deleteEdges ↑E₀) p {u, v} := by
  rw [scaledCovariance_zero_eq_bondDeleted G E₀ hE₀_sub]
  have hfk : (fun σ => spinProduct A σ * edgeSpin (K := ℝ) σ (Quot.mk _ (u, v)))
      = spinProduct (symmDiff A {u, v}) := by
    funext σ
    rw [edgeSpin_quot_eq_spinProduct huv, spinProduct_mul]
  have hk : (fun σ => edgeSpin (K := ℝ) σ (Quot.mk _ (u, v))) = spinProduct {u, v} := by
    funext σ; rw [edgeSpin_quot_eq_spinProduct huv]
  rw [hfk, hk]
  rfl

/-- **Per-edge shell covariance bounded by the bond-deleted Lebowitz cross**
(Issue #2965, Phase C): for a ferromagnetic zero-field model and four distinct
sites `x, z, u, v`, the `s=0` covariance of `σ^{x,z}` with the edge spin `σ_uσ_v` is
bounded by the bond-deleted Lebowitz cross product
`⟨σ_xσ_u⟩_{bd}⟨σ_zσ_v⟩_{bd} + ⟨σ_xσ_v⟩_{bd}⟨σ_zσ_u⟩_{bd}`. Composes
`scaledCovariance_zero_edgeSpin_eq_bondDeleted_ursell` (the covariance is the
bond-deleted Ursell function) with `summand_le_lebowitz_of_disjoint` on the
bond-deleted graph (Lebowitz / `cor_4_3_3`). For a cut edge `{u,v}` far from
`{x,z}`, the cross product decays (Part-B spatial decay on the bond-deleted graph),
so the localized shell term of the β-derivative increment is geometric. -/
theorem scaledCovariance_zero_edgeSpin_le_lebowitz (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (x z : ι) {u v : ι} (hxz : x ≠ z) (hxu : x ≠ u) (hxv : x ≠ v) (hzu : z ≠ u)
    (hzv : z ≠ v) (huv : u ≠ v) [Fintype (G.deleteEdges ↑E₀).edgeSet] :
    scaledCovariance G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 0 (spinProduct {x, z})
        (fun σ => edgeSpin (K := ℝ) σ (Quot.mk _ (u, v)))
      ≤ correlation (G.deleteEdges ↑E₀) (⟨J, 0, β⟩ : IsingParams ℝ) {x, u} *
            correlation (G.deleteEdges ↑E₀) (⟨J, 0, β⟩ : IsingParams ℝ) {z, v} +
          correlation (G.deleteEdges ↑E₀) (⟨J, 0, β⟩ : IsingParams ℝ) {x, v} *
            correlation (G.deleteEdges ↑E₀) (⟨J, 0, β⟩ : IsingParams ℝ) {z, u} := by
  rw [scaledCovariance_zero_edgeSpin_eq_bondDeleted_ursell G E₀ hE₀_sub _ {x, z} huv]
  exact summand_le_lebowitz_of_disjoint (G.deleteEdges ↑E₀) J β
    ⟨hJ, le_refl 0, hβ⟩ x z u v hxz hxu hxv hzu hzv huv

/-- **Per-edge shell covariance bounded by the full-graph Lebowitz cross**
(Issue #2965, Phase C): strengthening `scaledCovariance_zero_edgeSpin_le_lebowitz`
by GKS bond-monotonicity (`correlation_deleteEdges_le`: bond-deleted ≤ full
correlation), the `s=0` covariance is bounded by the **full-graph** Lebowitz cross
`⟨σ_xσ_u⟩_G⟨σ_zσ_v⟩_G + ⟨σ_xσ_v⟩_G⟨σ_zσ_u⟩_G`. This puts each summand of the
localized shell term of the β-derivative increment in terms of the full-graph
two-point functions. This can later be combined, in the high-temperature cubic
shell setting (contraction factor `cf < 1`, fresh-shell geometry), with the
infinite-volume correlation decay to make the localized shell term geometric,
reusing the correlation-side Part-B machinery. -/
theorem scaledCovariance_zero_edgeSpin_le_lebowitz_full (G : SimpleGraph ι)
    [Fintype G.edgeSet] (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬ e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (x z : ι) {u v : ι} (hxz : x ≠ z) (hxu : x ≠ u) (hxv : x ≠ v) (hzu : z ≠ u)
    (hzv : z ≠ v) (huv : u ≠ v) :
    scaledCovariance G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 0 (spinProduct {x, z})
        (fun σ => edgeSpin (K := ℝ) σ (Quot.mk _ (u, v)))
      ≤ correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {x, u} *
            correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {z, v} +
          correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {x, v} *
            correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {z, u} := by
  haveI : Fintype (G.deleteEdges ↑E₀).edgeSet :=
    ((Set.toFinite G.edgeSet).subset
      (SimpleGraph.edgeSet_subset_edgeSet.mpr (G.deleteEdges_le _))).fintype
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  refine (scaledCovariance_zero_edgeSpin_le_lebowitz G E₀ hE₀_sub J β hJ hβ x z
    hxz hxu hxv hzu hzv huv).trans ?_
  have hbd : ∀ A, correlation (G.deleteEdges ↑E₀) (⟨J, 0, β⟩ : IsingParams ℝ) A
      ≤ correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A :=
    fun A => correlation_deleteEdges_le G E₀ hE₀_nd hE₀_sub _ hf A
  exact add_le_add
    (mul_le_mul (hbd {x, u}) (hbd {z, v}) (gks_first _ _ hf _) (gks_first _ _ hf _))
    (mul_le_mul (hbd {x, v}) (hbd {z, u}) (gks_first _ _ hf _) (gks_first _ _ hf _))

/-- **Energy covariance as a per-edge covariance sum** (Issue #2965, Phase C, `h=0`).
For zero external field the Hamiltonian is the pure interaction energy
`H = −J·∑_{e∈edges} σ_e`, so the scaled covariance of `σ^A` with `H` decomposes into
the per-edge covariance sum
`Cov_s(σ^A, H) = −J·∑_{e∈edges} Cov_s(σ^A, σ_e)`. Pure linearity
(`scaledCovariance_const_mul_right`, `scaledCovariance_sum_right`). This is the
structural input for the coupling-difference term `[Cov_0 − Cov_1](σ^A, H)` of the
β-derivative increment decomposition: it rewrites that hard core as a sum over all
edges of per-edge covariance differences `Cov_0(σ^A,σ_e) − Cov_1(σ^A,σ_e)`. In the
intended cut-set application the bulk contributions are expected to cancel between
`s=0` and `s=1` (a later quantitative step, not established by this lemma). -/
theorem scaledCovariance_spinProduct_hamiltonian_eq_neg_J_edge_sum (G : SimpleGraph ι)
    [Fintype G.edgeSet] (E₀ : Finset (Sym2 ι)) (J β : ℝ) (s : ℝ) (A : Finset ι) :
    scaledCovariance G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s (spinProduct A)
        (hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ))
      = -J * ∑ e ∈ G.edgeFinset,
          scaledCovariance G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) s (spinProduct A)
            (fun σ => edgeSpin (K := ℝ) σ e) := by
  have hH : hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ)
      = fun σ => -J * ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e := by
    funext σ
    simp [hamiltonian, interactionEnergy, externalFieldEnergy]
  rw [hH, scaledCovariance_const_mul_right, scaledCovariance_sum_right]

/-- **Per-edge covariance as a scaled-correlation truncated function** (Issue #2965,
Phase C). For a non-degenerate edge `s(u,v)` (`u ≠ v`), the scaled covariance of
`σ^A` with the edge spin `σ_uσ_v` is the truncated two-point function in scaled
correlations:
`Cov_s(σ^A, σ_uσ_v) = ⟨σ^{A△{u,v}}⟩_s − ⟨σ^A⟩_s·⟨σ_uσ_v⟩_s`.
Uses `edgeSpin = spinProduct {u,v}` (`edgeSpin_quot_eq_spinProduct`) and the spin
product fusion `spinProduct_mul` (`σ^A·σ^{u,v} = σ^{A△{u,v}}`). This expresses every
per-edge summand of the coupling-difference sum
(`scaledCovariance_coupling_difference_eq_neg_J_edge_sum`) purely in terms of scaled
correlations, connecting the hard core to the bond-adding correlation increments
whose decay is established by the Part-A/B machinery. -/
theorem scaledCovariance_spinProduct_edgeSpin_eq_scaledCorrelation (G : SimpleGraph ι)
    [Fintype G.edgeSet] (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (A : Finset ι)
    {u v : ι} (huv : u ≠ v) :
    scaledCovariance G E₀ p s (spinProduct A)
        (fun σ => edgeSpin (K := ℝ) σ (Quot.mk _ (u, v)))
      = scaledCorrelation G E₀ p s (symmDiff A {u, v})
        - scaledCorrelation G E₀ p s A * scaledCorrelation G E₀ p s {u, v} := by
  unfold scaledCovariance scaledCorrelation
  have hfk : (fun σ => spinProduct A σ * edgeSpin (K := ℝ) σ (Quot.mk _ (u, v)))
      = spinProduct (symmDiff A {u, v}) := by
    funext σ
    rw [edgeSpin_quot_eq_spinProduct huv, spinProduct_mul]
  have hk : (fun σ => edgeSpin (K := ℝ) σ (Quot.mk _ (u, v))) = spinProduct {u, v} := by
    funext σ; rw [edgeSpin_quot_eq_spinProduct huv]
  rw [hfk, hk]

/-- **Per-edge coupling-difference summand in scaled correlations** (Issue #2965,
Phase C). Each summand of the coupling-difference sum, the `s=0` vs `s=1` covariance
difference of `σ^A` with an edge spin `σ_uσ_v`, is the difference of two
scaled-correlation truncated functions:
`Cov_0(σ^A,σ_uσ_v) − Cov_1(σ^A,σ_uσ_v) =
  [⟨σ^{A△{u,v}}⟩_0 − ⟨σ^A⟩_0⟨σ_uσ_v⟩_0] − [⟨σ^{A△{u,v}}⟩_1 − ⟨σ^A⟩_1⟨σ_uσ_v⟩_1]`.
Substitutes `scaledCovariance_spinProduct_edgeSpin_eq_scaledCorrelation` at the two
endpoints `s=0,1`. The scaled correlations `⟨·⟩_1` (full) and `⟨·⟩_0` (bond-deleted)
differ by the bond-adding increment over the cut set, so this rewrites each
coupling-difference summand in terms of correlation increments — the objects whose
geometric decay is established by the Part-A/B per-stage increment machinery. -/
theorem scaledCovariance_edgeSpin_zero_sub_one_eq_scaledCorrelation (G : SimpleGraph ι)
    [Fintype G.edgeSet] (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (A : Finset ι)
    {u v : ι} (huv : u ≠ v) :
    scaledCovariance G E₀ p 0 (spinProduct A)
          (fun σ => edgeSpin (K := ℝ) σ (Quot.mk _ (u, v))) -
        scaledCovariance G E₀ p 1 (spinProduct A)
          (fun σ => edgeSpin (K := ℝ) σ (Quot.mk _ (u, v)))
      = (scaledCorrelation G E₀ p 0 (symmDiff A {u, v})
            - scaledCorrelation G E₀ p 0 A * scaledCorrelation G E₀ p 0 {u, v})
        - (scaledCorrelation G E₀ p 1 (symmDiff A {u, v})
            - scaledCorrelation G E₀ p 1 A * scaledCorrelation G E₀ p 1 {u, v}) := by
  rw [scaledCovariance_spinProduct_edgeSpin_eq_scaledCorrelation G E₀ p 0 A huv,
    scaledCovariance_spinProduct_edgeSpin_eq_scaledCorrelation G E₀ p 1 A huv]

/-- **Coupling difference as a per-edge covariance-difference sum** (Issue #2965,
Phase C, `h=0`). The hard core of the β-derivative increment decomposition,
`[Cov_0(σ^A, H) − Cov_1(σ^A, H)]`, equals
`−J·∑_{e∈edges} [Cov_0(σ^A,σ_e) − Cov_1(σ^A,σ_e)]`. Subtracting the per-edge sum
representation `scaledCovariance_spinProduct_hamiltonian_eq_neg_J_edge_sum` at the two
endpoints `s=0` and `s=1` (in the intended bond-deletion application, `s=0` is the
bond-deleted graph and `s=1` the full graph). In that application the bulk edges (far
from the cut shell) are expected to cancel between `s=0` and `s=1`, leaving a
shell-localized contribution — the remaining quantitative input (not established here)
toward the geometric per-stage β-derivative increment. -/
theorem scaledCovariance_coupling_difference_eq_neg_J_edge_sum (G : SimpleGraph ι)
    [Fintype G.edgeSet] (E₀ : Finset (Sym2 ι)) (J β : ℝ) (A : Finset ι) :
    scaledCovariance G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 0 (spinProduct A)
          (hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ)) -
        scaledCovariance G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 1 (spinProduct A)
          (hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ))
      = -J * ∑ e ∈ G.edgeFinset,
          (scaledCovariance G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 0 (spinProduct A)
              (fun σ => edgeSpin (K := ℝ) σ e) -
            scaledCovariance G E₀ (⟨J, 0, β⟩ : IsingParams ℝ) 1 (spinProduct A)
              (fun σ => edgeSpin (K := ℝ) σ e)) := by
  rw [scaledCovariance_spinProduct_hamiltonian_eq_neg_J_edge_sum,
    scaledCovariance_spinProduct_hamiltonian_eq_neg_J_edge_sum,
    Finset.sum_sub_distrib, mul_sub]

end IsingModel
