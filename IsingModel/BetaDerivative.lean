import IsingModel.GibbsMeasure
import IsingModel.Inequalities.NonnegCorrelations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# β-Derivative of Ising Gibbs correlations (GJ §17.5 Step 117a)

Differentiability of finite-volume Ising correlations in the inverse
temperature `β`, with the explicit derivative formula.

## Main results

* `hasDerivAt_boltzmannWeight_beta` — `d/dβ exp(-β·H(σ)) = -H(σ)·exp(-β·H(σ))`
* `hasDerivAt_partitionFunction_beta` — `d/dβ Z(β) = Σ_σ -H(σ)·bw(σ)`
* `hasDerivAt_correlation_beta` — derivative formula
  `d/dβ ⟨σ^A⟩_β = J·Σ_{e∈E} [⟨σ^{A△{e₁,e₂}}⟩ − ⟨σ^A⟩·⟨σ_{e₁e₂}⟩]`

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5 pp. 310–312, Springer 1987.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Hamiltonian is independent of β -/

omit [DecidableEq ι] in
/-- The Ising Hamiltonian uses only `p.J` and `p.h`, not `p.β`. -/
private lemma hamiltonian_eq_of_same_JH
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β β' : ℝ) (σ : Config ι) :
    hamiltonian G (⟨J, h, β'⟩ : IsingParams ℝ) σ =
    hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) σ := rfl

/-! ## Derivative of the Boltzmann weight -/

omit [DecidableEq ι] in
/-- **Boltzmann weight is differentiable in β**:
`d/dβ exp(-β · H(σ)) = −H(σ) · exp(-β · H(σ))`.

Reference: standard computation; used implicitly in GJ §17.5. -/
theorem hasDerivAt_boltzmannWeight_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (σ : Config ι) :
    HasDerivAt (fun β' => boltzmannWeight G (⟨J, h, β'⟩ : IsingParams ℝ) σ)
      (- hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) σ *
         boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ) β := by
  set H := hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) σ
  have hbw : ∀ β' : ℝ,
      boltzmannWeight G (⟨J, h, β'⟩ : IsingParams ℝ) σ = Real.exp (-β' * H) := fun β' => by
    simp only [boltzmannWeight]
    rw [show hamiltonian G (⟨J, h, β'⟩ : IsingParams ℝ) σ = H from
        hamiltonian_eq_of_same_JH G J h β β' σ]
  simp_rw [hbw]
  have h1 : HasDerivAt (fun β' : ℝ => -β' * H) (-H) β := by
    have h := ((hasDerivAt_id β).neg).mul_const H
    simp only [Function.id_def, neg_one_mul] at h
    exact h
  have h2 := (Real.hasDerivAt_exp (-β * H)).comp β h1
  -- h2 : HasDerivAt (Real.exp ∘ fun β' => -β' * H) (Real.exp (-β * H) * -H) β
  have hfun : (Real.exp ∘ fun β' => -β' * H) = fun β' => Real.exp (-β' * H) := rfl
  rw [hfun] at h2
  convert h2 using 1
  ring

/-! ## Derivative of the partition function -/

/-- **Partition function is differentiable in β**:
`d/dβ Z(β) = Σ_σ (−H(σ)) · bw(σ)`.

Reference: standard computation; used implicitly in GJ §17.5. -/
theorem hasDerivAt_partitionFunction_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun β' => partitionFunction G (⟨J, h, β'⟩ : IsingParams ℝ))
      (∑ σ : Config ι,
        - hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) σ *
          boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ) β := by
  simp only [partitionFunction]
  exact HasDerivAt.fun_sum (fun σ _ => hasDerivAt_boltzmannWeight_beta G J h β σ)

/-! ## Derivative of weighted Boltzmann sums -/

/-- Weighted Boltzmann sum is differentiable in β. -/
private theorem hasDerivAt_weightedBoltzmannSum_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (F : Config ι → ℝ) :
    HasDerivAt
      (fun β' => ∑ σ : Config ι,
        F σ * boltzmannWeight G (⟨J, h, β'⟩ : IsingParams ℝ) σ)
      (∑ σ : Config ι,
        F σ * (- hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) σ *
               boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ)) β := by
  apply HasDerivAt.fun_sum
  intro σ _
  exact (hasDerivAt_boltzmannWeight_beta G J h β σ).const_mul (F σ)

/-! ## Derivative of the Gibbs expectation -/

/-- **Gibbs expectation is differentiable in β**:
`d/dβ ⟨F⟩_β = ⟨F·(−H)⟩_β − ⟨F⟩_β · ⟨−H⟩_β`.

Reference: standard computation; used implicitly in GJ §17.5. -/
private theorem hasDerivAt_gibbsExpectation_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (F : Config ι → ℝ) :
    HasDerivAt
      (fun β' => gibbsExpectation G (⟨J, h, β'⟩ : IsingParams ℝ) F)
      (gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ)
            (fun σ => F σ * (- hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) σ)) -
       gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) F *
       gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ)
            (fun σ => - hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) σ))
      β := by
  set p := (⟨J, h, β⟩ : IsingParams ℝ)
  have hZpos : 0 < partitionFunction G p := partitionFunction_pos G p
  have hZne : partitionFunction G p ≠ 0 := hZpos.ne'
  -- Unfold gibbsExpectation to Z⁻¹ * Σ F bw form
  have hge_eq : ∀ β',
      gibbsExpectation G (⟨J, h, β'⟩ : IsingParams ℝ) F =
      (partitionFunction G (⟨J, h, β'⟩ : IsingParams ℝ))⁻¹ *
      ∑ σ : Config ι, F σ * boltzmannWeight G (⟨J, h, β'⟩ : IsingParams ℝ) σ :=
    fun _ => rfl
  simp_rw [hge_eq]
  have hZderiv := hasDerivAt_partitionFunction_beta G J h β
  have hZinv : HasDerivAt (fun β' =>
      (partitionFunction G (⟨J, h, β'⟩ : IsingParams ℝ))⁻¹)
      (- (∑ σ, - hamiltonian G p σ * boltzmannWeight G p σ) / (partitionFunction G p) ^ 2) β :=
    (show (⟨J, h, β⟩ : IsingParams ℝ) = p from rfl) ▸ hZderiv.inv hZne
  have hnum := hasDerivAt_weightedBoltzmannSum_beta G J h β F
  have hprod := hZinv.mul hnum
  -- hprod : HasDerivAt (Z⁻¹ * Σ F bw) (-dZ/Z²*S + Z⁻¹*dS) β
  -- Goal:   HasDerivAt (Z⁻¹ * Σ F bw) (Z⁻¹*dS' - Z⁻¹*S*(Z⁻¹*dZ)) β
  -- where dS' = Σ F*(-H*bw), dZ = Σ (-H)*bw, S = Σ F*bw
  -- These derivative values are equal by field arithmetic.
  convert hprod using 1
  simp only [gibbsExpectation, p]
  -- Now: goal is an equality of real numbers
  -- LHS: Z⁻¹ * Σ F*(-H)*bw - Z⁻¹ * S * (Z⁻¹ * dZ)  where associativity may differ
  -- RHS: -dZ/Z² * S + Z⁻¹ * dS  where dS = Σ F*(-H*bw)
  -- Key: Σ F x * (-H x) * bw x = Σ F x * (-H x * bw x) = dS by ring
  set Z := partitionFunction G (⟨J, h, β⟩ : IsingParams ℝ)
  have hZne' : Z ≠ 0 := hZne
  have hdS_congr : ∑ x : Config ι, F x *
      (- hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) x *
       boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) x) =
      ∑ x : Config ι, F x * (- hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) x) *
      boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) x := by
    apply Finset.sum_congr rfl; intro σ _; ring
  rw [← hdS_congr]
  field_simp [hZne']
  ring

/-! ## Helper: edgeSpin and spinProduct -/

omit [Fintype ι] in
/-- `edgeSpin σ ⟦(i,j)⟧ = spinProduct {i,j} σ` for distinct `i ≠ j`. -/
private lemma edgeSpin_quot_eq_spinProduct
    {i j : ι} (hij : i ≠ j) (σ : Config ι) :
    edgeSpin (K := ℝ) σ (Quot.mk _ (i, j) : Sym2 ι) = spinProduct {i, j} σ := by
  simp [edgeSpin, spinProduct, Finset.prod_pair hij, Spin.sign]

omit [DecidableEq ι] in
/-- The negative Hamiltonian at `h = 0` equals `J` times the sum of edge spins. -/
private lemma neg_hamiltonian_h_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (σ : Config ι) :
    - hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ =
      J * ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e := by
  unfold hamiltonian interactionEnergy externalFieldEnergy
  ring

/-! ## Main derivative formula -/

/-- **Derivative formula for Ising correlations** (GJ §17.5):
The finite-volume correlation `⟨σ^A⟩_β` at `h = 0` is differentiable
in `β`, with derivative

  `d/dβ ⟨σ^A⟩_β = J · Σ_{e∈E} [⟨σ^{A△{e₁,e₂}}⟩_β − ⟨σ^A⟩_β · ⟨σ_{e₁e₂}⟩_β]`.

Proof: quotient rule `d/dβ ⟨F⟩ = ⟨F·(-H)⟩ - ⟨F⟩⟨-H⟩`, then expand
`−H = J·Σ_e σ^{e₁e₂}` and use `spinProduct_mul`.

Reference: Glimm–Jaffe §17.5 pp. 310–311 (implicit in the proof). -/
theorem hasDerivAt_correlation_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) :
    HasDerivAt (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) A)
      (J * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v =>
          correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff A {u, v}) -
          correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A *
          correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e)
      β := by
  unfold correlation
  have hderiv := hasDerivAt_gibbsExpectation_beta G J 0 β (spinProduct A)
  set p := (⟨J, 0, β⟩ : IsingParams ℝ)
  -- Helper: -H(σ) = J * Σ_e edgeSpin σ e (using set variable p)
  have hneg_H : ∀ σ : Config ι, - hamiltonian G p σ =
      J * ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e :=
    fun σ => neg_hamiltonian_h_zero G J β σ
  -- Rewrite ⟨spinProduct A · (-H)⟩ = J · Σ_e ⟨spinProduct (A△{e₁,e₂})⟩
  have hFH : gibbsExpectation G p
      (fun σ => spinProduct A σ * (- hamiltonian G p σ)) =
      J * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => gibbsExpectation G p (spinProduct (symmDiff A {u, v})),
          fun u v => by simp [Finset.pair_comm v u]⟩ e := by
    unfold gibbsExpectation
    -- Inner sum: Σ_σ spinProduct A σ * (-H σ) * bw σ
    --          = Σ_σ spinProduct A σ * (J * Σ_e edgeSpin σ e) * bw σ
    --          = J * Σ_e Σ_σ spinProduct A σ * edgeSpin σ e * bw σ
    --          = J * Σ_e Σ_σ spinProduct (A△{u,v}) σ * bw σ   (by spinProduct_mul)
    have hinner : ∑ σ : Config ι, spinProduct A σ * (- hamiltonian G p σ) *
        boltzmannWeight G p σ =
        J * ∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v => ∑ σ : Config ι,
              spinProduct (symmDiff A {u, v}) σ * boltzmannWeight G p σ,
            fun u v => by simp [Finset.pair_comm v u]⟩ e := by
      -- Substitute -H(σ) = J * Σ_e edgeSpin σ e
      simp_rw [hneg_H]
      -- spinProduct A σ * (J * Σ_e edgeSpin σ e) * bw σ
      --   = Σ_e (spinProduct A σ * (J * edgeSpin σ e) * bw σ)
      simp_rw [Finset.mul_sum]
      -- Now outer sum: Σ_σ (Σ_e spinProduct A σ * (J * edgeSpin σ e)) * bw σ
      -- Distribute bw over inner sum: Σ_σ Σ_e (spinProduct A σ * (J * edgeSpin σ e) * bw σ)
      simp_rw [Finset.sum_mul]
      -- Swap sums: Σ_e Σ_σ (spinProduct A σ * (J * edgeSpin σ e) * bw σ)
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
      have huv : u ≠ v := by
        intro heq; subst heq
        exact (SimpleGraph.mem_edgeFinset.mp he).ne rfl
      simp only [Sym2.lift_mk]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [edgeSpin_quot_eq_spinProduct huv, ← spinProduct_mul]
      ring
    -- Now: Z⁻¹ * (J * Σ_e X_e) = J * Σ_e (Z⁻¹ * X_e)
    rw [hinner]
    rw [← mul_assoc, mul_comm (partitionFunction G p)⁻¹ J, mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
  -- Rewrite ⟨-H⟩ = J · Σ_e ⟨spinProduct {e₁,e₂}⟩
  have hnH : gibbsExpectation G p (fun σ => - hamiltonian G p σ) =
      J * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => gibbsExpectation G p (spinProduct {u, v}),
          fun u v => by simp [Finset.pair_comm v u]⟩ e := by
    unfold gibbsExpectation
    have hinner : ∑ σ : Config ι, (- hamiltonian G p σ) * boltzmannWeight G p σ =
        J * ∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v => ∑ σ : Config ι,
              spinProduct {u, v} σ * boltzmannWeight G p σ,
            fun u v => by simp [Finset.pair_comm v u]⟩ e := by
      simp_rw [hneg_H]
      -- (J * Σ_e edgeSpin σ e) * bw σ = Σ_e (J * edgeSpin σ e * bw σ)
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
      have huv : u ≠ v := by
        intro heq; subst heq
        exact (SimpleGraph.mem_edgeFinset.mp he).ne rfl
      simp only [Sym2.lift_mk]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [edgeSpin_quot_eq_spinProduct huv]
      ring
    rw [hinner, ← mul_assoc, mul_comm (partitionFunction G p)⁻¹ J, mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
  rw [hFH, hnH] at hderiv
  -- hderiv : HasDerivAt ... (J*Σ A△_e - ge(A)*(J*Σ {u,v}_e)) β
  -- goal   : HasDerivAt ... (J*Σ (A△_e - ge(A)*{u,v}_e)) β
  -- Show these derivative values are equal:
  have hval : J * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v =>
          gibbsExpectation G p (spinProduct (symmDiff A {u, v})) -
          gibbsExpectation G p (spinProduct A) *
          gibbsExpectation G p (spinProduct {u, v}),
          fun u v => by simp [Finset.pair_comm v u]⟩ e =
      J * ∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v => gibbsExpectation G p (spinProduct (symmDiff A {u, v})),
            fun u v => by simp [Finset.pair_comm v u]⟩ e -
      gibbsExpectation G p (spinProduct A) *
        (J * ∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v => gibbsExpectation G p (spinProduct {u, v}),
            fun u v => by simp [Finset.pair_comm v u]⟩ e) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
    ring
  rw [hval]
  exact hderiv

end IsingModel
