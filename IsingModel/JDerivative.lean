import IsingModel.GibbsMeasure
import IsingModel.Inequalities.NonnegCorrelations
import IsingModel.Inequalities.GKS
import IsingModel.Inequalities.GHS
import IsingModel.BetaDerivative
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# J-Derivative of Ising Gibbs correlations (GJ §17.5 Step 214)

Differentiability of finite-volume Ising correlations in the coupling
constant `J`, with the explicit derivative formula.

Unlike the β derivative, the J derivative formula holds at general `h`
(not restricted to `h = 0`), since the magnetic-field term in the
Hamiltonian is independent of `J`.

## Main results

* `hasDerivAt_boltzmannWeight_J` — `d/dJ exp(-β·H(J,h)) = β·Σ_e edgeSpin · exp(-β·H(J,h))`
* `hasDerivAt_partitionFunction_J` — `d/dJ Z(J) = Σ_σ β·Σ_e edgeSpin σ e · bw(σ)`
* `hasDerivAt_correlation_J` — derivative formula
  `d/dJ ⟨σ^A⟩_J = β·Σ_{e∈E} [⟨σ^{A△{e₁,e₂}}⟩ − ⟨σ^A⟩·⟨σ_{e₁e₂}⟩]`

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5 pp. 310–312, Springer 1987.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Splitting the Boltzmann exponent into J-dependent and J-independent parts -/

omit [DecidableEq ι] in
/-- The Boltzmann exponent `−β·H(J, h)` splits as
`β·J·Σ_e edgeSpin σ e + (−β·externalFieldEnergy h σ)`,
where the second summand is independent of `J`. -/
private lemma neg_betaH_split_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (σ : Config ι) :
    -β * hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) σ =
      β * J * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e)
        + (-β * externalFieldEnergy h σ) := by
  unfold hamiltonian interactionEnergy
  ring

/-! ## Derivative of the Boltzmann weight in J -/

omit [DecidableEq ι] in
/-- **Boltzmann weight is differentiable in J**:
`d/dJ exp(-β · H(J, h; σ)) = β · Σ_e edgeSpin σ e · exp(-β · H(J, h; σ))`.

Reference: standard computation; used implicitly in GJ §17.5. -/
theorem hasDerivAt_boltzmannWeight_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (σ : Config ι) :
    HasDerivAt (fun J' => boltzmannWeight G (⟨J', h, β⟩ : IsingParams ℝ) σ)
      (β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e) *
         boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ) J := by
  set S := (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e) with hS
  set C := -β * externalFieldEnergy h σ with hC
  -- Rewrite bw(J') = exp(β·J'·S + C)
  have hbw : ∀ J' : ℝ,
      boltzmannWeight G (⟨J', h, β⟩ : IsingParams ℝ) σ
        = Real.exp (β * J' * S + C) := fun J' => by
    simp only [boltzmannWeight, hS, hC]
    rw [neg_betaH_split_J G J' h β σ]
  simp_rw [hbw]
  -- d/dJ' (β·J'·S + C) = β·S
  have h1 : HasDerivAt (fun J' : ℝ => β * J' * S + C) (β * S) J := by
    have h_lin : HasDerivAt (fun J' : ℝ => β * J' * S) (β * S) J := by
      have h := ((hasDerivAt_id J).const_mul β).mul_const S
      simpa using h
    simpa using h_lin.add_const C
  have h2 := (Real.hasDerivAt_exp (β * J * S + C)).comp J h1
  -- h2 : HasDerivAt (Real.exp ∘ fun J' => β·J'·S + C) (Real.exp(β·J·S + C) * (β·S)) J
  have hfun : (Real.exp ∘ fun J' => β * J' * S + C)
              = fun J' => Real.exp (β * J' * S + C) := rfl
  rw [hfun] at h2
  convert h2 using 1
  ring

/-! ## Derivative of the partition function in J -/

/-- **Partition function is differentiable in J**:
`d/dJ Z(J) = Σ_σ β·Σ_e edgeSpin σ e · bw(σ)`.

Reference: standard computation; used implicitly in GJ §17.5. -/
theorem hasDerivAt_partitionFunction_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun J' => partitionFunction G (⟨J', h, β⟩ : IsingParams ℝ))
      (∑ σ : Config ι,
        β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e) *
          boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ) J := by
  simp only [partitionFunction]
  exact HasDerivAt.fun_sum (fun σ _ => hasDerivAt_boltzmannWeight_J G J h β σ)

/-! ## Derivative of weighted Boltzmann sums in J -/

/-- Weighted Boltzmann sum is differentiable in J. -/
private theorem hasDerivAt_weightedBoltzmannSum_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (F : Config ι → ℝ) :
    HasDerivAt
      (fun J' => ∑ σ : Config ι,
        F σ * boltzmannWeight G (⟨J', h, β⟩ : IsingParams ℝ) σ)
      (∑ σ : Config ι,
        F σ * (β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e) *
               boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ)) J := by
  apply HasDerivAt.fun_sum
  intro σ _
  exact (hasDerivAt_boltzmannWeight_J G J h β σ).const_mul (F σ)

/-! ## Derivative of the Gibbs expectation in J -/

/-- **Gibbs expectation is differentiable in J**:
`d/dJ ⟨F⟩_J = ⟨F·X⟩_J − ⟨F⟩_J · ⟨X⟩_J`,
where `X(σ) = β · Σ_e edgeSpin σ e`.

Reference: standard computation; used implicitly in GJ §17.5. -/
private theorem hasDerivAt_gibbsExpectation_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (F : Config ι → ℝ) :
    HasDerivAt
      (fun J' => gibbsExpectation G (⟨J', h, β⟩ : IsingParams ℝ) F)
      (gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ)
            (fun σ => F σ * (β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e))) -
       gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) F *
       gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ)
            (fun σ => β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e)))
      J := by
  set p := (⟨J, h, β⟩ : IsingParams ℝ)
  have hZpos : 0 < partitionFunction G p := partitionFunction_pos G p
  have hZne : partitionFunction G p ≠ 0 := hZpos.ne'
  have hge_eq : ∀ J',
      gibbsExpectation G (⟨J', h, β⟩ : IsingParams ℝ) F =
      (partitionFunction G (⟨J', h, β⟩ : IsingParams ℝ))⁻¹ *
      ∑ σ : Config ι, F σ * boltzmannWeight G (⟨J', h, β⟩ : IsingParams ℝ) σ :=
    fun _ => rfl
  simp_rw [hge_eq]
  have hZderiv := hasDerivAt_partitionFunction_J G J h β
  have hZinv : HasDerivAt (fun J' =>
      (partitionFunction G (⟨J', h, β⟩ : IsingParams ℝ))⁻¹)
      (- (∑ σ, β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e) *
              boltzmannWeight G p σ) / (partitionFunction G p) ^ 2) J :=
    (show (⟨J, h, β⟩ : IsingParams ℝ) = p from rfl) ▸ hZderiv.inv hZne
  have hnum := hasDerivAt_weightedBoltzmannSum_J G J h β F
  have hprod := hZinv.mul hnum
  convert hprod using 1
  simp only [gibbsExpectation, p]
  set Z := partitionFunction G (⟨J, h, β⟩ : IsingParams ℝ)
  have hZne' : Z ≠ 0 := hZne
  have hdS_congr : ∑ x : Config ι, F x *
      (β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) x e) *
       boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) x) =
      ∑ x : Config ι, F x *
        (β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) x e)) *
      boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) x := by
    apply Finset.sum_congr rfl; intro σ _; ring
  rw [← hdS_congr]
  -- After field_simp the goal becomes a polynomial identity in Z,
  -- but the summands differ by associativity (F·β vs β·F inside the sum).
  -- We close it by congruence inside the sums.
  have hsum1 : ∀ σ : Config ι,
      F σ * (β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e) *
        boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ)
      = β * (F σ * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e) *
        boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ) := fun σ => by ring
  simp_rw [hsum1]
  rw [← Finset.mul_sum]
  field_simp [hZne']
  ring

/-! ## Helper: edgeSpin and spinProduct -/

omit [Fintype ι] in
/-- `edgeSpin σ ⟦(i,j)⟧ = spinProduct {i,j} σ` for distinct `i ≠ j`. -/
private lemma edgeSpin_quot_eq_spinProduct_J
    {i j : ι} (hij : i ≠ j) (σ : Config ι) :
    edgeSpin (K := ℝ) σ (Quot.mk _ (i, j) : Sym2 ι) = spinProduct {i, j} σ := by
  simp [edgeSpin, spinProduct, Finset.prod_pair hij, Spin.sign]

/-! ## Main derivative formula -/

/-- **Derivative formula for Ising correlations in J** (Step 214):
The finite-volume correlation `⟨σ^A⟩_J` is differentiable in `J`,
with derivative

  `d/dJ ⟨σ^A⟩_J = β · Σ_{e∈E} [⟨σ^{A△{e₁,e₂}}⟩_J − ⟨σ^A⟩_J · ⟨σ_{e₁e₂}⟩_J]`.

This formula holds at any `h ∈ ℝ`, since the magnetic-field term in the
Hamiltonian is independent of `J`.

Proof: quotient rule `d/dJ ⟨F⟩ = ⟨F·X⟩ − ⟨F⟩⟨X⟩` with
`X = β·Σ_e edgeSpin σ e`, then use `spinProduct_mul`.

Reference: parallel to the β-derivative formula in `hasDerivAt_correlation_beta`
(Glimm–Jaffe §17.5 pp. 310–311 in 1st ed.); the J-derivative is the natural
companion computation. Since `H = -J·Σ σσ - h·Σ σ` is multilinear in J·β at
h = 0, one has `J·∂_J⟨·⟩ = β·∂_β⟨·⟩` at h = 0 via scaling, but the J-derivative
extends to general h (whereas β-derivative requires h = 0). -/
theorem hasDerivAt_correlation_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (A : Finset ι) :
    HasDerivAt (fun J' => correlation G (⟨J', h, β⟩ : IsingParams ℝ) A)
      (β * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v =>
          correlation G (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff A {u, v}) -
          correlation G (⟨J, h, β⟩ : IsingParams ℝ) A *
          correlation G (⟨J, h, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e)
      J := by
  unfold correlation
  have hderiv := hasDerivAt_gibbsExpectation_J G J h β (spinProduct A)
  set p := (⟨J, h, β⟩ : IsingParams ℝ)
  -- Rewrite ⟨spinProduct A · X⟩ = β · Σ_e ⟨spinProduct (A△{e₁,e₂})⟩
  have hFX : gibbsExpectation G p
      (fun σ => spinProduct A σ *
        (β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e))) =
      β * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => gibbsExpectation G p (spinProduct (symmDiff A {u, v})),
          fun u v => by simp [Finset.pair_comm v u]⟩ e := by
    unfold gibbsExpectation
    have hinner : ∑ σ : Config ι, spinProduct A σ *
        (β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e)) *
        boltzmannWeight G p σ =
        β * ∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v => ∑ σ : Config ι,
              spinProduct (symmDiff A {u, v}) σ * boltzmannWeight G p σ,
            fun u v => by simp [Finset.pair_comm v u]⟩ e := by
      simp_rw [Finset.mul_sum]
      simp_rw [Finset.sum_mul]
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
      rw [edgeSpin_quot_eq_spinProduct_J huv, ← spinProduct_mul]
      ring
    rw [hinner]
    rw [← mul_assoc, mul_comm (partitionFunction G p)⁻¹ β, mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
  -- Rewrite ⟨X⟩ = β · Σ_e ⟨spinProduct {e₁,e₂}⟩
  have hX : gibbsExpectation G p
      (fun σ => β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e)) =
      β * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => gibbsExpectation G p (spinProduct {u, v}),
          fun u v => by simp [Finset.pair_comm v u]⟩ e := by
    unfold gibbsExpectation
    have hinner : ∑ σ : Config ι,
        (β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e)) *
          boltzmannWeight G p σ =
        β * ∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v => ∑ σ : Config ι,
              spinProduct {u, v} σ * boltzmannWeight G p σ,
            fun u v => by simp [Finset.pair_comm v u]⟩ e := by
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
      rw [edgeSpin_quot_eq_spinProduct_J huv]
      ring
    rw [hinner, ← mul_assoc, mul_comm (partitionFunction G p)⁻¹ β, mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
  rw [hFX, hX] at hderiv
  -- Combine into single derivative formula
  have hval : β * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v =>
          gibbsExpectation G p (spinProduct (symmDiff A {u, v})) -
          gibbsExpectation G p (spinProduct A) *
          gibbsExpectation G p (spinProduct {u, v}),
          fun u v => by simp [Finset.pair_comm v u]⟩ e =
      β * ∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v => gibbsExpectation G p (spinProduct (symmDiff A {u, v})),
            fun u v => by simp [Finset.pair_comm v u]⟩ e -
      gibbsExpectation G p (spinProduct A) *
        (β * ∑ e ∈ G.edgeFinset,
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

/-! ## Step 215: explicit J-derivatives for truncated2/magnetization/susceptibility -/

/-- **truncated2 has a J-derivative** (Step 215):
For any finite-volume Ising and any `(J, h, β)`, `truncated2 G ⟨J, h, β⟩ i j`
has a derivative in J. Holds at any `h` (parallels Step 191 in β direction).

Product rule applied to `truncated2 = correlation {i,j} - correlation {i} · correlation {j}`,
each factor differentiable via `hasDerivAt_correlation_J`. -/
theorem truncated2_hasDerivAt_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j : ι) :
    HasDerivAt (fun J' => truncated2 G (⟨J', h, β⟩ : IsingParams ℝ) i j)
      (deriv (fun J' => correlation G (⟨J', h, β⟩ : IsingParams ℝ) {i, j}) J -
       (deriv (fun J' => correlation G (⟨J', h, β⟩ : IsingParams ℝ) {i}) J *
        correlation G (⟨J, h, β⟩ : IsingParams ℝ) {j} +
        correlation G (⟨J, h, β⟩ : IsingParams ℝ) {i} *
        deriv (fun J' => correlation G (⟨J', h, β⟩ : IsingParams ℝ) {j}) J))
      J := by
  unfold truncated2
  have hij := hasDerivAt_correlation_J G J h β {i, j}
  have hi := hasDerivAt_correlation_J G J h β {i}
  have hj := hasDerivAt_correlation_J G J h β {j}
  have h_prod := hi.mul hj
  have h_diff := hij.sub h_prod
  rw [hij.deriv, hi.deriv, hj.deriv] at *
  exact h_diff

end IsingModel
