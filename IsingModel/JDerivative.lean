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

/-! ## Step 216: Lebowitz upper bound on the J-derivative at h = 0 -/

/-- **Lebowitz upper bound on J-derivative of 2-point function** (Step 216):
The derivative `d/dJ ⟨σ_r σ_s⟩` at `h = 0` satisfies

  `d/dJ ⟨σ_r σ_s⟩ ≤ β · Σ_{e∈E} [⟨σ_r σ_{e₁}⟩·⟨σ_s σ_{e₂}⟩ + ⟨σ_r σ_{e₂}⟩·⟨σ_s σ_{e₁}⟩]`
  `                  + β · |E(G)|`

Direct J-direction analogue of `correlation_beta_deriv_le_lebowitz` (Step 117b).
The proof mirrors the β version with prefactor `J → β`, using `hasDerivAt_correlation_J`
in place of `hasDerivAt_correlation_beta`.

Reference: parallel to Glimm–Jaffe §17.5 pp.311–312; Cor. 4.3.3 (Lebowitz). -/
theorem correlation_J_deriv_le_lebowitz
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (r s : ι) (hrs : r ≠ s) :
    let p := (⟨J, 0, β⟩ : IsingParams ℝ)
    ∃ d : ℝ,
      HasDerivAt (fun J' => correlation G (⟨J', 0, β⟩ : IsingParams ℝ) {r, s}) d J ∧
      d ≤ β * ∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v =>
              correlation G p {r, u} * correlation G p {s, v} +
              correlation G p {r, v} * correlation G p {s, u},
            fun u v => by ring⟩ e
        + β * G.edgeFinset.card := by
  intro p
  have hf : Ferromagnetic p := ⟨hJ, le_refl 0, hβ⟩
  refine ⟨_, hasDerivAt_correlation_J G J 0 β {r, s}, ?_⟩
  have hcard : (G.edgeFinset.card : ℝ) = ∑ _ ∈ G.edgeFinset, (1 : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard, ← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ hβ.le
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
  have huv : u ≠ v := by
    intro heq; subst heq; exact (SimpleGraph.mem_edgeFinset.mp he).ne rfl
  simp only [Sym2.lift_mk]
  by_cases hru : r = u
  · subst hru
    have h1 := summand_le_one G J β hf {r, s} {r, v}
    have h2 : 0 ≤ correlation G p {r, r} * correlation G p {s, v} +
                   correlation G p {r, v} * correlation G p {s, r} :=
      add_nonneg (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
                 (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
    linarith
  by_cases hrv : r = v
  · subst hrv
    have h1 := summand_le_one G J β hf {r, s} {u, r}
    have h2 : 0 ≤ correlation G p {r, u} * correlation G p {s, r} +
                   correlation G p {r, r} * correlation G p {s, u} :=
      add_nonneg (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
                 (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
    linarith
  by_cases hsu : s = u
  · subst hsu
    have h1 := summand_le_one G J β hf {r, s} {s, v}
    have h2 : 0 ≤ correlation G p {r, s} * correlation G p {s, v} +
                   correlation G p {r, v} * correlation G p {s, s} :=
      add_nonneg (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
                 (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
    linarith
  by_cases hsv : s = v
  · subst hsv
    have h1 := summand_le_one G J β hf {r, s} {u, s}
    have h2 : 0 ≤ correlation G p {r, u} * correlation G p {s, s} +
                   correlation G p {r, s} * correlation G p {s, u} :=
      add_nonneg (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
                 (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
    linarith
  -- Non-degenerate: r,s,u,v pairwise distinct
  have h_le := summand_le_lebowitz_of_disjoint G J β hf r s u v hrs hru hrv hsu hsv huv
  linarith [show (0 : ℝ) ≤ 1 from zero_le_one]

/-- **Tight Lebowitz upper bound on J-derivative of 2-point function** (Step 217):
The derivative `d/dJ ⟨σ_r σ_s⟩` at `h = 0` satisfies

  `d/dJ ⟨σ_r σ_s⟩ ≤ β · Σ_e Lebowitz_e + β · |{e ∈ E(G) : r ∈ e ∨ s ∈ e}|`

improving Step 216 by counting only **incident** edges in the error term.

Direct J-direction analogue of `correlation_beta_deriv_le_lebowitz_tight` (Step 154).
The proof mirrors the β version with prefactor `J → β`, using `hasDerivAt_correlation_J`.

Reference: parallel to Glimm–Jaffe §17.5 pp.311–312. -/
theorem correlation_J_deriv_le_lebowitz_tight
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (r s : ι) (hrs : r ≠ s) :
    let p := (⟨J, 0, β⟩ : IsingParams ℝ)
    ∃ d : ℝ,
      HasDerivAt (fun J' => correlation G (⟨J', 0, β⟩ : IsingParams ℝ) {r, s}) d J ∧
      d ≤ β * ∑ e ∈ G.edgeFinset,
              Sym2.lift ⟨fun u v =>
                  correlation G p {r, u} * correlation G p {s, v} +
                  correlation G p {r, v} * correlation G p {s, u},
                fun u v => by ring⟩ e
          + β * (G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e)).card := by
  classical
  intro p
  have hf : Ferromagnetic p := ⟨hJ, le_refl 0, hβ⟩
  refine ⟨_, hasDerivAt_correlation_J G J 0 β {r, s}, ?_⟩
  set leb : Sym2 ι → ℝ := fun e =>
    Sym2.lift ⟨fun u v => correlation G p {r, u} * correlation G p {s, v} +
                           correlation G p {r, v} * correlation G p {s, u},
              fun u v => by ring⟩ e
  set summ : Sym2 ι → ℝ := fun e =>
    Sym2.lift ⟨fun u v => correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff {r, s} {u, v}) -
                           correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} *
                           correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
              fun u v => by simp [Finset.pair_comm v u]⟩ e
  set deg := G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e)
  have h_leb_nn : ∀ e ∈ G.edgeFinset, 0 ≤ leb e := fun e _ => by
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    exact add_nonneg (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
                     (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
  have h_bound : ∑ e ∈ G.edgeFinset, summ e ≤ ∑ e ∈ G.edgeFinset, leb e + deg.card := by
    have split := (Finset.sum_filter_add_sum_filter_not G.edgeFinset
      (fun e => r ∈ e ∨ s ∈ e) summ).symm
    rw [split]
    have h1 : ∑ e ∈ deg, summ e ≤ deg.card := by
      rw [show (deg.card : ℝ) = ∑ _ ∈ deg, 1 from by simp]
      apply Finset.sum_le_sum
      intro e he
      rw [Finset.mem_filter] at he
      obtain ⟨heE, hmem⟩ := he
      obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
      simp only [Sym2.lift_mk, Sym2.mem_iff, summ] at hmem ⊢
      rcases hmem with (hru | hrv) | (hsu | hsv)
      · subst hru; exact summand_le_one G J β hf {r, s} {r, v}
      · subst hrv; exact summand_le_one G J β hf {r, s} {u, r}
      · subst hsu; exact summand_le_one G J β hf {r, s} {s, v}
      · subst hsv; exact summand_le_one G J β hf {r, s} {u, s}
    have h2 : ∑ e ∈ G.edgeFinset.filter (fun e => ¬(r ∈ e ∨ s ∈ e)), summ e ≤
              ∑ e ∈ G.edgeFinset, leb e :=
      calc ∑ e ∈ G.edgeFinset.filter (fun e => ¬(r ∈ e ∨ s ∈ e)), summ e
          ≤ ∑ e ∈ G.edgeFinset.filter (fun e => ¬(r ∈ e ∨ s ∈ e)), leb e := by
              apply Finset.sum_le_sum
              intro e he
              rw [Finset.mem_filter] at he
              obtain ⟨heE, hni⟩ := he
              obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
              have huv : u ≠ v := (SimpleGraph.mem_edgeFinset.mp heE).ne
              simp only [Sym2.mem_iff, not_or] at hni
              obtain ⟨⟨hru, hrv⟩, hsu, hsv⟩ := hni
              exact summand_le_lebowitz_of_disjoint G J β hf r s u v hrs hru hrv hsu hsv huv
        _ ≤ ∑ e ∈ G.edgeFinset, leb e :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun e he _ => h_leb_nn e he)
    have eq_deg : ∑ x ∈ G.edgeFinset with r ∈ x ∨ s ∈ x, summ x = ∑ e ∈ deg, summ e := rfl
    linarith
  calc β * ∑ e ∈ G.edgeFinset, summ e
      ≤ β * (∑ e ∈ G.edgeFinset, leb e + ↑(#deg)) :=
          mul_le_mul_of_nonneg_left h_bound hβ.le
    _ = β * G.edgeFinset.sum leb + β * ↑(#deg) := by ring

/-! ## Step 255: free energy J-derivative -/

/-- **Free energy J-derivative** (Step 255):
For any `(J, h, β)` and finite-volume Ising:

  `d/dJ freeEnergy(J) = |ι|⁻¹ · β · gibbsExpectation(Σ_e edgeSpin σ e)`

since `freeEnergy = |ι|⁻¹ · log(partitionFunction)` and
`d/dJ log(Z) = Z'(J)/Z(J) = β · ⟨Σ_e edgeSpin⟩` by `hasDerivAt_partitionFunction_J`.

Reference: Glimm–Jaffe §4.6 / §17.5; standard thermodynamic identity. -/
theorem hasDerivAt_freeEnergy_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun J' => freeEnergy G (⟨J', h, β⟩ : IsingParams ℝ))
      ((Fintype.card ι : ℝ)⁻¹ *
        gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ)
          (fun σ => β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e))) J := by
  set p := (⟨J, h, β⟩ : IsingParams ℝ)
  have hZpos : 0 < partitionFunction G p := partitionFunction_pos G p
  have hZne : partitionFunction G p ≠ 0 := hZpos.ne'
  have hZderiv := hasDerivAt_partitionFunction_J G J h β
  have hlogZ : HasDerivAt
      (fun J' => Real.log (partitionFunction G (⟨J', h, β⟩ : IsingParams ℝ)))
      ((∑ σ, β * (∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e) *
          boltzmannWeight G p σ) / partitionFunction G p) J := by
    have h := hZderiv.log hZne
    convert h using 1
  have hfreeE : (fun J' => freeEnergy G (⟨J', h, β⟩ : IsingParams ℝ)) =
      (fun J' => (Fintype.card ι : ℝ)⁻¹ *
        Real.log (partitionFunction G (⟨J', h, β⟩ : IsingParams ℝ))) := by
    funext J'; rfl
  rw [hfreeE]
  have h := hlogZ.const_mul ((Fintype.card ι : ℝ)⁻¹)
  convert h using 1
  unfold gibbsExpectation
  field_simp

end IsingModel
