import IsingModel.GibbsMeasure
import IsingModel.BetaDerivative
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Coupling derivative for bond subsets (GJ §17.8 infrastructure, Step 135)

Differentiability of finite-volume Ising correlations with respect to a
coupling parameter `s` that scales a subset `E₀ ⊆ Sym2 ι` of bonds from
full coupling `J` to `s·J` (s = 0: bonds absent; s = 1: full coupling).

## Setup

The parameterized Boltzmann weight:
  `w_s(σ) = w_G(σ) · exp(−β·(1−s)·J · Σ_{e∈E₀} σₑ)`

At s=0: Boltzmann weight with E₀-bonds removed.
At s=1: standard Boltzmann weight `w_G(σ)`.

## Main results

* `hasDerivAt_scaledBoltzmannWeight` — `d/ds w_s(σ) = β·J·(ΣE₀ σₑ)·w_s(σ)`
* `hasDerivAt_scaledCorrelation` — derivative of `⟨σ^A⟩s` in s

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.8 pp. 316–318, Springer 1987.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Definitions -/

/-- **Scaled Boltzmann weight** parameterized by `s`:
`w_s(σ) = w_G(σ) · exp(−β·(1−s)·J · Σ_{e∈E₀} edgeSpin σ e)`.

`s=1`: full Gibbs weight. `s=0`: weight with E₀-bonds absent. -/
noncomputable def scaledBoltzmannWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (σ : Config ι) : ℝ :=
  boltzmannWeight G p σ *
    Real.exp (-p.β * (1 - s) * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e)

/-- **Scaled partition function**. -/
noncomputable def scaledPartitionFunction (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) : ℝ :=
  ∑ σ : Config ι, scaledBoltzmannWeight G E₀ p s σ

/-- **Scaled Gibbs expectation**. -/
noncomputable def scaledGibbsExpectation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (F : Config ι → ℝ) : ℝ :=
  (scaledPartitionFunction G E₀ p s)⁻¹ *
    ∑ σ : Config ι, F σ * scaledBoltzmannWeight G E₀ p s σ

/-- **Scaled correlation**. -/
noncomputable def scaledCorrelation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (A : Finset ι) : ℝ :=
  scaledGibbsExpectation G E₀ p s (spinProduct A)

/-! ## Basic properties -/

omit [DecidableEq ι] in
/-- Scaled Boltzmann weight is positive. -/
theorem scaledBoltzmannWeight_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (σ : Config ι) :
    0 < scaledBoltzmannWeight G E₀ p s σ :=
  mul_pos (boltzmannWeight_pos G p σ) (Real.exp_pos _)

/-- Scaled partition function is positive. -/
theorem scaledPartitionFunction_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) :
    0 < scaledPartitionFunction G E₀ p s :=
  Finset.sum_pos (fun σ _ => scaledBoltzmannWeight_pos G E₀ p s σ) Finset.univ_nonempty

/-- Scaled partition function is nonzero. -/
theorem scaledPartitionFunction_ne_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) :
    scaledPartitionFunction G E₀ p s ≠ 0 :=
  ne_of_gt (scaledPartitionFunction_pos G E₀ p s)

omit [DecidableEq ι] in
/-- At `s = 1`: scaled model is the full model. -/
theorem scaledBoltzmannWeight_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (σ : Config ι) :
    scaledBoltzmannWeight G E₀ p 1 σ = boltzmannWeight G p σ := by
  simp only [scaledBoltzmannWeight, sub_self, zero_mul, mul_zero, Real.exp_zero, mul_one]

/-- At `s = 1`: scaled correlation equals standard correlation. -/
theorem scaledCorrelation_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (A : Finset ι) :
    scaledCorrelation G E₀ p 1 A = correlation G p A := by
  simp [scaledCorrelation, scaledGibbsExpectation, scaledPartitionFunction,
        scaledBoltzmannWeight_one, correlation, gibbsExpectation, partitionFunction]

/-! ## Derivative of Boltzmann weight -/

omit [DecidableEq ι] in
/-- **d/ds w_s(σ) = β·J·(Σ_{e∈E₀} σₑ) · w_s(σ)**. -/
theorem hasDerivAt_scaledBoltzmannWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (σ : Config ι) :
    HasDerivAt (fun s' => scaledBoltzmannWeight G E₀ p s' σ)
      (p.β * p.J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) *
       scaledBoltzmannWeight G E₀ p s σ) s := by
  set X := ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e
  set c := boltzmannWeight G p σ
  -- scaledBoltzmannWeight G E₀ p s' σ = c * exp(-β*(1-s')*J*X)
  have hsbw_eq : ∀ s' : ℝ,
      scaledBoltzmannWeight G E₀ p s' σ = c * Real.exp (-p.β * (1 - s') * p.J * X) :=
    fun s' => rfl
  simp_rw [hsbw_eq]
  -- d/ds [-β*(1-s)*J*X] = β*J*X
  have h_inner : HasDerivAt (fun s' : ℝ => -p.β * (1 - s') * p.J * X) (p.β * p.J * X) s := by
    have heq : (fun s' : ℝ => -p.β * (1 - s') * p.J * X) =
        fun s' => p.β * p.J * X * s' - p.β * p.J * X := by funext s'; ring
    rw [heq]
    have h := ((hasDerivAt_id s).const_mul (p.β * p.J * X))
    simp only [mul_one, Function.id_def] at h
    exact h.sub_const (p.β * p.J * X)
  -- d/ds exp(-β*(1-s)*J*X) = exp(...) * β*J*X  (HasDerivAt.exp)
  have h_exp := h_inner.exp
  -- d/ds [c * exp(...)] = c * (exp(...) * β*J*X)
  have h_mul := h_exp.const_mul c
  convert h_mul using 1
  ring

/-! ## Derivative of partition function -/

/-- **d/ds Zs = β·J · Σ_σ (Σ_{E₀} σₑ) · w_s(σ)**. -/
theorem hasDerivAt_scaledPartitionFunction (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) :
    HasDerivAt (fun s' => scaledPartitionFunction G E₀ p s')
      (p.β * p.J * ∑ σ : Config ι,
        (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) * scaledBoltzmannWeight G E₀ p s σ) s := by
  simp only [scaledPartitionFunction]
  have hsum : HasDerivAt (fun s' => ∑ σ : Config ι, scaledBoltzmannWeight G E₀ p s' σ)
      (∑ σ : Config ι, p.β * p.J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) *
        scaledBoltzmannWeight G E₀ p s σ) s :=
    HasDerivAt.fun_sum (fun σ _ => hasDerivAt_scaledBoltzmannWeight G E₀ p s σ)
  convert hsum using 1
  simp [Finset.mul_sum, mul_comm, mul_assoc]

/-- Weighted scaled Boltzmann sum is differentiable in s. -/
private theorem hasDerivAt_weightedScaledBoltzmannSum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (F : Config ι → ℝ) :
    HasDerivAt
      (fun s' => ∑ σ : Config ι, F σ * scaledBoltzmannWeight G E₀ p s' σ)
      (∑ σ : Config ι, F σ * (p.β * p.J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) *
        scaledBoltzmannWeight G E₀ p s σ)) s :=
  HasDerivAt.fun_sum (fun σ _ =>
    (hasDerivAt_scaledBoltzmannWeight G E₀ p s σ).const_mul (F σ))

/-! ## Derivative of Gibbs expectation -/

/-- **d/ds ⟨F⟩s = β·J · Σ_e (⟨F·σₑ⟩s − ⟨F⟩s·⟨σₑ⟩s)** (quotient rule). -/
private theorem hasDerivAt_scaledGibbsExpectation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (F : Config ι → ℝ) :
    HasDerivAt
      (fun s' => scaledGibbsExpectation G E₀ p s' F)
      (scaledGibbsExpectation G E₀ p s
            (fun σ => F σ * (p.β * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e)) -
       scaledGibbsExpectation G E₀ p s F *
       scaledGibbsExpectation G E₀ p s
            (fun σ => p.β * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e))
      s := by
  have hZpos : 0 < scaledPartitionFunction G E₀ p s := scaledPartitionFunction_pos G E₀ p s
  have hZne : scaledPartitionFunction G E₀ p s ≠ 0 := hZpos.ne'
  -- Use named functions to avoid definitional equality issues
  set Zs : ℝ → ℝ := fun s' => scaledPartitionFunction G E₀ p s' with hZs_def
  set Ns : ℝ → ℝ :=
    fun s' => ∑ σ : Config ι, F σ * scaledBoltzmannWeight G E₀ p s' σ with hNs_def
  -- scaledGibbsExpectation = Zs⁻¹ * Ns
  have hge_eq : ∀ s', scaledGibbsExpectation G E₀ p s' F = (Zs s')⁻¹ * Ns s' := fun _ => rfl
  simp_rw [hge_eq]
  -- Derivatives of Zs and Ns
  have hZderiv : HasDerivAt Zs (p.β * p.J * ∑ σ : Config ι,
      (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) * scaledBoltzmannWeight G E₀ p s σ) s :=
    hasDerivAt_scaledPartitionFunction G E₀ p s
  have hZinv : HasDerivAt (fun s' => (Zs s')⁻¹)
      (-(p.β * p.J * ∑ σ : Config ι,
          (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) * scaledBoltzmannWeight G E₀ p s σ) /
       (Zs s) ^ 2) s := hZderiv.inv hZne
  have hNderiv : HasDerivAt Ns
      (∑ σ : Config ι, F σ * (p.β * p.J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) *
        scaledBoltzmannWeight G E₀ p s σ)) s :=
    hasDerivAt_weightedScaledBoltzmannSum G E₀ p s F
  -- Product rule
  have hprod := hZinv.mul hNderiv
  -- hprod : HasDerivAt (fun s' => (Zs s')⁻¹ * Ns s') D_raw s
  -- Goal: HasDerivAt (fun s' => (Zs s')⁻¹ * Ns s') D_goal s
  -- Both have the same function; need D_raw = D_goal
  convert hprod using 1
  -- D_goal = D_raw: both equal β*J*(Z⁻¹*NFX - Z⁻²*NF*NX)
  simp only [scaledGibbsExpectation, hZs_def, hNs_def]
  set NF : ℝ := ∑ σ : Config ι, F σ * scaledBoltzmannWeight G E₀ p s σ with hNF_def
  set NX : ℝ := ∑ σ : Config ι, (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) *
      scaledBoltzmannWeight G E₀ p s σ with hNX_def
  set Z := scaledPartitionFunction G E₀ p s with hZ_def
  -- Normalize sums: Σ (β*J * X) * bw = β*J * NX
  have h_norm_X : ∑ σ : Config ι, (p.β * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) *
      scaledBoltzmannWeight G E₀ p s σ = p.β * p.J * NX := by
    have h : ∑ σ : Config ι, (p.β * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) *
        scaledBoltzmannWeight G E₀ p s σ =
        ∑ σ : Config ι, p.β * p.J * ((∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) *
        scaledBoltzmannWeight G E₀ p s σ) :=
      Finset.sum_congr rfl (fun x _ => by ring)
    rw [h, ← Finset.mul_sum]
  -- Normalize sums: Σ F*(β*J*X)*bw = Σ F*(β*J*X*bw)  [ring inside sum]
  have h_norm_FX_goal : ∑ σ : Config ι, F σ * (p.β * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) *
      scaledBoltzmannWeight G E₀ p s σ =
      ∑ σ : Config ι, F σ * (p.β * p.J * (∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) *
      scaledBoltzmannWeight G E₀ p s σ) := by
    apply Finset.sum_congr rfl; intro x _; ring
  rw [h_norm_FX_goal, h_norm_X]
  field_simp [hZne]
  have hS : ∑ x : Config ι, (F x * p.β * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) x e) *
      scaledBoltzmannWeight G E₀ p s x =
      ∑ x : Config ι, (p.β * p.J * F x * ∑ e ∈ E₀, edgeSpin (K := ℝ) x e) *
      scaledBoltzmannWeight G E₀ p s x :=
    Finset.sum_congr rfl fun x _ => by ring
  linear_combination Z * hS

/-! ## Helper lemmas -/

omit [Fintype ι] in
private lemma edgeSpin_quot_eq_spinProduct'
    {i j : ι} (hij : i ≠ j) (σ : Config ι) :
    edgeSpin (K := ℝ) σ (Quot.mk _ (i, j) : Sym2 ι) = spinProduct {i, j} σ := by
  simp [edgeSpin, spinProduct, Finset.prod_pair hij, Spin.sign]

/-! ## Main derivative formula -/

/-- **Derivative formula for scaled Ising correlations** (GJ §17.8):

For `E₀ : Finset (Sym2 ι)` a non-diagonal subset and arbitrary Ising parameters `p`:
`d/ds ⟨σ^A⟩s = β·J · Σ_{e=(u,v)∈E₀} [⟨σ^{A△{u,v}}⟩s − ⟨σ^A⟩s · ⟨σ^{u,v}⟩s]`.

Reference: Glimm–Jaffe §17.8 pp. 316–318. -/
theorem hasDerivAt_scaledCorrelation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬ e.IsDiag)
    (p : IsingParams ℝ) (s : ℝ) (A : Finset ι) :
    HasDerivAt (fun s' => scaledCorrelation G E₀ p s' A)
      (p.β * p.J * ∑ e ∈ E₀,
        Sym2.lift ⟨fun u v =>
          scaledCorrelation G E₀ p s (symmDiff A {u, v}) -
          scaledCorrelation G E₀ p s A * scaledCorrelation G E₀ p s {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e)
      s := by
  unfold scaledCorrelation
  have hderiv := hasDerivAt_scaledGibbsExpectation G E₀ p s (spinProduct A)
  -- Rewrite ⟨spinProduct A * (β*J * Σ_{E₀} edgeSpin)⟩_s = β*J * Σ_{E₀} ⟨spinProduct(A△e)⟩_s
  have hFX : scaledGibbsExpectation G E₀ p s
      (fun σ => spinProduct A σ * (p.β * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e)) =
      p.β * p.J * ∑ e ∈ E₀,
        Sym2.lift ⟨fun u v => scaledGibbsExpectation G E₀ p s (spinProduct (symmDiff A {u, v})),
          fun u v => by simp [Finset.pair_comm v u]⟩ e := by
    unfold scaledGibbsExpectation
    have hinner : ∑ σ : Config ι,
        spinProduct A σ * (p.β * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) *
        scaledBoltzmannWeight G E₀ p s σ =
        p.β * p.J * ∑ e ∈ E₀,
          Sym2.lift ⟨fun u v => ∑ σ : Config ι,
              spinProduct (symmDiff A {u, v}) σ * scaledBoltzmannWeight G E₀ p s σ,
            fun u v => by simp [Finset.pair_comm v u]⟩ e := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
      have huv : u ≠ v := by
        intro heq; subst heq
        exact hE₀_nd _ he (Sym2.mk_isDiag_iff.mpr rfl)
      simp only [Sym2.lift_mk]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [edgeSpin_quot_eq_spinProduct' huv, ← spinProduct_mul]
      ring
    rw [hinner]
    rw [← mul_assoc, mul_comm (scaledPartitionFunction G E₀ p s)⁻¹ (p.β * p.J),
        mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
  -- Rewrite ⟨β*J * Σ_{E₀} edgeSpin⟩_s = β*J * Σ_{E₀} scaledCorrelation_s {u,v}
  have hX_exp : scaledGibbsExpectation G E₀ p s
      (fun σ => p.β * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) =
      p.β * p.J * ∑ e ∈ E₀,
        Sym2.lift ⟨fun u v => scaledGibbsExpectation G E₀ p s (spinProduct {u, v}),
          fun u v => by simp [Finset.pair_comm v u]⟩ e := by
    unfold scaledGibbsExpectation
    have hinner : ∑ σ : Config ι,
        (p.β * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e) *
        scaledBoltzmannWeight G E₀ p s σ =
        p.β * p.J * ∑ e ∈ E₀,
          Sym2.lift ⟨fun u v => ∑ σ : Config ι,
              spinProduct {u, v} σ * scaledBoltzmannWeight G E₀ p s σ,
            fun u v => by simp [Finset.pair_comm v u]⟩ e := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
      have huv : u ≠ v := by
        intro heq; subst heq
        exact hE₀_nd _ he (Sym2.mk_isDiag_iff.mpr rfl)
      simp only [Sym2.lift_mk]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [edgeSpin_quot_eq_spinProduct' huv]
      ring
    rw [hinner]
    rw [← mul_assoc, mul_comm (scaledPartitionFunction G E₀ p s)⁻¹ (p.β * p.J),
        mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
  -- Assemble
  rw [hFX, hX_exp] at hderiv
  convert hderiv using 1
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  ring

end IsingModel
