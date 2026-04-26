import IsingModel.GibbsMeasure
import IsingModel.Inequalities.NonnegCorrelations
import IsingModel.Inequalities.GKS
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Field (h) derivatives for correlations (GJ §17.6 Step 118)

Differentiability of finite-volume Ising correlations in the external field
parameter `h`, with the explicit derivative formula.

## Main results

* `hasDerivAt_boltzmannWeight_field` — `d/dh exp(-β·H(σ)) = β·M(σ)·exp(-β·H(σ))`
* `hasDerivAt_partitionFunction_field` — `d/dh Z(h) = Σ_σ β·M(σ)·bw(σ)`
* `hasDerivAt_correlation_field` — `d/dh ⟨σ^A⟩_h = β·(⟨σ^A·M⟩ − ⟨σ^A⟩·⟨M⟩)`

where `M(σ) = totalMagnetization σ = Σ_i sign(σ_i)`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.6 pp. 348–351, Springer 1987.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Total magnetization -/

/-- The total magnetization: `∑_i sign(σ_i)`. -/
noncomputable def totalMagnetization (σ : Config ι) : ℝ :=
  ∑ i : ι, (↑(σ i).toSign : ℝ)

/-! ## Relation between externalFieldEnergy and totalMagnetization -/

omit [DecidableEq ι] in
/-- `externalFieldEnergy h σ = -h · totalMagnetization σ`. -/
private lemma externalFieldEnergy_eq (h : ℝ) (σ : Config ι) :
    externalFieldEnergy h σ = -h * totalMagnetization σ := by
  simp [externalFieldEnergy, totalMagnetization, Spin.sign]

omit [DecidableEq ι] in
/-- `d/dh externalFieldEnergy h σ = -totalMagnetization σ`. -/
private lemma hasDerivAt_externalFieldEnergy
    (h : ℝ) (σ : Config ι) :
    HasDerivAt (fun h' => externalFieldEnergy h' σ) (-totalMagnetization σ) h := by
  simp_rw [externalFieldEnergy_eq]
  have h1 := ((hasDerivAt_id h).neg).mul_const (totalMagnetization σ)
  simp only [Function.id_def, neg_one_mul] at h1
  exact h1

/-! ## Hamiltonian h-derivative -/

omit [DecidableEq ι] in
/-- `d/dh H(σ; J, h, β) = -totalMagnetization σ`.

The interaction energy is constant in `h`; only the external field term contributes. -/
private lemma hasDerivAt_hamiltonian_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (σ : Config ι) :
    HasDerivAt (fun h' => hamiltonian G (⟨J, h', β⟩ : IsingParams ℝ) σ)
      (-totalMagnetization σ) h := by
  rw [show (fun h' => hamiltonian G (⟨J, h', β⟩ : IsingParams ℝ) σ) =
      (fun h' => interactionEnergy G J σ + externalFieldEnergy h' σ) from rfl]
  have h1 := (hasDerivAt_const h (interactionEnergy G J σ)).add
      (hasDerivAt_externalFieldEnergy h σ)
  simp only [zero_add] at h1
  exact h1

/-! ## Boltzmann weight h-derivative -/

omit [DecidableEq ι] in
/-- **Boltzmann weight is differentiable in h**:
`d/dh exp(-β · H(σ)) = β · totalMagnetization(σ) · exp(-β · H(σ))`.

Proof: chain rule via `d/dh H = -M`, so `d/dh [-β·H] = β·M`.

Reference: Glimm–Jaffe §17.6 pp. 348–351. -/
theorem hasDerivAt_boltzmannWeight_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (σ : Config ι) :
    HasDerivAt (fun h' => boltzmannWeight G (⟨J, h', β⟩ : IsingParams ℝ) σ)
      (β * totalMagnetization σ * boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ) h := by
  set H := hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) σ
  set M := totalMagnetization σ
  have hbw : ∀ h' : ℝ,
      boltzmannWeight G (⟨J, h', β⟩ : IsingParams ℝ) σ =
      Real.exp (-β * hamiltonian G (⟨J, h', β⟩ : IsingParams ℝ) σ) := fun h' => rfl
  simp_rw [hbw]
  have hH := hasDerivAt_hamiltonian_field G J h β σ
  have harg : HasDerivAt (fun h' => -β * hamiltonian G (⟨J, h', β⟩ : IsingParams ℝ) σ)
      (-β * (-M)) h := hH.const_mul (-β)
  have hexp := (Real.hasDerivAt_exp (-β * H)).comp h harg
  rw [show (Real.exp ∘ fun h' => -β * hamiltonian G (⟨J, h', β⟩ : IsingParams ℝ) σ) =
      fun h' => Real.exp (-β * hamiltonian G (⟨J, h', β⟩ : IsingParams ℝ) σ) from rfl] at hexp
  convert hexp using 1
  ring

/-! ## Partition function h-derivative -/

/-- **Partition function is differentiable in h**:
`d/dh Z(h) = Σ_σ β · totalMagnetization(σ) · bw(σ)`.

Reference: Glimm–Jaffe §17.6. -/
theorem hasDerivAt_partitionFunction_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun h' => partitionFunction G (⟨J, h', β⟩ : IsingParams ℝ))
      (∑ σ : Config ι,
        β * totalMagnetization σ * boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ) h := by
  simp only [partitionFunction]
  exact HasDerivAt.fun_sum (fun σ _ => hasDerivAt_boltzmannWeight_field G J h β σ)

/-! ## Weighted Boltzmann sum h-derivative -/

/-- Weighted Boltzmann sum is differentiable in h. -/
private theorem hasDerivAt_weightedBoltzmannSum_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (F : Config ι → ℝ) :
    HasDerivAt
      (fun h' => ∑ σ : Config ι, F σ * boltzmannWeight G (⟨J, h', β⟩ : IsingParams ℝ) σ)
      (∑ σ : Config ι,
        F σ * (β * totalMagnetization σ * boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ)) h := by
  apply HasDerivAt.fun_sum
  intro σ _
  exact (hasDerivAt_boltzmannWeight_field G J h β σ).const_mul (F σ)

/-! ## Gibbs expectation h-derivative -/

/-- **Gibbs expectation is differentiable in h**:
`d/dh ⟨F⟩_h = β · (⟨F · M⟩_h − ⟨F⟩_h · ⟨M⟩_h)`.

Proof: quotient rule on `⟨F⟩ = Z⁻¹ · Σ F·bw`.

Reference: Glimm–Jaffe §17.6. -/
private theorem hasDerivAt_gibbsExpectation_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (F : Config ι → ℝ) :
    HasDerivAt
      (fun h' => gibbsExpectation G (⟨J, h', β⟩ : IsingParams ℝ) F)
      (β * (gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) (fun σ => F σ * totalMagnetization σ) -
            gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) F *
            gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) totalMagnetization)) h := by
  set p := (⟨J, h, β⟩ : IsingParams ℝ)
  have hZpos := partitionFunction_pos G p
  have hZne : partitionFunction G p ≠ 0 := hZpos.ne'
  have hge_eq : ∀ h',
      gibbsExpectation G (⟨J, h', β⟩ : IsingParams ℝ) F =
      (partitionFunction G (⟨J, h', β⟩ : IsingParams ℝ))⁻¹ *
      ∑ σ : Config ι, F σ * boltzmannWeight G (⟨J, h', β⟩ : IsingParams ℝ) σ := fun _ => rfl
  simp_rw [hge_eq]
  have hZderiv := hasDerivAt_partitionFunction_field G J h β
  have hZinv : HasDerivAt (fun h' => (partitionFunction G (⟨J, h', β⟩ : IsingParams ℝ))⁻¹)
      (-(∑ σ, β * totalMagnetization σ * boltzmannWeight G p σ) / (partitionFunction G p) ^ 2) h :=
    (show (⟨J, h, β⟩ : IsingParams ℝ) = p from rfl) ▸ hZderiv.inv hZne
  have hnum := hasDerivAt_weightedBoltzmannSum_field G J h β F
  have hprod := hZinv.mul hnum
  convert hprod using 1
  simp only [gibbsExpectation, p]
  set Z := partitionFunction G (⟨J, h, β⟩ : IsingParams ℝ)
  have hZne' : Z ≠ 0 := hZne
  -- Rewrite sums with β factored out for ring
  have hFM : ∑ x : Config ι, F x * (β * totalMagnetization x *
      boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) x) =
      β * ∑ x : Config ι, F x * totalMagnetization x *
      boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) x := by
    simp_rw [show ∀ x : Config ι, F x * (β * totalMagnetization x *
        boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) x) =
        β * (F x * totalMagnetization x * boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) x)
        from fun x => by ring]
    rw [← Finset.mul_sum]
  rw [hFM]
  have hMβ : ∑ x : Config ι, β * totalMagnetization x *
      boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) x =
      β * ∑ x : Config ι, totalMagnetization x *
      boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) x := by
    simp_rw [show ∀ x : Config ι, β * totalMagnetization x *
        boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) x =
        β * (totalMagnetization x * boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) x)
        from fun x => by ring]
    rw [← Finset.mul_sum]
  field_simp [hZne']
  rw [hMβ]
  ring

/-! ## Main correlation h-derivative -/

/-- **Derivative formula for Ising correlations w.r.t. external field** (GJ §17.6):
`d/dh ⟨σ^A⟩_h = β · (⟨σ^A · M⟩_h − ⟨σ^A⟩_h · ⟨M⟩_h)`.

Here `M(σ) = totalMagnetization σ = Σ_i sign(σ_i)`.

Proof: Apply the quotient rule for Gibbs expectations with `F = spinProduct A`.

Reference: Glimm–Jaffe §17.6 pp. 348–351. -/
theorem hasDerivAt_correlation_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (A : Finset ι) :
    HasDerivAt (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) A)
      (β * (gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ)
              (fun σ => spinProduct A σ * totalMagnetization σ) -
            correlation G (⟨J, h, β⟩ : IsingParams ℝ) A *
            gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) totalMagnetization)) h := by
  unfold correlation
  exact hasDerivAt_gibbsExpectation_field G J h β (spinProduct A)

/-! ## Monotonicity in h (Step 121): GKS-II-based bound -/

omit [DecidableEq ι] in
/-- `totalMagnetization σ = Σ_i spinProduct {i} σ`. -/
private lemma totalMagnetization_eq_sum_spinProduct (σ : Config ι) :
    totalMagnetization σ = ∑ i : ι, spinProduct {i} σ := by
  simp [totalMagnetization, spinProduct]

/-- `spinProduct A σ * totalMagnetization σ = Σ_i spinProduct (symmDiff A {i}) σ`. -/
private lemma spinProduct_mul_totalMagnetization (A : Finset ι) (σ : Config ι) :
    spinProduct A σ * totalMagnetization σ =
    ∑ i : ι, spinProduct (symmDiff A {i}) σ := by
  rw [totalMagnetization_eq_sum_spinProduct, Finset.mul_sum]
  congr 1; ext i
  exact spinProduct_mul A {i} σ

/-- `⟨spinProduct A · M⟩_p = Σ_i ⟨σ^{AΔ{i}}⟩_p`. -/
private lemma gibbsExpectation_spinProd_mul_mag
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    gibbsExpectation G p (fun σ => spinProduct A σ * totalMagnetization σ) =
    ∑ i : ι, correlation G p (symmDiff A {i}) := by
  simp_rw [spinProduct_mul_totalMagnetization, correlation, gibbsExpectation,
           Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- `⟨M⟩_p = Σ_i correlation G p {i}`. -/
private lemma gibbsExpectation_totalMag_eq_sum
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    gibbsExpectation G p totalMagnetization = ∑ i : ι, correlation G p {i} := by
  simp_rw [correlation, gibbsExpectation, totalMagnetization_eq_sum_spinProduct,
           Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The h-derivative of correlations is nonneg for ferromagnetic Ising (h ≥ 0).

`d/dh ⟨σ^A⟩_h = β · Σ_i (⟨σ^{AΔ{i}}⟩ - ⟨σ^A⟩·⟨σ_i⟩) ≥ 0`

by GKS-II (each term ≥ 0 for ferromagnetic `h ≥ 0`).

Reference: Glimm–Jaffe §17.5 p.311 (implicit in the monotonicity of correlations in h). -/
theorem correlation_field_deriv_nonneg
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (A : Finset ι)
    (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ)) (hβ : 0 ≤ β) :
    0 ≤ β * (gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ)
              (fun σ => spinProduct A σ * totalMagnetization σ) -
            correlation G (⟨J, h, β⟩ : IsingParams ℝ) A *
            gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) totalMagnetization) := by
  apply mul_nonneg hβ
  rw [gibbsExpectation_spinProd_mul_mag, gibbsExpectation_totalMag_eq_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro i _
  linarith [gks_second G (⟨J, h, β⟩ : IsingParams ℝ) hf A {i}]

end IsingModel
