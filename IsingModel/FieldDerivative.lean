import IsingModel.GibbsMeasure
import IsingModel.FreeEnergy
import IsingModel.Inequalities.NonnegCorrelations
import IsingModel.Inequalities.GKS
import IsingModel.Inequalities.GHS
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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

/-- The h-derivative of correlations is nonneg (infinitesimal form of h-monotonicity).

`d/dh ⟨σ^A⟩_h = β · Σ_i (⟨σ^{AΔ{i}}⟩ - ⟨σ^A⟩·⟨σ_i⟩) ≥ 0`

by GKS-II: each term `⟨σ^{AΔ{i}}⟩ - ⟨σ^A⟩·⟨σ_i⟩ ≥ 0` for ferromagnetic `h ≥ 0`.
This is the infinitesimal form underlying the monotonicity of correlations in `h`.

Reference: Friedli–Velenik §4.2, Prop. 4.2.4 (p. 58);
Glimm–Jaffe §17.6 pp. 348–351 (derivative formula). -/
theorem correlation_field_deriv_nonneg
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (A : Finset ι)
    (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ)) :
    0 ≤ β * (gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ)
              (fun σ => spinProduct A σ * totalMagnetization σ) -
            correlation G (⟨J, h, β⟩ : IsingParams ℝ) A *
            gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) totalMagnetization) := by
  apply mul_nonneg hf.hβ.le
  rw [gibbsExpectation_spinProd_mul_mag, gibbsExpectation_totalMag_eq_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro i _
  linarith [gks_second G (⟨J, h, β⟩ : IsingParams ℝ) hf A {i}]

/-! ## GHS consequence: truncated2 antitone in h (Step 124) -/

/-- Helper: the per-site summand in `d/dh truncated2(i,j)`.

For each `k : ι`, this is
`corr(symmDiff {i,j} {k}) - corr(symmDiff {i} {k}) * corr({j})
- corr({i}) * corr(symmDiff {j} {k}) - corr({i,j}) * corr({k})
+ 2 * corr({i}) * corr({j}) * corr({k})`.

For `k ∉ {i,j}` this equals `truncated3 G p i j k ≤ 0` (GHS).
For `k = i` or `k = j` this equals `-2 * corr({m}) * truncated2 G p i j ≤ 0`. -/
private noncomputable def truncated2FieldDerivSummand
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i j k : ι) : ℝ :=
  correlation G p (symmDiff {i, j} {k})
  - correlation G p (symmDiff {i} {k}) * correlation G p {j}
  - correlation G p {i} * correlation G p (symmDiff {j} {k})
  - correlation G p {i, j} * correlation G p {k}
  + 2 * correlation G p {i} * correlation G p {j} * correlation G p {k}

/-- For `k ∉ {i, j}`, the summand equals `truncated3 G p i j k`. -/
private lemma truncated2FieldDerivSummand_of_not_mem
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) {i j k : ι} (hki : k ≠ i) (hkj : k ≠ j) :
    truncated2FieldDerivSummand G p i j k = truncated3 G p i j k := by
  unfold truncated2FieldDerivSummand truncated3
  have hijk : symmDiff ({i, j} : Finset ι) {k} = {i, j, k} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h | rfl, hk⟩ | ⟨rfl, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact Or.inl ⟨Or.inl rfl, hki.symm⟩
      · exact Or.inl ⟨Or.inr rfl, hkj.symm⟩
      · exact Or.inr ⟨rfl, fun h => h.elim hki hkj⟩
  have hik : symmDiff ({i} : Finset ι) {k} = {i, k} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hki.symm⟩
      · exact Or.inr ⟨rfl, hki⟩
  have hjk : symmDiff ({j} : Finset ι) {k} = {j, k} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hkj.symm⟩
      · exact Or.inr ⟨rfl, hkj⟩
  rw [hijk, hik, hjk]; ring

/-- For `k = i` (with `i ≠ j`), the summand equals `-2 * corr({i}) * truncated2`. -/
private lemma truncated2FieldDerivSummand_of_eq_left
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) {i j : ι} (hij : i ≠ j) :
    truncated2FieldDerivSummand G p i j i =
    -2 * correlation G p {i} * truncated2 G p i j := by
  unfold truncated2FieldDerivSummand truncated2
  have h1 : symmDiff ({i, j} : Finset ι) {i} = {j} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h | rfl, hi⟩ | ⟨rfl, h⟩)
      · exact absurd h hi
      · rfl
      · exact absurd (Or.inl rfl) h
    · intro rfl; exact Or.inl ⟨Or.inr rfl, Ne.symm hij⟩
  have h2 : symmDiff ({i} : Finset ι) {i} = (∅ : Finset ι) := symmDiff_self _
  have h3 : symmDiff ({j} : Finset ι) {i} = {j, i} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, Ne.symm hij⟩
      · exact Or.inr ⟨rfl, hij⟩
  rw [h1, h2, h3]
  simp only [correlation_empty]
  have h4 : ({j, i} : Finset ι) = {i, j} := Finset.pair_comm j i
  rw [h4]
  ring

/-- For `k = j` (with `i ≠ j`), the summand equals `-2 * corr({j}) * truncated2`. -/
private lemma truncated2FieldDerivSummand_of_eq_right
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) {i j : ι} (hij : i ≠ j) :
    truncated2FieldDerivSummand G p i j j =
    -2 * correlation G p {j} * truncated2 G p i j := by
  unfold truncated2FieldDerivSummand truncated2
  have h1 : symmDiff ({i, j} : Finset ι) {j} = {i} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h | rfl, hj⟩ | ⟨rfl, h⟩)
      · exact h
      · exact absurd rfl hj
      · exact absurd (Or.inr rfl) h
    · intro rfl; exact Or.inl ⟨Or.inl rfl, hij⟩
  have h2 : symmDiff ({i} : Finset ι) {j} = {i, j} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hij⟩
      · exact Or.inr ⟨rfl, Ne.symm hij⟩
  have h3 : symmDiff ({j} : Finset ι) {j} = (∅ : Finset ι) := symmDiff_self _
  rw [h1, h2, h3]
  simp only [correlation_empty]
  ring

/-- Each summand is nonpositive for ferromagnetic `p` with `hf.hh ≥ 0`, `i ≠ j`. -/
private lemma truncated2FieldDerivSummand_nonpos
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {i j : ι} (hij : i ≠ j) (k : ι) :
    truncated2FieldDerivSummand G p i j k ≤ 0 := by
  by_cases hki : k = i
  · rw [hki, truncated2FieldDerivSummand_of_eq_left G p hij]
    apply mul_nonpos_of_nonpos_of_nonneg
    · apply mul_nonpos_of_nonpos_of_nonneg
      · norm_num
      · exact gks_first G p hf _
    · exact truncated2_nonneg G p hf i j
  · by_cases hkj : k = j
    · rw [hkj, truncated2FieldDerivSummand_of_eq_right G p hij]
      apply mul_nonpos_of_nonpos_of_nonneg
      · apply mul_nonpos_of_nonpos_of_nonneg
        · norm_num
        · exact gks_first G p hf _
      · exact truncated2_nonneg G p hf i j
    · rw [truncated2FieldDerivSummand_of_not_mem G p hki hkj]
      exact ghs_inequality G p hf i j k hij (Ne.symm hkj) (Ne.symm hki)

/-- The h-derivative of `truncated2 G (⟨J, h, β⟩) i j` equals `β * Σₖ summand`. -/
private lemma hasDerivAt_truncated2_field_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j : ι) :
    HasDerivAt (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j)
      (β * ∑ k : ι, truncated2FieldDerivSummand G (⟨J, h, β⟩ : IsingParams ℝ) i j k) h := by
  unfold truncated2
  have h_ij := hasDerivAt_correlation_field G J h β {i, j}
  have h_i := hasDerivAt_correlation_field G J h β {i}
  have h_j := hasDerivAt_correlation_field G J h β {j}
  have hd := h_ij.sub (h_i.mul h_j)
  convert hd using 1
  set p := (⟨J, h, β⟩ : IsingParams ℝ)
  rw [gibbsExpectation_spinProd_mul_mag G p {i, j},
      gibbsExpectation_spinProd_mul_mag G p {i},
      gibbsExpectation_spinProd_mul_mag G p {j},
      gibbsExpectation_totalMag_eq_sum G p]
  unfold truncated2FieldDerivSummand
  -- Split sums (forward), then factor out constants (backward), then ring identity
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- **GHS consequence (Step 124)**: The truncated 2-point function `⟨σᵢ; σⱼ⟩_T` is antitone
in `h` on `[0, ∞)` for distinct sites `i ≠ j` and ferromagnetic coupling `J ≥ 0`, `β > 0`.

`d/dh ⟨σᵢ; σⱼ⟩_T = β Σₖ (GHS-term_k) ≤ 0`:
each summand equals `truncated3(i,j,k) ≤ 0` (distinct) or
`-2 corr({m}) · truncated2(i,j) ≤ 0` (degenerate).

Reference: Glimm–Jaffe §4.3, Cor. 4.3.4 (GHS inequality);
Friedli–Velenik §3.6.3 (consequences). -/
theorem truncated2_antitoneOn_h_of_ne
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) {i j : ι} (hij : i ≠ j) :
    AntitoneOn (fun h => truncated2 G (⟨J, h, β⟩ : IsingParams ℝ) i j) (Set.Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
  · intro h _
    exact (hasDerivAt_truncated2_field_eq G J h β i j).continuousAt.continuousWithinAt
  · intro h hh
    rw [interior_Ici] at hh ⊢
    exact (hasDerivAt_truncated2_field_eq G J h β i j).hasDerivWithinAt
  · intro h hh
    rw [interior_Ici] at hh
    apply mul_nonpos_of_nonneg_of_nonpos hβ.le
    apply Finset.sum_nonpos
    intro k _
    exact truncated2FieldDerivSummand_nonpos G (⟨J, h, β⟩ : IsingParams ℝ)
      ⟨hJ, le_of_lt hh, hβ⟩ hij k

/-- **correlation ContinuousAt h** (Step 199):
For finite-volume Ising, `correlation G ⟨J, h, β⟩ A` is continuous in h at any h.

Proof: differentiable ⇒ continuous (from `hasDerivAt_correlation_field`). -/
theorem correlation_continuousAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (A : Finset ι) :
    ContinuousAt (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) A) h :=
  (hasDerivAt_correlation_field G J h β A).continuousAt

/-- **correlation Continuous in h** (Step 199, whole-ℝ). -/
theorem correlation_continuous_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) :
    Continuous (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) A) :=
  continuous_iff_continuousAt.mpr fun h => correlation_continuousAt_field G J h β A

/-- **correlation DifferentiableAt h** (Step 199). -/
theorem correlation_differentiableAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (A : Finset ι) :
    DifferentiableAt ℝ (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) A) h :=
  (hasDerivAt_correlation_field G J h β A).differentiableAt

/-- **correlation Differentiable in h** (Step 199, whole-ℝ). -/
theorem correlation_differentiable_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) :
    Differentiable ℝ (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) A) :=
  fun h => correlation_differentiableAt_field G J h β A

/-- **truncated2 ContinuousAt h** (Step 200):
For finite-volume Ising, `truncated2 G ⟨J, h, β⟩ i j` is continuous in h at any h.

Proof: `truncated2 = correlation {i,j} - correlation {i} · correlation {j}`,
each continuous in h. -/
theorem truncated2_continuousAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j : ι) :
    ContinuousAt (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j) h := by
  unfold truncated2
  exact (correlation_continuousAt_field G J h β _).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))

/-- **truncated2 Continuous in h** (Step 200, whole-ℝ). -/
theorem truncated2_continuous_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    Continuous (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j) :=
  continuous_iff_continuousAt.mpr fun h => truncated2_continuousAt_field G J h β i j

/-- **truncated2 DifferentiableAt h** (Step 200):
At any h, truncated2 has a derivative via product rule. -/
theorem truncated2_differentiableAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j : ι) :
    DifferentiableAt ℝ (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j) h := by
  unfold truncated2
  exact (correlation_differentiableAt_field G J h β _).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))

/-- **truncated2 Differentiable in h** (Step 200, whole-ℝ). -/
theorem truncated2_differentiable_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    Differentiable ℝ (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j) :=
  fun h => truncated2_differentiableAt_field G J h β i j

/-- **truncated2 hasDerivAt in h with explicit value** (Step 242):
For any finite-volume Ising at any `(J, h, β)`, `truncated2 G ⟨J, h, β⟩ i j`
has an h-derivative given by the product rule. This completes the truncated2
explicit-derivative trio (truncated2_hasDerivAt_beta at h = 0, truncated2_hasDerivAt_J
at any h, truncated2_hasDerivAt_field at any J, β). -/
theorem truncated2_hasDerivAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j : ι) :
    HasDerivAt (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j)
      (deriv (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) {i, j}) h -
       (deriv (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) {i}) h *
        correlation G (⟨J, h, β⟩ : IsingParams ℝ) {j} +
        correlation G (⟨J, h, β⟩ : IsingParams ℝ) {i} *
        deriv (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) {j}) h))
      h := by
  unfold truncated2
  have hij := hasDerivAt_correlation_field G J h β {i, j}
  have hi := hasDerivAt_correlation_field G J h β {i}
  have hj := hasDerivAt_correlation_field G J h β {j}
  have h_prod := hi.mul hj
  have h_diff := hij.sub h_prod
  rw [hij.deriv, hi.deriv, hj.deriv] at *
  exact h_diff

/-! ## Step 254: free energy h-derivative -/

/-- **Free energy h-derivative** (Step 254):
For any `(J, h, β)` and finite-volume Ising:

  `d/dh freeEnergy(h) = |ι|⁻¹ · β · gibbsExpectation(totalMagnetization)`

since `freeEnergy = |ι|⁻¹ · log(partitionFunction)` and
`d/dh log(Z) = Z'(h)/Z(h) = β·⟨M⟩` by the partition function h-derivative
(`hasDerivAt_partitionFunction_field`).

Reference: Glimm–Jaffe §17.6 / §4.6; standard thermodynamic identity
(magnetization per site = β⁻¹ · d/dh log(Z) / |ι|). -/
theorem hasDerivAt_freeEnergy_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun h' => freeEnergy G (⟨J, h', β⟩ : IsingParams ℝ))
      ((Fintype.card ι : ℝ)⁻¹ *
        gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ)
          (fun σ => β * totalMagnetization σ)) h := by
  set p := (⟨J, h, β⟩ : IsingParams ℝ)
  have hZpos : 0 < partitionFunction G p := partitionFunction_pos G p
  have hZne : partitionFunction G p ≠ 0 := hZpos.ne'
  have hZderiv := hasDerivAt_partitionFunction_field G J h β
  have hlogZ : HasDerivAt (fun h' => Real.log (partitionFunction G (⟨J, h', β⟩ : IsingParams ℝ)))
      ((∑ σ, β * totalMagnetization σ * boltzmannWeight G p σ) / partitionFunction G p) h := by
    have h := hZderiv.log hZne
    convert h using 1
  have hfreeE : (fun h' => freeEnergy G (⟨J, h', β⟩ : IsingParams ℝ)) =
      (fun h' => (Fintype.card ι : ℝ)⁻¹ *
        Real.log (partitionFunction G (⟨J, h', β⟩ : IsingParams ℝ))) := by
    funext h'; rfl
  rw [hfreeE]
  have h := hlogZ.const_mul ((Fintype.card ι : ℝ)⁻¹)
  convert h using 1
  unfold gibbsExpectation
  field_simp

/-- **freeEnergy Continuous in h** (Step 256). -/
theorem freeEnergy_continuous_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) :
    Continuous (fun h' => freeEnergy G (⟨J, h', β⟩ : IsingParams ℝ)) :=
  continuous_iff_continuousAt.mpr fun h =>
    (hasDerivAt_freeEnergy_field G J h β).continuousAt

/-- **freeEnergy Differentiable in h** (Step 256). -/
theorem freeEnergy_differentiable_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) :
    Differentiable ℝ (fun h' => freeEnergy G (⟨J, h', β⟩ : IsingParams ℝ)) :=
  fun h => (hasDerivAt_freeEnergy_field G J h β).differentiableAt

/-- **truncated3 ContinuousAt h** (Step 202).
truncated3 is a polynomial in correlation values, each continuous in h. -/
theorem truncated3_continuousAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j k : ι) :
    ContinuousAt (fun h' => truncated3 G (⟨J, h', β⟩ : IsingParams ℝ) i j k) h := by
  unfold truncated3
  exact (((correlation_continuousAt_field G J h β _).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))
    |>.add (((continuousAt_const).mul (correlation_continuousAt_field G J h β _)).mul
      (correlation_continuousAt_field G J h β _) |>.mul
      (correlation_continuousAt_field G J h β _))

/-- **truncated3 Continuous in h** (Step 202, whole-ℝ). -/
theorem truncated3_continuous_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k : ι) :
    Continuous (fun h' => truncated3 G (⟨J, h', β⟩ : IsingParams ℝ) i j k) :=
  continuous_iff_continuousAt.mpr fun h => truncated3_continuousAt_field G J h β i j k

/-- **truncated3 DifferentiableAt h** (Step 202). -/
theorem truncated3_differentiableAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j k : ι) :
    DifferentiableAt ℝ (fun h' => truncated3 G (⟨J, h', β⟩ : IsingParams ℝ) i j k) h := by
  unfold truncated3
  exact (((correlation_differentiableAt_field G J h β _).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))
    |>.add (((differentiableAt_const _).mul
      (correlation_differentiableAt_field G J h β _)).mul
      (correlation_differentiableAt_field G J h β _) |>.mul
      (correlation_differentiableAt_field G J h β _))

/-- **truncated3 Differentiable in h** (Step 202, whole-ℝ). -/
theorem truncated3_differentiable_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k : ι) :
    Differentiable ℝ (fun h' => truncated3 G (⟨J, h', β⟩ : IsingParams ℝ) i j k) :=
  fun h => truncated3_differentiableAt_field G J h β i j k

/-- **truncated4 ContinuousAt h** (Step 204).
truncated4 is a polynomial in correlation values, each continuous in h. -/
theorem truncated4_continuousAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j k l : ι) :
    ContinuousAt (fun h' => truncated4 G (⟨J, h', β⟩ : IsingParams ℝ) i j k l) h := by
  unfold truncated4
  exact (((correlation_continuousAt_field G J h β _).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))

/-- **truncated4 Continuous in h** (Step 204, whole-ℝ). -/
theorem truncated4_continuous_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k l : ι) :
    Continuous (fun h' => truncated4 G (⟨J, h', β⟩ : IsingParams ℝ) i j k l) :=
  continuous_iff_continuousAt.mpr fun h => truncated4_continuousAt_field G J h β i j k l

/-- **truncated4 DifferentiableAt h** (Step 204). -/
theorem truncated4_differentiableAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j k l : ι) :
    DifferentiableAt ℝ (fun h' => truncated4 G (⟨J, h', β⟩ : IsingParams ℝ) i j k l) h := by
  unfold truncated4
  exact (((correlation_differentiableAt_field G J h β _).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))

/-- **truncated4 Differentiable in h** (Step 204, whole-ℝ). -/
theorem truncated4_differentiable_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k l : ι) :
    Differentiable ℝ (fun h' => truncated4 G (⟨J, h', β⟩ : IsingParams ℝ) i j k l) :=
  fun h => truncated4_differentiableAt_field G J h β i j k l

end IsingModel
