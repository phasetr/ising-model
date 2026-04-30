import IsingModel.GibbsMeasure
import IsingModel.Inequalities.NonnegCorrelations
import IsingModel.Inequalities.GKS
import IsingModel.Inequalities.GHS
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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

/-! ## Lebowitz upper bound on the β-derivative (Step 117b) -/

omit [Fintype ι] in
/-- **symmDiff of two disjoint pairs**: when `r,s,u,v` are pairwise
distinct, `{r,s} △ {u,v} = {r,s,u,v}` as Finsets. -/
private lemma symmDiff_pairs_of_disjoint
    {r s u v : ι} (hrs : r ≠ s) (hru : r ≠ u) (hrv : r ≠ v)
    (hsu : s ≠ u) (hsv : s ≠ v) (huv : u ≠ v) :
    symmDiff ({r, s} : Finset ι) {u, v} = {r, s, u, v} := by
  have h_disj : Disjoint ({r, s} : Finset ι) {u, v} := by
    apply Finset.disjoint_left.mpr
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro x (rfl | rfl) (rfl | rfl)
    · exact absurd rfl hru
    · exact absurd rfl hrv
    · exact absurd rfl hsu
    · exact absurd rfl hsv
  rw [symmDiff_def, Finset.sdiff_eq_self_iff_disjoint.mpr h_disj,
      Finset.sdiff_eq_self_iff_disjoint.mpr h_disj.symm]
  ext x
  rw [Finset.sup_eq_union]
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **Lebowitz bound for the β-derivative summand at non-degenerate edges**
(GJ §17.5 p.312):
For pairwise distinct sites `r,s,u,v` and ferromagnetic `h=0`:

  `⟨σ_r σ_s σ_u σ_v⟩ − ⟨σ_r σ_s⟩·⟨σ_u σ_v⟩`
  `  ≤ ⟨σ_r σ_u⟩·⟨σ_s σ_v⟩ + ⟨σ_r σ_v⟩·⟨σ_s σ_u⟩`

which bounds the summand `corr({r,s}△{u,v}) − corr({r,s})·corr({u,v})`.

Proof: `symmDiff {r,s} {u,v} = {r,s,u,v}` (disjoint) + Cor 4.3.3.

Reference: Glimm–Jaffe §17.5 p.312 (2nd ed.); Cor. 4.3.3 (Lebowitz). -/
theorem summand_le_lebowitz_of_disjoint
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (r s u v : ι) (hrs : r ≠ s) (hru : r ≠ u) (hrv : r ≠ v)
    (hsu : s ≠ u) (hsv : s ≠ v) (huv : u ≠ v) :
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff {r, s} {u, v}) -
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} *
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {u, v} ≤
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} *
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {s, v} +
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, v} *
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {s, u} := by
  rw [symmDiff_pairs_of_disjoint hrs hru hrv hsu hsv huv]
  have h := cor_4_3_3 G J β hf r s u v hrs hru hrv hsu hsv huv
  unfold truncated4 at h
  linarith

/-- **Upper bound on each derivative summand**:
For any edge `e ∈ G.edgeFinset` and distinct `r, s`, the summand
`corr({r,s}△{e₁,e₂}) − corr({r,s})·corr({e₁,e₂})` in the
β-derivative formula satisfies a one-sided bound ≤ 1.

Proof: GKS-I gives all correlations ≥ 0, and all correlations ≤ 1
(from `abs_correlation_le_one`). The summand is ≥ 0 by GKS-II and ≤ 1.

Reference: Glimm–Jaffe §17.5 p.312 (2nd ed.). -/
private lemma summand_le_one
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (A B : Finset ι) :
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff A B) -
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A *
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) B ≤ 1 := by
  have h_sd : |correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff A B)| ≤ 1 :=
    abs_correlation_le_one G ⟨J, 0, β⟩ (symmDiff A B)
  have h_A : 0 ≤ correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A :=
    gks_first G ⟨J, 0, β⟩ hf A
  have h_B : 0 ≤ correlation G (⟨J, 0, β⟩ : IsingParams ℝ) B :=
    gks_first G ⟨J, 0, β⟩ hf B
  have h_pos : 0 ≤ correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff A B) :=
    gks_first G ⟨J, 0, β⟩ hf (symmDiff A B)
  linarith [abs_le.mp h_sd, mul_nonneg h_A h_B]

/-- **Lebowitz upper bound on β-derivative of 2-point function** (GJ §17.5 p.312):
The derivative `d/dβ ⟨σ_r σ_s⟩_β` at `h = 0` satisfies:

  `d/dβ ⟨σ_r σ_s⟩ ≤ J · Σ_{e∈E} [⟨σ_r σ_{e₁}⟩·⟨σ_s σ_{e₂}⟩ + ⟨σ_r σ_{e₂}⟩·⟨σ_s σ_{e₁}⟩]`
  `                  + J · |E(G)|`

The extra `J·|E(G)|` term is a coarse upper bound for degenerate edges
(those incident to `r` or `s`), for which the standard Lebowitz bound does not
apply directly. Since at most `deg(r) + deg(s)` edges are degenerate, a tighter
bound is `J·(deg(r) + deg(s))` — for ℤ^d nearest-neighbour, this is `J·4d`.

Reference: Glimm–Jaffe §17.5 pp.311–312 (2nd ed.); Cor. 4.3.3 (Lebowitz). -/
theorem correlation_beta_deriv_le_lebowitz
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (r s : ι) (hrs : r ≠ s) :
    let p := (⟨J, 0, β⟩ : IsingParams ℝ)
    ∃ d : ℝ,
      HasDerivAt (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) d β ∧
      d ≤ J * ∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v =>
              correlation G p {r, u} * correlation G p {s, v} +
              correlation G p {r, v} * correlation G p {s, u},
            fun u v => by ring⟩ e
        + J * G.edgeFinset.card := by
  intro p
  have hf : Ferromagnetic p := ⟨hJ, le_refl 0, hβ⟩
  refine ⟨_, hasDerivAt_correlation_beta G J β {r, s}, ?_⟩
  -- Goal: J * Σ_e [summand_e] ≤ J * Σ_e [lebowitz_e] + J * |E|
  have hcard : (G.edgeFinset.card : ℝ) = ∑ _ ∈ G.edgeFinset, (1 : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard, ← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ hJ
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
  have huv : u ≠ v := by
    intro heq; subst heq; exact (SimpleGraph.mem_edgeFinset.mp he).ne rfl
  simp only [Sym2.lift_mk]
  -- summand_e ≤ lebowitz_e + 1
  -- Use Lebowitz if non-degenerate; trivial bound otherwise
  by_cases hru : r = u
  · subst hru
    -- Degenerate: r = u. summand ≤ 1 ≤ lebowitz + 1
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
  -- Non-degenerate case: r,s,u,v pairwise distinct
  have h_le := summand_le_lebowitz_of_disjoint G J β hf r s u v hrs hru hrv hsu hsv huv
  linarith [show (0 : ℝ) ≤ 1 from zero_le_one]

/-- **Tight Lebowitz upper bound on β-derivative of 2-point function** (Step 154, GJ §17.5):
The derivative `d/dβ ⟨σ_r σ_s⟩_β` satisfies:
`d ≤ J · ∑_{e∈E} lebowitz_e + J · |{e ∈ E(G) : r ∈ e ∨ s ∈ e}|`.

Improves `correlation_beta_deriv_le_lebowitz` (Step 117b): the error is now proportional
to the number of edges **incident to r or s** only (≤ deg(r) + deg(s) ≤ 4d for ℤ^d),
not the full edge count |E(G)|. This makes the bound usable in the infinite-volume limit
where |E| → ∞ but the number of incident edges stays bounded.

Key insight: for non-degenerate edges {u,v} (r,s,u,v all distinct), `summand ≤ lebowitz`
exactly (no +1). Only degenerate edges (incident to r or s) need the `+1` correction.

Reference: Glimm–Jaffe §17.5 pp.311–312. -/
theorem correlation_beta_deriv_le_lebowitz_tight
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (r s : ι) (hrs : r ≠ s) :
    let p := (⟨J, 0, β⟩ : IsingParams ℝ)
    ∃ d : ℝ,
      HasDerivAt (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) d β ∧
      d ≤ J * ∑ e ∈ G.edgeFinset,
              Sym2.lift ⟨fun u v =>
                  correlation G p {r, u} * correlation G p {s, v} +
                  correlation G p {r, v} * correlation G p {s, u},
                fun u v => by ring⟩ e
          + J * (G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e)).card := by
  classical
  intro p
  have hf : Ferromagnetic p := ⟨hJ, le_refl 0, hβ⟩
  refine ⟨_, hasDerivAt_correlation_beta G J β {r, s}, ?_⟩
  -- Abbreviate the summand and Lebowitz functions
  set leb : Sym2 ι → ℝ := fun e =>
    Sym2.lift ⟨fun u v => correlation G p {r, u} * correlation G p {s, v} +
                           correlation G p {r, v} * correlation G p {s, u},
              fun u v => by ring⟩ e
  set summ : Sym2 ι → ℝ := fun e =>
    Sym2.lift ⟨fun u v => correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff {r, s} {u, v}) -
                           correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} *
                           correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
              fun u v => by simp [Finset.pair_comm v u]⟩ e
  -- Step 1: bound ∑_e summ ≤ ∑_e leb + |{e: deg}|
  set deg := G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e)
  have h_leb_nn : ∀ e ∈ G.edgeFinset, 0 ≤ leb e := fun e _ => by
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    exact add_nonneg (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
                     (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
  have h_bound : ∑ e ∈ G.edgeFinset, summ e ≤ ∑ e ∈ G.edgeFinset, leb e + deg.card := by
    have split := (Finset.sum_filter_add_sum_filter_not G.edgeFinset
      (fun e => r ∈ e ∨ s ∈ e) summ).symm
    rw [split]
    -- deg part: ∑_{deg} summ ≤ ∑_{deg} 1 = |deg|
    -- non-deg part: ∑_{non-deg} summ ≤ ∑_{non-deg} leb ≤ ∑_e leb
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
  calc J * ∑ e ∈ G.edgeFinset, summ e
      ≤ J * (∑ e ∈ G.edgeFinset, leb e + ↑(#deg)) := mul_le_mul_of_nonneg_left h_bound hJ
    _ = J * G.edgeFinset.sum leb + J * ↑(#deg) := by ring

/-! ## Continuity corollaries (Step 120) -/

/-- **Correlation is continuous in β**:
`fun β' => correlation G (⟨J, 0, β'⟩) A` is continuous at `β`.

Proof: differentiable ⇒ continuous (from `hasDerivAt_correlation_beta`).

Reference: GJ §17.5 (implicit); used in Step 120 for pseudoMass composition. -/
theorem correlation_continuousAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) :
    ContinuousAt (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) A) β :=
  (hasDerivAt_correlation_beta G J β A).continuousAt

/-- **truncated2 is continuous in β at h = 0** (Step 188 helper):
`fun β' => truncated2 G (⟨J, 0, β'⟩) i j` is continuous at β.

At h = 0, `truncated2 = correlation - correlation * correlation`, each continuous in β. -/
theorem truncated2_continuousAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    ContinuousAt (fun β' => truncated2 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j) β := by
  unfold truncated2
  exact (correlation_continuousAt_beta G J β _).sub
    ((correlation_continuousAt_beta G J β _).mul (correlation_continuousAt_beta G J β _))

/-- **truncated2 has a β-derivative at h = 0** (Step 191):
For any finite-volume Ising at h = 0, `truncated2 G ⟨J, 0, β⟩ i j` has a derivative in β.

At h = 0, `truncated2 = correlation {i,j} - correlation {i} · correlation {j}`. Each
correlation has a derivative (`hasDerivAt_correlation_beta`), so the product rule gives
the derivative for truncated2. -/
theorem truncated2_hasDerivAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    HasDerivAt (fun β' => truncated2 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j)
      (deriv (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {i, j}) β -
       (deriv (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {i}) β *
        correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {j} +
        correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {i} *
        deriv (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {j}) β))
      β := by
  unfold truncated2
  have hij := hasDerivAt_correlation_beta G J β {i, j}
  have hi := hasDerivAt_correlation_beta G J β {i}
  have hj := hasDerivAt_correlation_beta G J β {j}
  have h_prod := hi.mul hj
  have h_diff := hij.sub h_prod
  -- Convert HasDerivAt's value to use deriv
  rw [hij.deriv, hi.deriv, hj.deriv] at *
  exact h_diff

/-- **correlation is Continuous in β over the whole ℝ at h = 0** (Step 193).
Strengthens `correlation_continuousAt_beta` from `ContinuousAt` to `Continuous`. -/
theorem correlation_continuous_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (A : Finset ι) :
    Continuous (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) A) :=
  continuous_iff_continuousAt.mpr fun β => correlation_continuousAt_beta G J β A

/-- **truncated2 is Continuous in β over the whole ℝ at h = 0** (Step 193).
Strengthens `truncated2_continuousAt_beta` to `Continuous`. -/
theorem truncated2_continuous_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i j : ι) :
    Continuous (fun β' => truncated2 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j) :=
  continuous_iff_continuousAt.mpr fun β => truncated2_continuousAt_beta G J β i j

/-- **correlation is Differentiable in β at h = 0** (Step 193).
Strengthens `hasDerivAt_correlation_beta` (single-point) to `Differentiable`. -/
theorem correlation_differentiable_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (A : Finset ι) :
    Differentiable ℝ (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) A) :=
  fun β => (hasDerivAt_correlation_beta G J β A).differentiableAt

/-- **truncated2 is Differentiable in β at h = 0** (Step 193). -/
theorem truncated2_differentiable_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i j : ι) :
    Differentiable ℝ (fun β' => truncated2 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j) :=
  fun β => (truncated2_hasDerivAt_beta G J β i j).differentiableAt

/-- **truncated3 is ContinuousAt β at h = 0** (Step 203).
truncated3 is a polynomial in correlation values, each continuous in β at h = 0. -/
theorem truncated3_continuousAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k : ι) :
    ContinuousAt (fun β' => truncated3 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j k) β := by
  unfold truncated3
  exact (((correlation_continuousAt_beta G J β _).sub
    ((correlation_continuousAt_beta G J β _).mul (correlation_continuousAt_beta G J β _))).sub
    ((correlation_continuousAt_beta G J β _).mul (correlation_continuousAt_beta G J β _))).sub
    ((correlation_continuousAt_beta G J β _).mul (correlation_continuousAt_beta G J β _))
    |>.add (((continuousAt_const).mul (correlation_continuousAt_beta G J β _)).mul
      (correlation_continuousAt_beta G J β _) |>.mul
      (correlation_continuousAt_beta G J β _))

/-- **truncated3 Continuous in β at h = 0** (Step 203, whole-ℝ). -/
theorem truncated3_continuous_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i j k : ι) :
    Continuous (fun β' => truncated3 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j k) :=
  continuous_iff_continuousAt.mpr fun β => truncated3_continuousAt_beta G J β i j k

/-- **truncated3 DifferentiableAt β at h = 0** (Step 203). -/
theorem truncated3_differentiableAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k : ι) :
    DifferentiableAt ℝ (fun β' => truncated3 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j k) β := by
  unfold truncated3
  -- Combine 4 differentiable correlation pieces via product rule
  have h1 := (hasDerivAt_correlation_beta G J β {i, j, k}).differentiableAt
  have h2 := ((hasDerivAt_correlation_beta G J β {i}).differentiableAt).mul
              (hasDerivAt_correlation_beta G J β {j, k}).differentiableAt
  have h3 := ((hasDerivAt_correlation_beta G J β {j}).differentiableAt).mul
              (hasDerivAt_correlation_beta G J β {i, k}).differentiableAt
  have h4 := ((hasDerivAt_correlation_beta G J β {k}).differentiableAt).mul
              (hasDerivAt_correlation_beta G J β {i, j}).differentiableAt
  have h5 := (((differentiableAt_const (2 : ℝ)).mul
    (hasDerivAt_correlation_beta G J β {i}).differentiableAt).mul
    (hasDerivAt_correlation_beta G J β {j}).differentiableAt).mul
    (hasDerivAt_correlation_beta G J β {k}).differentiableAt
  exact (((h1.sub h2).sub h3).sub h4).add h5

/-- **truncated3 Differentiable in β at h = 0** (Step 203, whole-ℝ). -/
theorem truncated3_differentiable_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i j k : ι) :
    Differentiable ℝ (fun β' => truncated3 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j k) :=
  fun β => truncated3_differentiableAt_beta G J β i j k

/-! ## Monotonicity in β (Step 122): GKS-II-based bound -/

/-- The β-derivative of two-point correlations is nonneg (infinitesimal form of β-monotonicity).

`d/dβ ⟨σ^A⟩_β = J · Σ_e (⟨σ^{AΔe}⟩ − ⟨σ^A⟩·⟨σ^e⟩) ≥ 0`

by GKS-II: each term `⟨σ^{AΔe}⟩ − ⟨σ^A⟩·⟨σ^e⟩ ≥ 0` for ferromagnetic `h = 0`.
This is the infinitesimal form underlying the monotonicity of correlations in β.

Reference: Friedli–Velenik §3.7, Lemma 3.31 part 2 (p. 107) — adapted to general `σ^A`;
Glimm–Jaffe §17.5 pp. 345–347. -/
theorem correlation_beta_deriv_nonneg
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι)
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) :
    0 ≤ J * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun r s =>
          correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff A {r, s}) -
          correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A *
          correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s},
          fun r s => by simp [Finset.pair_comm s r]⟩ e := by
  apply mul_nonneg hf.hJ
  apply Finset.sum_nonneg
  intro e _
  obtain ⟨⟨r, s⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  linarith [gks_second G (⟨J, 0, β⟩ : IsingParams ℝ) hf A {r, s}]

/-- **Correlations are monotone in β** (on `{β ≥ 0}`):
`β₁ ≤ β₂ → correlation G (⟨J, 0, β₁⟩) A ≤ correlation G (⟨J, 0, β₂⟩) A`

for ferromagnetic coupling `J ≥ 0`.

Proof: mean value theorem applied to `β ↦ correlation` whose derivative
is nonneg by GKS-II (`correlation_beta_deriv_nonneg`).

Reference: Friedli–Velenik §3.7, Lemma 3.31 part 2 (p. 107);
Glimm–Jaffe §17.5 pp. 345–347. -/
theorem correlation_monotoneOn_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (A : Finset ι) :
    MonotoneOn (fun β => correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A) (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
  · -- ContinuousOn: from HasDerivAt ⇒ ContinuousAt ⇒ ContinuousWithinAt
    intro β _
    exact (hasDerivAt_correlation_beta G J β A).continuousAt.continuousWithinAt
  · -- HasDerivWithinAt on interior (Ici 0) = Ioi 0
    intro β hβ
    rw [interior_Ici] at hβ ⊢
    exact (hasDerivAt_correlation_beta G J β A).hasDerivWithinAt
  · -- derivative ≥ 0 on interior
    intro β hβ
    rw [interior_Ici] at hβ
    exact correlation_beta_deriv_nonneg G J β A ⟨hJ, le_refl 0, hβ⟩

end IsingModel
