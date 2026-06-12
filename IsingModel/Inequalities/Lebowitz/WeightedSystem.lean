import IsingModel.Inequalities.Lebowitz.LebowitzFour

/-!
# Duplicate-variable systems over an abstract positive weight

The fourfold and twofold duplicate systems of GJ §4.3, generalised from the
uniform-coupling Boltzmann weight to an abstract positive weight
`w : Config ι → ℝ`. The factorisation proofs are verbatim those of
`FourfoldSystem.lean` / `DoubleSystem.lean` with `boltzmannWeight G p`
replaced by `w`; positivity enters only through the hypothesis `0 < w σ`.

This layer exists to discharge the Lebowitz corollaries for models with
non-uniform ferromagnetic couplings (the scaled model `J_e = sJ` on a
distinguished edge set, `cor_4_3_3_scaled` in
`BallBoundarySimonLieb/Tight.lean`): the whole `t`/`q` bracket chain
depends on the weight only through the product structure and
`HasNonnegUMoments` of the fourfold product weight.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.3, pp. 59–62
-/

namespace IsingModel

namespace Lebowitz

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-! ## The fourfold system over an abstract weight -/

/-- The fourfold product of an abstract weight: `w(ξ)w(χ)w(ξ')w(χ')`. -/
noncomputable def wQuadWeight (w : Config ι → ℝ) (v : QuadConfig ι) : ℝ :=
  w v.1 * w v.2.1 * w v.2.2.1 * w v.2.2.2

/-- The single-copy partition function of an abstract weight. -/
noncomputable def wPartition (w : Config ι → ℝ) : ℝ := ∑ σ : Config ι, w σ

/-- The fourfold partition function of an abstract weight. -/
noncomputable def wQuadPartition (w : Config ι → ℝ) : ℝ :=
  ∑ v : QuadConfig ι, wQuadWeight w v

/-- The single-copy partition function of a positive weight is positive. -/
theorem wPartition_pos (w : Config ι → ℝ) (hw : ∀ σ, 0 < w σ) :
    0 < wPartition w :=
  Finset.sum_pos (fun σ _ => hw σ) Finset.univ_nonempty

/-- **The fourfold partition function factorises**: `Z₄(w) = Z(w)⁴`. -/
theorem wQuadPartition_eq (w : Config ι → ℝ) :
    wQuadPartition w = wPartition w ^ 4 := by
  unfold wQuadPartition wQuadWeight wPartition
  simp only [Fintype.sum_prod_type]
  have h4 : ∀ σ τ ρ : Config ι,
      ∑ κ : Config ι, w σ * w τ * w ρ * w κ
      = w σ * w τ * w ρ * ∑ κ : Config ι, w κ := by
    intro σ τ ρ
    rw [← Finset.mul_sum]
  simp_rw [h4]
  have h3 : ∀ σ τ : Config ι,
      ∑ ρ : Config ι, w σ * w τ * w ρ * ∑ κ : Config ι, w κ
      = w σ * w τ * (∑ ρ : Config ι, w ρ) * ∑ κ : Config ι, w κ := by
    intro σ τ
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [h3]
  have h2 : ∀ σ : Config ι,
      ∑ τ : Config ι, w σ * w τ * (∑ ρ : Config ι, w ρ) * ∑ κ : Config ι, w κ
      = w σ * (∑ τ : Config ι, w τ) * (∑ ρ : Config ι, w ρ) *
        ∑ κ : Config ι, w κ := by
    intro σ
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [h2]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- The fourfold partition function of a positive weight is positive. -/
theorem wQuadPartition_pos (w : Config ι → ℝ) (hw : ∀ σ, 0 < w σ) :
    0 < wQuadPartition w := by
  rw [wQuadPartition_eq]
  exact pow_pos (wPartition_pos w hw) 4

/-- The single-copy expectation of an abstract weight. -/
noncomputable def wExpectation (w : Config ι → ℝ) (F : Config ι → ℝ) : ℝ :=
  (wPartition w)⁻¹ * ∑ σ : Config ι, F σ * w σ

/-- The fourfold expectation of an abstract weight. -/
noncomputable def wQuadExpectation (w : Config ι → ℝ)
    (F : QuadConfig ι → ℝ) : ℝ :=
  (wQuadPartition w)⁻¹ * ∑ v : QuadConfig ι, F v * wQuadWeight w v

/-- **Factorisation of fourfold expectations of per-copy products** over an
abstract positive weight: `⟨F₁(ξ)F₂(χ)F₃(ξ')F₄(χ')⟩₄ = ⟨F₁⟩⟨F₂⟩⟨F₃⟩⟨F₄⟩`. -/
theorem wQuadExpectation_factor (w : Config ι → ℝ) (hw : ∀ σ, 0 < w σ)
    (F₁ F₂ F₃ F₄ : Config ι → ℝ) :
    wQuadExpectation w (fun v => F₁ v.1 * F₂ v.2.1 * F₃ v.2.2.1 * F₄ v.2.2.2)
      = wExpectation w F₁ * wExpectation w F₂ *
        wExpectation w F₃ * wExpectation w F₄ := by
  unfold wQuadExpectation wExpectation
  rw [wQuadPartition_eq]
  have hZ : wPartition w ≠ 0 := ne_of_gt (wPartition_pos w hw)
  have hsum : ∑ v : QuadConfig ι,
      (F₁ v.1 * F₂ v.2.1 * F₃ v.2.2.1 * F₄ v.2.2.2) * wQuadWeight w v
      = (∑ σ, F₁ σ * w σ) * (∑ σ, F₂ σ * w σ) *
        (∑ σ, F₃ σ * w σ) * (∑ σ, F₄ σ * w σ) := by
    unfold wQuadWeight
    simp only [Fintype.sum_prod_type]
    have h4 : ∀ σ τ ρ : Config ι,
        ∑ κ : Config ι, (F₁ σ * F₂ τ * F₃ ρ * F₄ κ) * (w σ * w τ * w ρ * w κ)
        = (F₁ σ * w σ) * (F₂ τ * w τ) * (F₃ ρ * w ρ) *
          ∑ κ : Config ι, F₄ κ * w κ := by
      intro σ τ ρ
      have hgr : ∀ κ : Config ι,
          (F₁ σ * F₂ τ * F₃ ρ * F₄ κ) * (w σ * w τ * w ρ * w κ)
          = (F₁ σ * w σ) * (F₂ τ * w τ) * (F₃ ρ * w ρ) * (F₄ κ * w κ) :=
        fun κ => by ring
      simp_rw [hgr, ← Finset.mul_sum]
    simp_rw [h4]
    have h3 : ∀ σ τ : Config ι,
        ∑ ρ : Config ι, (F₁ σ * w σ) * (F₂ τ * w τ) * (F₃ ρ * w ρ) *
          ∑ κ : Config ι, F₄ κ * w κ
        = (F₁ σ * w σ) * (F₂ τ * w τ) * (∑ ρ : Config ι, F₃ ρ * w ρ) *
          ∑ κ : Config ι, F₄ κ * w κ := by
      intro σ τ
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    simp_rw [h3]
    have h2 : ∀ σ : Config ι,
        ∑ τ : Config ι, (F₁ σ * w σ) * (F₂ τ * w τ) *
          (∑ ρ : Config ι, F₃ ρ * w ρ) * ∑ κ : Config ι, F₄ κ * w κ
        = (F₁ σ * w σ) * (∑ τ : Config ι, F₂ τ * w τ) *
          (∑ ρ : Config ι, F₃ ρ * w ρ) * ∑ κ : Config ι, F₄ κ * w κ := by
      intro σ
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    simp_rw [h2]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [hsum]
  field_simp


/-! ## The doubled system over an abstract weight -/

/-- The doubled product of an abstract weight: `w(ξ)w(χ)`. -/
noncomputable def wDoubleWeight (w : Config ι → ℝ) (d : DoubleConfig ι) : ℝ :=
  w d.1 * w d.2

/-- The doubled partition function of an abstract weight. -/
noncomputable def wDoublePartition (w : Config ι → ℝ) : ℝ :=
  ∑ d : DoubleConfig ι, wDoubleWeight w d

/-- **The doubled partition function factorises**: `Z₂(w) = Z(w)²`. -/
theorem wDoublePartition_eq (w : Config ι → ℝ) :
    wDoublePartition w = wPartition w ^ 2 := by
  unfold wDoublePartition wDoubleWeight wPartition
  rw [Fintype.sum_prod_type]
  have h1 : ∀ σ : Config ι,
      ∑ τ : Config ι, w σ * w τ = w σ * ∑ τ : Config ι, w τ := by
    intro σ
    rw [← Finset.mul_sum]
  simp_rw [h1]
  rw [← Finset.sum_mul]
  ring

/-- The doubled partition function of a positive weight is positive. -/
theorem wDoublePartition_pos (w : Config ι → ℝ) (hw : ∀ σ, 0 < w σ) :
    0 < wDoublePartition w := by
  rw [wDoublePartition_eq]
  exact pow_pos (wPartition_pos w hw) 2

/-- The doubled expectation of an abstract weight. -/
noncomputable def wDoubleExpectation (w : Config ι → ℝ)
    (F : DoubleConfig ι → ℝ) : ℝ :=
  (wDoublePartition w)⁻¹ * ∑ d : DoubleConfig ι, F d * wDoubleWeight w d

/-- **Factorisation of doubled expectations of per-copy products** over an
abstract positive weight: `⟨F₁(ξ)F₂(χ)⟩₂ = ⟨F₁⟩⟨F₂⟩`. -/
theorem wDoubleExpectation_factor (w : Config ι → ℝ) (hw : ∀ σ, 0 < w σ)
    (F₁ F₂ : Config ι → ℝ) :
    wDoubleExpectation w (fun d => F₁ d.1 * F₂ d.2)
      = wExpectation w F₁ * wExpectation w F₂ := by
  unfold wDoubleExpectation wExpectation
  rw [wDoublePartition_eq]
  have hZ : wPartition w ≠ 0 := ne_of_gt (wPartition_pos w hw)
  have hsum : ∑ d : DoubleConfig ι, (F₁ d.1 * F₂ d.2) * wDoubleWeight w d
      = (∑ σ, F₁ σ * w σ) * ∑ σ, F₂ σ * w σ := by
    unfold wDoubleWeight
    rw [Fintype.sum_prod_type]
    have h1 : ∀ σ : Config ι,
        ∑ τ : Config ι, (F₁ σ * F₂ τ) * (w σ * w τ)
          = (F₁ σ * w σ) * ∑ τ : Config ι, F₂ τ * w τ := by
      intro σ
      have hgr : ∀ τ : Config ι,
          (F₁ σ * F₂ τ) * (w σ * w τ) = (F₁ σ * w σ) * (F₂ τ * w τ) :=
        fun τ => by ring
      simp_rw [hgr, ← Finset.mul_sum]
    simp_rw [h1]
    rw [← Finset.sum_mul]
  rw [hsum]
  field_simp

/-- **Pair factorisation of the fourfold expectation** over an abstract
positive weight: `⟨F₁(ξ,χ)F₂(ξ',χ')⟩₄ = ⟨F₁⟩₂⟨F₂⟩₂`. -/
theorem wQuadExpectation_factor_pair (w : Config ι → ℝ) (hw : ∀ σ, 0 < w σ)
    (F₁ F₂ : DoubleConfig ι → ℝ) :
    wQuadExpectation w (fun v => F₁ (v.1, v.2.1) * F₂ (v.2.2.1, v.2.2.2))
      = wDoubleExpectation w F₁ * wDoubleExpectation w F₂ := by
  unfold wQuadExpectation wDoubleExpectation
  rw [wQuadPartition_eq, wDoublePartition_eq]
  have hZ : wPartition w ≠ 0 := ne_of_gt (wPartition_pos w hw)
  have hsum : ∑ v : QuadConfig ι,
      (F₁ (v.1, v.2.1) * F₂ (v.2.2.1, v.2.2.2)) * wQuadWeight w v
      = (∑ d : DoubleConfig ι, F₁ d * wDoubleWeight w d) *
        ∑ d : DoubleConfig ι, F₂ d * wDoubleWeight w d := by
    unfold wQuadWeight wDoubleWeight
    simp only [Fintype.sum_prod_type]
    have h4 : ∀ σ τ ρ : Config ι,
        ∑ κ : Config ι, (F₁ (σ, τ) * F₂ (ρ, κ)) * (w σ * w τ * w ρ * w κ)
        = (F₁ (σ, τ) * (w σ * w τ)) *
          ∑ κ : Config ι, F₂ (ρ, κ) * (w ρ * w κ) := by
      intro σ τ ρ
      have hgr : ∀ κ : Config ι,
          (F₁ (σ, τ) * F₂ (ρ, κ)) * (w σ * w τ * w ρ * w κ)
          = (F₁ (σ, τ) * (w σ * w τ)) * (F₂ (ρ, κ) * (w ρ * w κ)) :=
        fun κ => by ring
      simp_rw [hgr, ← Finset.mul_sum]
    simp_rw [h4]
    have h3 : ∀ σ τ : Config ι,
        ∑ ρ : Config ι, (F₁ (σ, τ) * (w σ * w τ)) *
          ∑ κ : Config ι, F₂ (ρ, κ) * (w ρ * w κ)
        = (F₁ (σ, τ) * (w σ * w τ)) *
          ∑ ρ : Config ι, ∑ κ : Config ι, F₂ (ρ, κ) * (w ρ * w κ) := by
      intro σ τ
      rw [← Finset.mul_sum]
    simp_rw [h3]
    simp_rw [← Finset.sum_mul]
  rw [hsum]
  field_simp

/-- **First-pair embedding** over an abstract positive weight: a doubled
observable of the first copy pair has the same fourfold and doubled
expectations. -/
theorem wQuadExpectation_fst_pair (w : Config ι → ℝ) (hw : ∀ σ, 0 < w σ)
    (F : DoubleConfig ι → ℝ) :
    wQuadExpectation w (fun v => F (v.1, v.2.1)) = wDoubleExpectation w F := by
  have h := wQuadExpectation_factor_pair w hw F (fun _ => 1)
  have hone : wDoubleExpectation w (fun _ => 1) = 1 := by
    unfold wDoubleExpectation
    rw [show ∑ d : DoubleConfig ι, (1 : ℝ) * wDoubleWeight w d
        = wDoublePartition w from by
      unfold wDoublePartition
      simp]
    field_simp [(wDoublePartition_pos w hw).ne']
  simpa [hone] using h

/-! ## Linearity of the weighted expectations -/

/-- The weighted fourfold expectation commutes with finite sums. -/
theorem wQuadExpectation_sum (w : Config ι → ℝ) {γ : Type*} (s : Finset γ)
    (F : γ → QuadConfig ι → ℝ) :
    wQuadExpectation w (fun v => ∑ x ∈ s, F x v)
      = ∑ x ∈ s, wQuadExpectation w (F x) := by
  unfold wQuadExpectation
  have h1 : ∀ v : QuadConfig ι, (∑ x ∈ s, F x v) * wQuadWeight w v
      = ∑ x ∈ s, F x v * wQuadWeight w v :=
    fun v => Finset.sum_mul s (fun x => F x v) _
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- The weighted fourfold expectation is homogeneous in scalar multiples. -/
theorem wQuadExpectation_const_mul (w : Config ι → ℝ) (c : ℝ)
    (F : QuadConfig ι → ℝ) :
    wQuadExpectation w (fun v => c * F v) = c * wQuadExpectation w F := by
  unfold wQuadExpectation
  have h : ∑ v : QuadConfig ι, (c * F v) * wQuadWeight w v
      = c * ∑ v : QuadConfig ι, F v * wQuadWeight w v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [h]
  ring

/-- The weighted fourfold expectation respects subtraction. -/
theorem wQuadExpectation_sub (w : Config ι → ℝ) (F H : QuadConfig ι → ℝ) :
    wQuadExpectation w (fun v => F v - H v)
      = wQuadExpectation w F - wQuadExpectation w H := by
  unfold wQuadExpectation
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

/-- The weighted doubled expectation commutes with finite sums. -/
theorem wDoubleExpectation_sum (w : Config ι → ℝ) {γ : Type*} (s : Finset γ)
    (F : γ → DoubleConfig ι → ℝ) :
    wDoubleExpectation w (fun d => ∑ x ∈ s, F x d)
      = ∑ x ∈ s, wDoubleExpectation w (F x) := by
  unfold wDoubleExpectation
  have h1 : ∀ d : DoubleConfig ι, (∑ x ∈ s, F x d) * wDoubleWeight w d
      = ∑ x ∈ s, F x d * wDoubleWeight w d :=
    fun d => Finset.sum_mul s (fun x => F x d) _
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- The weighted doubled expectation is homogeneous in scalar multiples. -/
theorem wDoubleExpectation_const_mul (w : Config ι → ℝ) (c : ℝ)
    (F : DoubleConfig ι → ℝ) :
    wDoubleExpectation w (fun d => c * F d) = c * wDoubleExpectation w F := by
  unfold wDoubleExpectation
  have h : ∑ d : DoubleConfig ι, (c * F d) * wDoubleWeight w d
      = c * ∑ d : DoubleConfig ι, F d * wDoubleWeight w d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [h]
  ring

/-! ## The generic `tq` comparison inequality -/

/-- Joint u-monomial weighted expectations are non-negative when the fourfold
weight has non-negative u-moments. -/
theorem wQuadExpectation_uMonomial_nonneg (w : Config ι → ℝ)
    (hw : ∀ σ, 0 < w σ) (hmom : HasNonnegUMoments (wQuadWeight w))
    (k l m n : ι → ℕ) :
    0 ≤ wQuadExpectation w (uMonomial k l m n) := by
  unfold wQuadExpectation
  exact mul_nonneg (inv_nonneg.mpr (wQuadPartition_pos w hw).le) (hmom k l m n)

/-- The `t`/`q` mixed term is a joint u-monomial with non-negative weighted
fourfold expectation. -/
theorem wQuadExpectation_t_q_term_nonneg (w : Config ι → ℝ)
    (hw : ∀ σ, 0 < w σ) (hmom : HasNonnegUMoments (wQuadWeight w))
    (S S' T T' : Finset ι) :
    0 ≤ wQuadExpectation w (fun v =>
      (uProd₁ S v * uProd₂ S' v) * (uProd₃ T v * uProd₄ T' v)) := by
  have heq : (fun v : QuadConfig ι =>
      (uProd₁ S v * uProd₂ S' v) * (uProd₃ T v * uProd₄ T' v))
      = uMonomial (fun i => if i ∈ S then 1 else 0)
          (fun i => if i ∈ S' then 1 else 0)
          (fun i => if i ∈ T then 1 else 0)
          (fun i => if i ∈ T' then 1 else 0) := by
    funext v
    rw [show (uProd₁ S v * uProd₂ S' v) * (uProd₃ T v * uProd₄ T' v)
        = uProd₁ S v * uProd₂ S' v * uProd₃ T v * uProd₄ T' v from by ring,
      uProd_eq_uMonomial]
  rw [heq]
  exact wQuadExpectation_uMonomial_nonneg w hw hmom _ _ _ _

/-- **The generic `tq` comparison inequality** (GJ Cor 4.3.2, third
inequality, over an abstract positive weight with non-negative fourfold
u-moments): `0 ≤ ⟨t^A⟩₂⟨q^B⟩₂ − ⟨t^A q^B⟩₂`. -/
theorem wCor_4_3_2_tq (w : Config ι → ℝ) (hw : ∀ σ, 0 < w σ)
    (hmom : HasNonnegUMoments (wQuadWeight w)) (A B : Finset ι) :
    0 ≤ wDoubleExpectation w (tProd A) * wDoubleExpectation w (qProd B)
      - wDoubleExpectation w (fun d => tProd A d * qProd B d) := by
  rw [← wQuadExpectation_factor_pair w hw (tProd A) (qProd B),
    ← wQuadExpectation_fst_pair w hw (fun d => tProd A d * qProd B d),
    ← wQuadExpectation_sub]
  have hpt : (fun v : QuadConfig ι =>
      tProd A (v.1, v.2.1) * qProd B (v.2.2.1, v.2.2.2)
        - tProd A (v.1, v.2.1) * qProd B (v.1, v.2.1))
      = fun v => ∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
          ((1 / 2 : ℝ) ^ A.card * (1 / 2) ^ B.card * (1 - (-1) ^ (B \ T).card)) *
            ((uProd₁ S v * uProd₂ (A \ S) v) * (uProd₃ T v * uProd₄ (B \ T) v)) := by
    funext v
    rw [tProd_fst_expand, qProd_snd_expand, qProd_fst_expand]
    exact mul_bracket_expand A.powerset B.powerset _ _ _ _ _
  rw [hpt, wQuadExpectation_sum]
  refine Finset.sum_nonneg fun S _ => ?_
  rw [wQuadExpectation_sum]
  refine Finset.sum_nonneg fun T _ => ?_
  rw [wQuadExpectation_const_mul]
  exact mul_nonneg (bracket_coeff_nonneg _ _ _)
    (wQuadExpectation_t_q_term_nonneg w hw hmom _ _ _ _)

/-! ## Powerset formulas for the weighted doubled expectations -/

/-- The correlation of an abstract weight: `c^w_X = ⟨σ^X⟩_w`. -/
noncomputable def wCorrelation (w : Config ι → ℝ) (X : Finset ι) : ℝ :=
  wExpectation w (spinProduct X)

/-- Per-term factorisation of the weighted doubled expectation of a per-copy
spin-product pair. -/
theorem wDoubleExpectation_spin_term (w : Config ι → ℝ) (hw : ∀ σ, 0 < w σ)
    (X Y : Finset ι) :
    wDoubleExpectation w (fun d => spinProduct X d.1 * spinProduct Y d.2)
      = wCorrelation w X * wCorrelation w Y := by
  rw [wDoubleExpectation_factor w hw]
  rfl

/-- **Powerset formula for the weighted doubled `t` expectation**:
`⟨t^A⟩₂ = ∑_{S ⊆ A} c^w_S · c^w_{A∖S}`. -/
theorem wDoubleExpectation_tProd (w : Config ι → ℝ) (hw : ∀ σ, 0 < w σ)
    (A : Finset ι) :
    wDoubleExpectation w (tProd A)
      = ∑ S ∈ A.powerset, wCorrelation w S * wCorrelation w (A \ S) := by
  have hrw : tProd (ι := ι) A
      = fun d => ∑ S ∈ A.powerset, spinProduct S d.1 * spinProduct (A \ S) d.2 := by
    funext d
    exact tProd_expand A d
  rw [hrw, wDoubleExpectation_sum]
  exact Finset.sum_congr rfl fun S _ => wDoubleExpectation_spin_term w hw _ _

/-- **Powerset formula for the weighted doubled `q` expectation**:
`⟨q^B⟩₂ = ∑_{T ⊆ B} (−1)^{|B∖T|} c^w_T · c^w_{B∖T}`. -/
theorem wDoubleExpectation_qProd (w : Config ι → ℝ) (hw : ∀ σ, 0 < w σ)
    (B : Finset ι) :
    wDoubleExpectation w (qProd B)
      = ∑ T ∈ B.powerset,
          (-1 : ℝ) ^ (B \ T).card *
            (wCorrelation w T * wCorrelation w (B \ T)) := by
  have hrw : qProd (ι := ι) B
      = fun d => ∑ T ∈ B.powerset,
          (-1 : ℝ) ^ (B \ T).card *
            (spinProduct T d.1 * spinProduct (B \ T) d.2) := by
    funext d
    exact qProd_expand B d
  rw [hrw, wDoubleExpectation_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [wDoubleExpectation_const_mul, wDoubleExpectation_spin_term w hw]

/-- **Powerset formula for the weighted doubled `t·q` expectation** (disjoint
index sets): `⟨t^A q^B⟩₂ = ∑_S ∑_T (−1)^{|B∖T|} c^w_{S∪T} · c^w_{(A∖S)∪(B∖T)}`. -/
theorem wDoubleExpectation_tProd_mul_qProd (w : Config ι → ℝ)
    (hw : ∀ σ, 0 < w σ) (A B : Finset ι) (hAB : Disjoint A B) :
    wDoubleExpectation w (fun d => tProd A d * qProd B d)
      = ∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
          (-1 : ℝ) ^ (B \ T).card *
            (wCorrelation w (S ∪ T) * wCorrelation w ((A \ S) ∪ (B \ T))) := by
  have hobs : (fun d : DoubleConfig ι => tProd A d * qProd B d)
      = fun d => ∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
          (-1 : ℝ) ^ (B \ T).card *
            (spinProduct (S ∪ T) d.1 * spinProduct ((A \ S) ∪ (B \ T)) d.2) := by
    funext d
    rw [tProd_expand A d, qProd_expand B d, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl fun T hT => ?_
    have hd₁ : Disjoint S T :=
      hAB.mono (Finset.mem_powerset.1 hS) (Finset.mem_powerset.1 hT)
    have hd₂ : Disjoint (A \ S) (B \ T) :=
      hAB.mono Finset.sdiff_subset Finset.sdiff_subset
    have hm₁ : spinProduct S d.1 * spinProduct T d.1
        = spinProduct (S ∪ T) d.1 := by
      rw [spinProduct_mul, hd₁.symmDiff_eq_sup]
      rfl
    have hm₂ : spinProduct (A \ S) d.2 * spinProduct (B \ T) d.2
        = spinProduct ((A \ S) ∪ (B \ T)) d.2 := by
      rw [spinProduct_mul, hd₂.symmDiff_eq_sup]
      rfl
    calc (spinProduct S d.1 * spinProduct (A \ S) d.2) *
          ((-1 : ℝ) ^ (B \ T).card * (spinProduct T d.1 * spinProduct (B \ T) d.2))
        = (-1 : ℝ) ^ (B \ T).card *
            ((spinProduct S d.1 * spinProduct T d.1) *
              (spinProduct (A \ S) d.2 * spinProduct (B \ T) d.2)) := by ring
      _ = (-1 : ℝ) ^ (B \ T).card *
            (spinProduct (S ∪ T) d.1 * spinProduct ((A \ S) ∪ (B \ T)) d.2) := by
          rw [hm₁, hm₂]
  rw [hobs, wDoubleExpectation_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [wDoubleExpectation_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [wDoubleExpectation_const_mul, wDoubleExpectation_spin_term w hw]

end Lebowitz

end IsingModel
