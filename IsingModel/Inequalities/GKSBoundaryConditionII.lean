import IsingModel.Inequalities.GKSBoundaryCondition

/-!
# GKS-II for the `+` boundary-condition state (FV §3.6 / Theorem 3.49, Issue #3605)

The second Griffiths inequality (GKS-II) for the `+` boundary state,
`⟨σ^A⟩⁺_Λ · ⟨σ^B⟩⁺_Λ ≤ ⟨σ^{AΔB}⟩⁺_Λ`, by the duplicate-variable argument applied to
the pinned weight `w⁺ = w · pin`.  The change of variables `ω' ↦ φt`
(`(φt)_i = ω_i·t_i`) collapses the pinning factors,
`pin(ω)·pin(φt) = pin(ω)·pin(t)`, so the doubled `+` weight is
`w⁺(ω)·w⁺(φt) = modExp(t,ω)·pin(ω)·pin(t)`, which (as a function of `ω`) has
non-negative correlations.  Mirrors the free-state `gks_second`
(`Inequalities/GKS.lean`) and the scaled-state `scaledCorrelation_gks_second`.

* `gibbsExpectationBC_plus_gks_second` — GKS-II for the `+` boundary state.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.6, Theorem 3.49 (GKS-II, pp. 127–128).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The boundary pinning product** `pin_Λ(σ) = ∏_{i ∈ Λᶜ}(½ + ½·σ_i)`. -/
noncomputable def bcPin (Λ : Finset ι) (σ : Config ι) : ℝ :=
  ∏ i ∈ Finset.univ \ Λ, (1 / 2 + 1 / 2 * spinProduct {i} σ)

/-- Each pinning factor is non-negative, so `pin_Λ(σ) ≥ 0`. -/
theorem bcPin_nonneg (Λ : Finset ι) (σ : Config ι) : 0 ≤ bcPin Λ σ := by
  refine Finset.prod_nonneg fun i _ => ?_
  rw [spinProduct_singleton]
  cases σ i <;> norm_num [Spin.toSign]

/-- **The `+` boundary weight factors as `w·pin`** (restatement of
`boltzmannWeightBC_plus_eq_prod` with `bcPin`). -/
theorem boltzmannWeightBC_plus_eq_mul_pin (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J h : ℝ) (Λ : Finset ι) (σ : Config ι) :
    boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ
      = boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ * bcPin Λ σ :=
  boltzmannWeightBC_plus_eq_prod G β J h Λ σ

/-- **The exp-product modified weight** (boltzmann part of the doubled `+` weight). -/
noncomputable def bcModExp (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (t ω : Config ι) : ℝ :=
  (∏ e ∈ G.edgeFinset, Real.exp (p.β * p.J * (1 + edgeSpin (K := ℝ) t e) *
      edgeSpin (K := ℝ) ω e)) *
  (∏ i : ι, Real.exp (p.β * p.h * (1 + Spin.sign ℝ (t i)) * Spin.sign ℝ (ω i)))

omit [Fintype ι] [DecidableEq ι] in
/-- Helper: `edgeSpin (φ_t ω) e = edgeSpin ω e * edgeSpin t e`. -/
private lemma bc_edgeSpin_spinMul (ω t : Config ι) (e : Sym2 ι) :
    edgeSpin (K := ℝ) (fun i => Spin.mul (ω i) (t i)) e =
    edgeSpin (K := ℝ) ω e * edgeSpin (K := ℝ) t e := by
  refine Sym2.ind (fun i j => ?_) e
  simp [edgeSpin, Sym2.lift_mk, Spin.sign, Spin.toSign_mul]; ring

/-- Helper: `Spin.sign (Spin.mul a b) = Spin.sign a * Spin.sign b`. -/
private lemma bc_sign_spinMul (a b : Spin) :
    Spin.sign ℝ (Spin.mul a b) = Spin.sign ℝ a * Spin.sign ℝ b := by
  simp [Spin.sign, Spin.toSign_mul]

omit [DecidableEq ι] in
/-- Product form of the plain Boltzmann weight. -/
private lemma boltzmannWeight_product_form (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (σ : Config ι) :
    boltzmannWeight G p σ =
      (∏ e ∈ G.edgeFinset, Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e)) *
      (∏ i : ι, Real.exp (p.β * p.h * Spin.sign ℝ (σ i))) := by
  simp only [boltzmannWeight, hamiltonian, interactionEnergy, externalFieldEnergy]
  rw [← Real.exp_sum (f := fun e => p.β * p.J * edgeSpin (K := ℝ) σ e),
      ← Real.exp_sum (f := fun i => p.β * p.h * Spin.sign ℝ (σ i)),
      ← Real.exp_add]
  congr 1
  simp only [← Finset.mul_sum]
  ring

omit [DecidableEq ι] in
/-- **Boltzmann duplicate identity**: `w(ω)·w(φ_t ω) = bcModExp(t,ω)`. -/
theorem boltzmannWeight_duplicate_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (t ω : Config ι) :
    boltzmannWeight G p ω * boltzmannWeight G p (fun i => Spin.mul (ω i) (t i)) =
      bcModExp G p t ω := by
  rw [boltzmannWeight_product_form G p ω,
      boltzmannWeight_product_form G p (fun i => Spin.mul (ω i) (t i))]
  simp_rw [bc_edgeSpin_spinMul ω t, bc_sign_spinMul]
  simp only [bcModExp]
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  · apply Finset.prod_congr rfl; intro e _
    rw [← Real.exp_add]; congr 1; ring
  · apply Finset.prod_congr rfl; intro i _
    rw [← Real.exp_add]; congr 1; ring

/-- **Pinning collapse**: `pin_Λ(ω)·pin_Λ(φ_t ω) = pin_Λ(ω)·pin_Λ(t)` — because each
factor `(½+½σ_i^ω)(½+½σ_i^ω·σ_i^t) = (½+½σ_i^ω)(½+½σ_i^t)` (since `(σ_i^ω)² = 1`). -/
theorem bcPin_duplicate_eq (Λ : Finset ι) (t ω : Config ι) :
    bcPin Λ ω * bcPin Λ (fun i => Spin.mul (ω i) (t i)) = bcPin Λ ω * bcPin Λ t := by
  unfold bcPin
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hsi : spinProduct {i} (fun j => Spin.mul (ω j) (t j)) =
      spinProduct {i} ω * spinProduct {i} t := by
    rw [spinProduct_singleton, spinProduct_singleton, spinProduct_singleton,
      Spin.toSign_mul]
    push_cast; ring
  rw [hsi]
  have hsq : spinProduct {i} ω * spinProduct {i} ω = 1 := by
    rw [spinProduct_singleton]; cases ω i <;> norm_num [Spin.toSign]
  linear_combination (1 / 4 * spinProduct {i} t) * hsq

/-- **The boundary modified weight**: `bcModExp(t,ω)·pin_Λ(ω)·pin_Λ(t)`, the doubled
`+` weight after the change of variables. -/
noncomputable def bcModifiedWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (Λ : Finset ι) (t ω : Config ι) : ℝ :=
  bcModExp G p t ω * bcPin Λ ω * bcPin Λ t

/-- **The doubled `+` weight equals the boundary modified weight** under the change of
variables `ω' = φ_t ω`. -/
theorem boltzmannWeightBC_plus_duplicate_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J h : ℝ) (Λ : Finset ι) (t ω : Config ι) :
    boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) ω *
      boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι)
        (fun i => Spin.mul (ω i) (t i)) =
      bcModifiedWeight G (⟨J, h, β⟩ : IsingParams ℝ) Λ t ω := by
  rw [boltzmannWeightBC_plus_eq_mul_pin, boltzmannWeightBC_plus_eq_mul_pin, bcModifiedWeight]
  rw [show boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) ω * bcPin Λ ω *
        (boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) (fun i => Spin.mul (ω i) (t i)) *
          bcPin Λ (fun i => Spin.mul (ω i) (t i)))
      = (boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) ω *
            boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) (fun i => Spin.mul (ω i) (t i))) *
        (bcPin Λ ω * bcPin Λ (fun i => Spin.mul (ω i) (t i))) from by ring,
    boltzmannWeight_duplicate_eq, bcPin_duplicate_eq]
  ring

/-- **The boundary modified weight has non-negative correlations** (for each fixed `t`):
the exp-product part is HNC (couplings `βJ(1+t^e) ≥ 0`, `βh(1+t_i) ≥ 0`), times the
pinning product `pin_Λ(ω)` (factors `(½+½σ^i)`), times the non-negative constant
`pin_Λ(t)`. -/
theorem bcModifiedWeight_nonneg_corr (G : SimpleGraph ι) [Fintype G.edgeSet]
    {p : IsingParams ℝ} (hf : Ferromagnetic p) (Λ : Finset ι) (t : Config ι) :
    HasNonnegCorrelations (bcModifiedWeight G p Λ t) := by
  have hexp_hnc : HasNonnegCorrelations (bcModExp G p t) := by
    unfold bcModExp
    exact hasNonnegCorrelations_edge_site_product G
      (fun e => p.β * p.J * (1 + edgeSpin (K := ℝ) t e))
      (fun i => p.β * p.h * (1 + Spin.sign ℝ (t i)))
      (fun e _ => by
        apply mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
        have := edgeSpin_sq t e
        have : (edgeSpin (K := ℝ) t e - 1) * (edgeSpin (K := ℝ) t e + 1) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h | h <;> linarith)
      (fun i => by
        apply mul_nonneg (mul_nonneg hf.hβ.le hf.hh)
        have := Spin.sign_sq (K := ℝ) (t i)
        have : (Spin.sign ℝ (t i) - 1) * (Spin.sign ℝ (t i) + 1) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h | h <;> linarith)
  have hexp_pin_hnc : HasNonnegCorrelations (fun ω => bcModExp G p t ω * bcPin Λ ω) := by
    unfold bcPin
    exact hasNonnegCorrelations_mul_prod (Finset.univ \ Λ) hexp_hnc _
      (fun i _ => ⟨1 / 2, 1 / 2, {i}, by norm_num, by norm_num, fun σ => rfl⟩)
  intro S
  have hrw : ∀ ω : Config ι, spinProduct S ω * bcModifiedWeight G p Λ t ω =
      bcPin Λ t * (spinProduct S ω * (bcModExp G p t ω * bcPin Λ ω)) := by
    intro ω; unfold bcModifiedWeight; ring
  simp_rw [hrw, ← Finset.mul_sum]
  exact mul_nonneg (bcPin_nonneg Λ t) (hexp_pin_hnc S)

/-- The duplicate sum for the `+` boundary state. -/
private noncomputable def bcDuplicateSum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J h : ℝ) (Λ : Finset ι) (A B : Finset ι) : ℝ :=
  ∑ ω : Config ι, ∑ ω' : Config ι,
    spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
    boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) ω *
    boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) ω'

/-- The `+` boundary duplicate sum equals `Z⁺² · (⟨AΔB⟩⁺ − ⟨A⟩⁺·⟨B⟩⁺)`. -/
private theorem bcDuplicateSum_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J h : ℝ} (Λ : Finset ι) (A B : Finset ι) :
    bcDuplicateSum G β J h Λ A B =
      partitionFunctionBC G β (fun _ => J) h Λ (plusConfig ι) ^ 2 *
        (gibbsExpectationBC G β (fun _ => J) h Λ (plusConfig ι) (spinProduct (symmDiff A B)) -
          gibbsExpectationBC G β (fun _ => J) h Λ (plusConfig ι) (spinProduct A) *
            gibbsExpectationBC G β (fun _ => J) h Λ (plusConfig ι) (spinProduct B)) := by
  have hZ : partitionFunctionBC G β (fun _ => J) h Λ (plusConfig ι) ≠ 0 :=
    partitionFunctionBC_ne_zero G β (fun _ => J) h Λ (plusConfig ι)
  unfold bcDuplicateSum gibbsExpectationBC
  set w := boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) with hw_def
  rw [sq]
  field_simp
  have hmul : ∀ ω : Config ι, spinProduct A ω * spinProduct B ω =
      spinProduct (symmDiff A B) ω := fun ω => spinProduct_mul A B ω
  have step1 : ∀ ω : Config ι,
      ∑ ω' : Config ι, spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
        w ω * w ω' =
      spinProduct A ω * spinProduct B ω * w ω * ∑ ω', w ω' -
      spinProduct A ω * w ω * ∑ ω', spinProduct B ω' * w ω' := by
    intro ω
    simp_rw [show ∀ ω' : Config ι,
        spinProduct A ω * (spinProduct B ω - spinProduct B ω') * w ω * w ω' =
        spinProduct A ω * spinProduct B ω * w ω * w ω' -
        spinProduct A ω * w ω * (spinProduct B ω' * w ω')
      from fun ω' => by ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp_rw [step1, Finset.sum_sub_distrib, hmul]
  unfold partitionFunctionBC
  rw [← hw_def]
  simp_rw [← Finset.sum_mul]
  ring

/-- The change-of-variables form of the `+` boundary duplicate sum. -/
private noncomputable def bcDuplicateSumChanged (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J h : ℝ) (Λ : Finset ι) (A B : Finset ι) : ℝ :=
  ∑ t : Config ι, (1 - spinProduct B t) *
    ∑ ω : Config ι, spinProduct (symmDiff A B) ω *
      bcModifiedWeight G (⟨J, h, β⟩ : IsingParams ℝ) Λ t ω

/-- The `+` boundary duplicate sum equals its change-of-variables form. -/
private theorem bcDuplicateSum_eq_changed (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J h : ℝ) (Λ : Finset ι) (A B : Finset ι) :
    bcDuplicateSum G β J h Λ A B = bcDuplicateSumChanged G β J h Λ A B := by
  unfold bcDuplicateSum bcDuplicateSumChanged
  have hinner : ∀ ω : Config ι,
      ∑ ω', spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
        boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) ω *
        boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) ω' =
      ∑ t, (1 - spinProduct B t) *
        (spinProduct (symmDiff A B) ω *
          bcModifiedWeight G (⟨J, h, β⟩ : IsingParams ℝ) Λ t ω) := by
    intro ω
    let φ : Config ι → Config ι := fun ω' i => Spin.mul (ω i) (ω' i)
    have hφ_inv : Function.Involutive φ := fun t => by ext i; simp [φ, Spin.mul_mul_cancel]
    rw [(Fintype.sum_bijective φ hφ_inv.bijective _ _ fun t => rfl).symm]
    apply Finset.sum_congr rfl; intro t _
    have hspB : spinProduct B (φ t) = spinProduct B ω * spinProduct B t := by
      unfold spinProduct
      simp_rw [show ∀ i, (↑((φ t i).toSign) : ℝ) = ↑(ω i).toSign * ↑(t i).toSign
        from fun i => by simp [φ, Spin.toSign_mul]]
      rw [Finset.prod_mul_distrib]
    rw [hspB]
    have hw : boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) ω *
        boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) (φ t) =
        bcModifiedWeight G (⟨J, h, β⟩ : IsingParams ℝ) Λ t ω :=
      boltzmannWeightBC_plus_duplicate_eq G β J h Λ t ω
    have key : spinProduct A ω * (spinProduct B ω - spinProduct B ω * spinProduct B t) *
        boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) ω *
        boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) (φ t) =
        (1 - spinProduct B t) *
        (spinProduct (symmDiff A B) ω *
          bcModifiedWeight G (⟨J, h, β⟩ : IsingParams ℝ) Λ t ω) := by
      rw [← hw, ← spinProduct_mul]; ring
    linarith
  simp_rw [hinner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  rw [← Finset.mul_sum]

/-- The change-of-variables `+` boundary duplicate sum is non-negative. -/
private theorem bcDuplicateSumChanged_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J h : ℝ} (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ)) (Λ : Finset ι)
    (A B : Finset ι) :
    0 ≤ bcDuplicateSumChanged G β J h Λ A B := by
  unfold bcDuplicateSumChanged
  apply Finset.sum_nonneg; intro t _
  exact mul_nonneg (one_sub_spinProduct_nonneg B t)
    (bcModifiedWeight_nonneg_corr G hf Λ t (symmDiff A B))

/-- **Second Griffiths inequality (GKS-II) for the `+` boundary state**: for a
ferromagnetic Ising model with the `+` boundary condition,
`⟨σ^A⟩⁺_Λ · ⟨σ^B⟩⁺_Λ ≤ ⟨σ^{AΔB}⟩⁺_Λ`. -/
theorem gibbsExpectationBC_plus_gks_second (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J h : ℝ} (hβ : 0 < β) (hJ : 0 ≤ J) (hh : 0 ≤ h) (Λ : Finset ι) (A B : Finset ι) :
    gibbsExpectationBC G β (fun _ => J) h Λ (plusConfig ι) (spinProduct A) *
        gibbsExpectationBC G β (fun _ => J) h Λ (plusConfig ι) (spinProduct B) ≤
      gibbsExpectationBC G β (fun _ => J) h Λ (plusConfig ι) (spinProduct (symmDiff A B)) := by
  have hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ) := ⟨hJ, hh, hβ⟩
  have hZ2 : (0 : ℝ) < partitionFunctionBC G β (fun _ => J) h Λ (plusConfig ι) ^ 2 :=
    pow_pos (partitionFunctionBC_pos G β (fun _ => J) h Λ (plusConfig ι)) 2
  have hdup : 0 ≤ bcDuplicateSum G β J h Λ A B := by
    rw [bcDuplicateSum_eq_changed G β J h Λ A B]
    exact bcDuplicateSumChanged_nonneg G hf Λ A B
  rw [bcDuplicateSum_eq G Λ A B] at hdup
  linarith [nonneg_of_mul_nonneg_right hdup hZ2]

end IsingModel
