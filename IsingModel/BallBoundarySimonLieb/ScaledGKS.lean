import IsingModel.CouplingDerivative
import IsingModel.Inequalities.GHS

/-!
# Ball-boundary Simon-Lieb scaled GKS wrappers

Initial helper layer for the ball-boundary Simon-Lieb inequality.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Product form of the scaled Boltzmann weight -/

/-- When `E₀ ⊆ G.edgeFinset`, the scaled Boltzmann weight decomposes as a product:
`w_s(σ) = ∏_{e∈G} exp(K_e · σ_e) · ∏_i exp(βh · σ_i)`
where `K_e = βsJ` for `e ∈ E₀` and `K_e = βJ` otherwise. -/
private lemma scaledBoltzmannWeight_product_form (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (s : ℝ) (σ : Config ι) :
    scaledBoltzmannWeight G E₀ p s σ =
      (∏ e ∈ G.edgeFinset, Real.exp ((if e ∈ E₀ then p.β * s * p.J else p.β * p.J) *
          edgeSpin (K := ℝ) σ e)) *
      (∏ i : ι, Real.exp (p.β * p.h * Spin.sign ℝ (σ i))) := by
  simp only [scaledBoltzmannWeight, boltzmannWeight, hamiltonian, interactionEnergy,
    externalFieldEnergy]
  -- LHS: exp(A) * exp(B), RHS: ∏_G exp(K_e * σ_e) * ∏_i exp(βh * σ_i)
  -- Strategy: convert RHS to exp(Σ_G K_e*σ_e + Σ_i βh*σ_i), then show LHS exp equals it
  rw [← Real.exp_add]
  conv_rhs => rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
  congr 1
  -- Goal: A + B = Σ_G K_e*σ_e + Σ_i βh*σ_i
  -- A = -β*(-J*Σ_G + -h*Σ_i), B = -β*(1-s)*J*Σ_{E₀}
  have h_sum_G : ∑ e ∈ G.edgeFinset \ E₀, edgeSpin (K := ℝ) σ e +
      ∑ e ∈ E₀, edgeSpin (K := ℝ) σ e =
      ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e :=
    Finset.sum_sdiff hE₀_sub
  have hkey : ∑ e ∈ G.edgeFinset, (if e ∈ E₀ then p.β * s * p.J else p.β * p.J) *
      edgeSpin (K := ℝ) σ e =
      ∑ e ∈ G.edgeFinset \ E₀, p.β * p.J * edgeSpin (K := ℝ) σ e +
      ∑ e ∈ E₀, p.β * s * p.J * edgeSpin (K := ℝ) σ e := by
    rw [← Finset.sum_sdiff hE₀_sub]
    congr 1
    · apply Finset.sum_congr rfl; intro e he
      have hne := (Finset.mem_sdiff.mp he).2; simp [hne]
    · apply Finset.sum_congr rfl; intro e he; simp [he]
  rw [hkey, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [← Finset.mul_sum]
  linear_combination -p.β * p.J * h_sum_G

/-! ## GKS-I for the scaled model -/

/-- **GKS-I for the scaled model**: for ferromagnetic params, `s ≥ 0`, and `E₀ ⊆ G.edgeFinset`,
all scaled correlations are non-negative. -/
theorem scaledCorrelation_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (s : ℝ) (hs : 0 ≤ s) (A : Finset ι) :
    0 ≤ scaledCorrelation G E₀ p s A := by
  unfold scaledCorrelation scaledGibbsExpectation
  apply mul_nonneg (inv_nonneg.mpr (le_of_lt (scaledPartitionFunction_pos G E₀ p s)))
  -- Need: 0 ≤ ∑ σ, spinProduct A σ * scaledBoltzmannWeight G E₀ p s σ
  have hnnc : HasNonnegCorrelations (scaledBoltzmannWeight G E₀ p s) := by
    intro S
    have heq : ∀ σ : Config ι, scaledBoltzmannWeight G E₀ p s σ =
        (∏ e ∈ G.edgeFinset, Real.exp ((if e ∈ E₀ then p.β * s * p.J else p.β * p.J) *
            edgeSpin (K := ℝ) σ e)) *
        (∏ i : ι, Real.exp (p.β * p.h * Spin.sign ℝ (σ i))) :=
      fun σ => scaledBoltzmannWeight_product_form G E₀ hE₀_sub p s σ
    simp_rw [heq]
    exact hasNonnegCorrelations_edge_site_product G
      (fun e => if e ∈ E₀ then p.β * s * p.J else p.β * p.J)
      (fun _ => p.β * p.h)
      (fun e _ => by
        change 0 ≤ if e ∈ E₀ then p.β * s * p.J else p.β * p.J
        split_ifs
        · exact mul_nonneg (mul_nonneg hf.hβ.le hs) hf.hJ
        · exact mul_nonneg hf.hβ.le hf.hJ)
      (fun _ => mul_nonneg hf.hβ.le hf.hh) S
  exact hnnc A

/-! ## GKS-II for the scaled model (duplicate variable argument) -/

/-- The duplicate sum for the scaled model. -/
private noncomputable def scaledDuplicateSum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (A B : Finset ι) : ℝ :=
  ∑ ω : Config ι, ∑ ω' : Config ι,
    spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
    scaledBoltzmannWeight G E₀ p s ω * scaledBoltzmannWeight G E₀ p s ω'

/-- The scaled duplicate sum equals `Z_s² · (⟨AΔB⟩_s − ⟨A⟩_s·⟨B⟩_s)`. -/
private theorem scaledDuplicateSum_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (A B : Finset ι) :
    scaledDuplicateSum G E₀ p s A B =
    scaledPartitionFunction G E₀ p s ^ 2 *
      (scaledCorrelation G E₀ p s (symmDiff A B) -
       scaledCorrelation G E₀ p s A * scaledCorrelation G E₀ p s B) := by
  have hZ := scaledPartitionFunction_ne_zero G E₀ p s
  unfold scaledDuplicateSum scaledCorrelation scaledGibbsExpectation
  rw [sq]; field_simp
  have hmul : ∀ ω : Config ι, spinProduct A ω * spinProduct B ω =
      spinProduct (symmDiff A B) ω := fun ω => spinProduct_mul A B ω
  have step1 : ∀ ω : Config ι,
      ∑ ω' : Config ι, spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
        scaledBoltzmannWeight G E₀ p s ω * scaledBoltzmannWeight G E₀ p s ω' =
      spinProduct A ω * spinProduct B ω * scaledBoltzmannWeight G E₀ p s ω *
        ∑ ω', scaledBoltzmannWeight G E₀ p s ω' -
      spinProduct A ω * scaledBoltzmannWeight G E₀ p s ω *
        ∑ ω', spinProduct B ω' * scaledBoltzmannWeight G E₀ p s ω' := by
    intro ω
    simp_rw [show ∀ ω' : Config ι,
        spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
        scaledBoltzmannWeight G E₀ p s ω * scaledBoltzmannWeight G E₀ p s ω' =
        spinProduct A ω * spinProduct B ω * scaledBoltzmannWeight G E₀ p s ω *
        scaledBoltzmannWeight G E₀ p s ω' -
        spinProduct A ω * scaledBoltzmannWeight G E₀ p s ω *
        (spinProduct B ω' * scaledBoltzmannWeight G E₀ p s ω')
      from fun ω' => by ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp_rw [step1, Finset.sum_sub_distrib, hmul]
  unfold scaledPartitionFunction; simp_rw [← Finset.sum_mul]; ring

/-- The scaled modified weight: the product form after the change of variables.
For fixed `t`, this uses per-edge coupling `(if e ∈ E₀ then β·s·J else β·J) · (1 + t^e)`. -/
private noncomputable def scaledModifiedWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (t ω : Config ι) : ℝ :=
  (∏ e ∈ G.edgeFinset,
      Real.exp ((if e ∈ E₀ then p.β * s * p.J else p.β * p.J) *
                (1 + edgeSpin (K := ℝ) t e) * edgeSpin (K := ℝ) ω e)) *
  (∏ i : ι, Real.exp (p.β * p.h * (1 + Spin.sign ℝ (t i)) * Spin.sign ℝ (ω i)))

/-- The change of variables formula: `w_s(ω) · w_s(φ_t ω) = scaledModifiedWeight t ω`.
Requires `E₀ ⊆ G.edgeFinset` to merge the edge sums. -/
private theorem scaledBoltzmannWeight_duplicate_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (s : ℝ) (t ω : Config ι) :
    scaledBoltzmannWeight G E₀ p s ω *
      scaledBoltzmannWeight G E₀ p s (fun i => Spin.mul (ω i) (t i)) =
    scaledModifiedWeight G E₀ p s t ω := by
  rw [scaledBoltzmannWeight_product_form G E₀ hE₀_sub p s ω,
      scaledBoltzmannWeight_product_form G E₀ hE₀_sub p s (fun i => Spin.mul (ω i) (t i))]
  simp_rw [edgeSpin_spinMul ω t, Spin.sign_mul]
  simp only [scaledModifiedWeight]
  -- Both sides are products of exps of sums; convert all to exp(Σ + Σ) form
  conv_lhs =>
    rw [← Real.exp_sum (f := fun e => (if e ∈ E₀ then p.β * s * p.J else p.β * p.J) *
            edgeSpin (K := ℝ) ω e),
        ← Real.exp_sum (f := fun i => p.β * p.h * Spin.sign ℝ (ω i)),
        ← Real.exp_add,
        ← Real.exp_sum (f := fun e => (if e ∈ E₀ then p.β * s * p.J else p.β * p.J) *
            (edgeSpin (K := ℝ) ω e * edgeSpin (K := ℝ) t e)),
        ← Real.exp_sum (f := fun i => p.β * p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i))),
        ← Real.exp_add, ← Real.exp_add]
  conv_rhs =>
    rw [← Real.exp_sum (f := fun e => (if e ∈ E₀ then p.β * s * p.J else p.β * p.J) *
            (1 + edgeSpin (K := ℝ) t e) * edgeSpin (K := ℝ) ω e),
        ← Real.exp_sum (f := fun i => p.β * p.h * (1 + Spin.sign ℝ (t i)) * Spin.sign ℝ (ω i)),
        ← Real.exp_add]
  congr 1
  -- Goal: (Σ_G K_e*ω_e + Σ_i βh*ω_i) + (Σ_G K_e*(ω_e*t_e) + Σ_i βh*(ω_i*t_i))
  --     = Σ_G K_e*(1+t_e)*ω_e + Σ_i βh*(1+t_i)*ω_i
  have hG : ∑ e ∈ G.edgeFinset, (if e ∈ E₀ then p.β * s * p.J else p.β * p.J) *
      edgeSpin (K := ℝ) ω e +
      ∑ e ∈ G.edgeFinset, (if e ∈ E₀ then p.β * s * p.J else p.β * p.J) *
      (edgeSpin (K := ℝ) ω e * edgeSpin (K := ℝ) t e) =
      ∑ e ∈ G.edgeFinset, (if e ∈ E₀ then p.β * s * p.J else p.β * p.J) *
      (1 + edgeSpin (K := ℝ) t e) * edgeSpin (K := ℝ) ω e := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro e _; ring
  have hi : ∑ i : ι, p.β * p.h * Spin.sign ℝ (ω i) +
      ∑ i : ι, p.β * p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i)) =
      ∑ i : ι, p.β * p.h * (1 + Spin.sign ℝ (t i)) * Spin.sign ℝ (ω i) := by
    rw [← Finset.sum_add_distrib]; congr 1; ext i; ring
  linarith

/-! ## Non-negativity of the scaled modified weight -/

/-- The scaled modified weight has non-negative correlations under ferromagnetic
parameters and `s ≥ 0`. -/
private theorem scaledModifiedWeight_nonneg_corr (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (s : ℝ) (hs : 0 ≤ s) (t : Config ι) :
    HasNonnegCorrelations (scaledModifiedWeight G E₀ p s t) := by
  unfold scaledModifiedWeight
  exact hasNonnegCorrelations_edge_site_product G
    (fun e => (if e ∈ E₀ then p.β * s * p.J else p.β * p.J) * (1 + edgeSpin (K := ℝ) t e))
    (fun i => p.β * p.h * (1 + Spin.sign ℝ (t i)))
    (fun e _ => by
      apply mul_nonneg
      · change 0 ≤ if e ∈ E₀ then p.β * s * p.J else p.β * p.J
        split_ifs
        · exact mul_nonneg (mul_nonneg hf.hβ.le hs) hf.hJ
        · exact mul_nonneg hf.hβ.le hf.hJ
      · have := edgeSpin_sq t e
        have : (edgeSpin (K := ℝ) t e - 1) * (edgeSpin (K := ℝ) t e + 1) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h | h <;> linarith)
    (fun i => by
      apply mul_nonneg (mul_nonneg hf.hβ.le hf.hh)
      have := Spin.sign_sq (K := ℝ) (t i)
      have : (Spin.sign ℝ (t i) - 1) * (Spin.sign ℝ (t i) + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h <;> linarith)

/-! ## GKS-II for the scaled model -/

/-- The duplicate sum after reindexing by the spin-product change of variables. -/
private noncomputable def scaledDuplicateSumChanged (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (A B : Finset ι) : ℝ :=
  ∑ t : Config ι, (1 - spinProduct B t) *
    ∑ ω : Config ι, spinProduct (symmDiff A B) ω * scaledModifiedWeight G E₀ p s t ω

/-- The original scaled duplicate sum equals the changed-variable duplicate sum. -/
private theorem scaledDuplicateSum_eq_changed (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (s : ℝ) (A B : Finset ι) :
    scaledDuplicateSum G E₀ p s A B = scaledDuplicateSumChanged G E₀ p s A B := by
  unfold scaledDuplicateSum scaledDuplicateSumChanged
  have hinner : ∀ ω : Config ι,
      ∑ ω', spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
        scaledBoltzmannWeight G E₀ p s ω * scaledBoltzmannWeight G E₀ p s ω' =
      ∑ t, (1 - spinProduct B t) *
        (spinProduct (symmDiff A B) ω * scaledModifiedWeight G E₀ p s t ω) := by
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
    have hw : scaledBoltzmannWeight G E₀ p s ω * scaledBoltzmannWeight G E₀ p s (φ t) =
        scaledModifiedWeight G E₀ p s t ω :=
      scaledBoltzmannWeight_duplicate_eq G E₀ hE₀_sub p s t ω
    have key : spinProduct A ω * (spinProduct B ω - spinProduct B ω * spinProduct B t) *
        scaledBoltzmannWeight G E₀ p s ω *
        scaledBoltzmannWeight G E₀ p s (φ t) =
        (1 - spinProduct B t) *
        (spinProduct (symmDiff A B) ω * scaledModifiedWeight G E₀ p s t ω) := by
      rw [← hw, ← spinProduct_mul]; ring
    linarith
  simp_rw [hinner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  rw [← Finset.mul_sum]

/-- The changed-variable scaled duplicate sum is non-negative under
ferromagnetic parameters and `s ≥ 0`. -/
private theorem scaledDuplicateSumChanged_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (s : ℝ) (hs : 0 ≤ s) (A B : Finset ι) :
    0 ≤ scaledDuplicateSumChanged G E₀ p s A B := by
  unfold scaledDuplicateSumChanged
  apply Finset.sum_nonneg; intro t _
  apply mul_nonneg (one_sub_spinProduct_nonneg B t)
  exact scaledModifiedWeight_nonneg_corr G E₀ p hf s hs t (symmDiff A B)

/-- **GKS-II for the scaled model**: for ferromagnetic params, `s ≥ 0`, and `E₀ ⊆ G.edgeFinset`,
`⟨σ^A⟩_s · ⟨σ^B⟩_s ≤ ⟨σ^{AΔB}⟩_s`. -/
theorem scaledCorrelation_gks_second (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (s : ℝ) (hs : 0 ≤ s) (A B : Finset ι) :
    scaledCorrelation G E₀ p s A * scaledCorrelation G E₀ p s B ≤
    scaledCorrelation G E₀ p s (symmDiff A B) := by
  have hZ2 : (0 : ℝ) < scaledPartitionFunction G E₀ p s ^ 2 :=
    pow_pos (scaledPartitionFunction_pos G E₀ p s) 2
  have hdup : 0 ≤ scaledDuplicateSum G E₀ p s A B := by
    rw [scaledDuplicateSum_eq_changed G E₀ hE₀_sub p s A B]
    exact scaledDuplicateSumChanged_nonneg G E₀ p hf s hs A B
  rw [scaledDuplicateSum_eq] at hdup
  linarith [nonneg_of_mul_nonneg_right hdup hZ2]


end IsingModel
