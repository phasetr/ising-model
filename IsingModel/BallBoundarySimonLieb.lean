import IsingModel.CouplingDerivative
import IsingModel.Inequalities.GHS

/-!
# Ball-boundary Simon-Lieb inequality (GJ §17.8 infrastructure, Step 136)

Proves the ball-boundary inequality used in GJ §17.8 Thm 17.8.1 (η ≤ 1):

  `⟨σ_r σ_s⟩ ≤ β·J · Σ_{(k,l)∈E₀}
    [⟨σ_r σ_k⟩·⟨σ_s σ_l⟩ + ⟨σ_r σ_l⟩·⟨σ_s σ_k⟩ + ⟨σ_r σ_s⟩·⟨σ_k σ_l⟩]`

under `scaledCorrelation G E₀ p 0 {r,s} = 0` (disconnection at s=0) and `E₀ ⊆ G.edgeFinset`.

## Proof strategy

1. GKS-I for scaled model: `⟨σ^A⟩_s ≥ 0` for ferromagnetic params and `s ≥ 0`.
2. GKS-II for scaled model: `⟨σ^A⟩_s · ⟨σ^B⟩_s ≤ ⟨σ^{AΔB}⟩_s` (duplicate variable trick).
3. Monotonicity: `⟨σ^A⟩_s ≤ ⟨σ^A⟩_1` for `s ≤ 1` (from `d/ds ≥ 0`).
4. MVT: integrate the bounded derivative from 0 to 1.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.8 pp. 316–318, Springer 1987.
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

omit [Fintype ι] [DecidableEq ι] in
/-- Helper: `edgeSpin (φ_t ω) e = edgeSpin ω e * edgeSpin t e`
where `φ_t ω = fun i => Spin.mul (ω i) (t i)`. -/
private lemma edgeSpin_spinMul (ω t : Config ι) (e : Sym2 ι) :
    edgeSpin (K := ℝ) (fun i => Spin.mul (ω i) (t i)) e =
    edgeSpin (K := ℝ) ω e * edgeSpin (K := ℝ) t e := by
  refine Sym2.ind (fun i j => ?_) e
  simp [edgeSpin, Sym2.lift_mk, Spin.sign, Spin.toSign_mul]; ring

/-- Helper: `Spin.sign (Spin.mul ω_i t_i) = Spin.sign ω_i * Spin.sign t_i`. -/
private lemma sign_spinMul (a b : Spin) :
    Spin.sign ℝ (Spin.mul a b) = Spin.sign ℝ a * Spin.sign ℝ b := by
  simp [Spin.sign, Spin.toSign_mul]

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
  simp_rw [edgeSpin_spinMul ω t, sign_spinMul]
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

private noncomputable def scaledDuplicateSumChanged (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (s : ℝ) (A B : Finset ι) : ℝ :=
  ∑ t : Config ι, (1 - spinProduct B t) *
    ∑ ω : Config ι, spinProduct (symmDiff A B) ω * scaledModifiedWeight G E₀ p s t ω

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

/-! ## Monotonicity in s -/

/-- The derivative of `scaledCorrelation G E₀ p s A` in `s` is non-negative for
ferromagnetic params, `s ≥ 0`, `E₀ ⊆ G.edgeFinset`, and non-diagonal `E₀`. -/
theorem scaledCorrelation_deriv_nonneg' (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (s : ℝ) (hs : 0 ≤ s) (A : Finset ι) :
    0 ≤ p.β * p.J * ∑ e ∈ E₀,
      Sym2.lift ⟨fun u v =>
        scaledCorrelation G E₀ p s (symmDiff A {u, v}) -
        scaledCorrelation G E₀ p s A * scaledCorrelation G E₀ p s {u, v},
      fun u v => by simp [Finset.pair_comm v u]⟩ e := by
  apply mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_nonneg; intro e he
  obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  have huv : u ≠ v := by
    intro h; subst h; exact hE₀_nd _ he (Sym2.mk_isDiag_iff.mpr rfl)
  linarith [scaledCorrelation_gks_second G E₀ hE₀_sub p hf s hs A {u, v}]

/-- **Monotonicity of scaled correlation in `s`**: for ferromagnetic params and `0 ≤ s₁ ≤ s₂`,
`⟨σ^A⟩_{s₁} ≤ ⟨σ^A⟩_{s₂}`. -/
theorem scaledCorrelation_monotoneOn (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset ι) :
    MonotoneOn (fun s => scaledCorrelation G E₀ p s A) (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
  · intro s _
    exact (hasDerivAt_scaledCorrelation G E₀ hE₀_nd p s A).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ici] at hs ⊢
    exact (hasDerivAt_scaledCorrelation G E₀ hE₀_nd p s A).hasDerivWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    exact scaledCorrelation_deriv_nonneg' G E₀ hE₀_nd hE₀_sub p hf s hs.le A

/-! ## Ball-boundary inequality -/

/-- The derivative bound constant for the ball-boundary inequality. -/
private noncomputable def derivBound (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (r s : ι) : ℝ :=
  p.β * p.J * ∑ e ∈ E₀,
    Sym2.lift ⟨fun k l =>
      correlation G p {r, k} * correlation G p {s, l} +
      correlation G p {r, l} * correlation G p {s, k} +
      correlation G p {r, s} * correlation G p {k, l},
    fun k l => by simp [Finset.pair_comm k l]; ring⟩ e

/-- Upper bound on `d/ds ⟨σ_r σ_s⟩_s`:
Using GKS-I (drop negative term) + 4-pt monotonicity + full-model Lebowitz. -/
private theorem scaledCorrelation_pair_deriv_le_derivBound (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (r s : ι) (hrs : r ≠ s)
    (hE₀_sep : ∀ e ∈ E₀, ¬ Sym2.Mem r e ∧ ¬ Sym2.Mem s e)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    p.β * p.J * ∑ e ∈ E₀,
      Sym2.lift ⟨fun k l =>
        scaledCorrelation G E₀ p t (symmDiff {r, s} {k, l}) -
        scaledCorrelation G E₀ p t {r, s} *
        scaledCorrelation G E₀ p t {k, l},
      fun k l => by simp [Finset.pair_comm l k]⟩ e ≤
    derivBound G E₀ p r s := by
  unfold derivBound
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_le_sum; intro e he
  obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  have hkl : k ≠ l := by
    intro h; subst h; exact hE₀_nd _ he (Sym2.mk_isDiag_iff.mpr rfl)
  -- Establish p = ⟨p.J, 0, p.β⟩ since p.h = 0
  have hp_eq : p = (⟨p.J, 0, p.β⟩ : IsingParams ℝ) := by
    cases p; simp_all
  -- Drop negative term using GKS-I for scaled model
  have hnn_prod : 0 ≤ scaledCorrelation G E₀ p t {r, s} * scaledCorrelation G E₀ p t {k, l} :=
    mul_nonneg (scaledCorrelation_nonneg G E₀ hE₀_sub p hf t ht0 {r, s})
              (scaledCorrelation_nonneg G E₀ hE₀_sub p hf t ht0 {k, l})
  -- Monotonicity: scaledCorrelation_t ≤ correlation (= scaledCorrelation_1)
  have hmono : scaledCorrelation G E₀ p t (symmDiff {r, s} {k, l}) ≤
      correlation G p (symmDiff {r, s} {k, l}) := by
    have := scaledCorrelation_monotoneOn G E₀ hE₀_nd hE₀_sub p hf (symmDiff {r, s} {k, l})
      (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr zero_le_one) ht1
    simp only [scaledCorrelation_one] at this; exact this
  -- All 4 vertices are distinct by hE₀_sep
  have hrk : r ≠ k := by
    intro h; subst h; exact (hE₀_sep _ he).1 (Sym2.mem_mk_left r l)
  have hrl : r ≠ l := by
    intro h; subst h; exact (hE₀_sep _ he).1 (Sym2.mem_mk_right k r)
  have hsk : s ≠ k := by
    intro h; subst h; exact (hE₀_sep _ he).2 (Sym2.mem_mk_left s l)
  have hsl : s ≠ l := by
    intro h; subst h; exact (hE₀_sep _ he).2 (Sym2.mem_mk_right k s)
  -- Apply summand_le_lebowitz_of_disjoint
  have hf' : Ferromagnetic (⟨p.J, 0, p.β⟩ : IsingParams ℝ) := ⟨hf.hJ, le_refl 0, hf.hβ⟩
  have hleb := summand_le_lebowitz_of_disjoint G p.J p.β hf' r s k l hrs hrk hrl hsk hsl hkl
  rw [← hp_eq] at hleb
  calc scaledCorrelation G E₀ p t (symmDiff {r, s} {k, l}) -
        scaledCorrelation G E₀ p t {r, s} * scaledCorrelation G E₀ p t {k, l}
      ≤ correlation G p (symmDiff {r, s} {k, l}) := by linarith
    _ ≤ correlation G p {r, k} * correlation G p {s, l} +
          correlation G p {r, l} * correlation G p {s, k} +
          correlation G p {r, s} * correlation G p {k, l} := by linarith

/-- The derivative bound is non-negative. -/
private lemma derivBound_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r s : ι) :
    0 ≤ derivBound G E₀ p r s := by
  unfold derivBound
  apply mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_nonneg; intro e _
  obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  apply add_nonneg
  · apply add_nonneg
    · exact mul_nonneg (gks_first G p hf _) (gks_first G p hf _)
    · exact mul_nonneg (gks_first G p hf _) (gks_first G p hf _)
  · exact mul_nonneg (gks_first G p hf _) (gks_first G p hf _)

/-- **Ball-boundary Simon-Lieb inequality** (GJ §17.8, weak form):

For a ferromagnetic Ising model at `h = 0`, edge subset `E₀ ⊆ G.edgeFinset`, and distinct
vertices `r, s` with `scaledCorrelation G E₀ p 0 {r, s} = 0` (disconnected at s=0):

  `⟨σ_r σ_s⟩ ≤ β·J · Σ_{(k,l)∈E₀}
    [⟨σ_r σ_k⟩·⟨σ_s σ_l⟩ + ⟨σ_r σ_l⟩·⟨σ_s σ_k⟩ + ⟨σ_r σ_s⟩·⟨σ_k σ_l⟩]`

The extra `⟨σ_r σ_s⟩·⟨σ_k σ_l⟩` term can be eliminated if Lebowitz holds for the
scaled model (cf. GJ §17.8 eq. 17.8.4 / `cor_4_3_3`).

Reference: Glimm–Jaffe §17.8 pp. 316–318. -/
theorem ball_boundary_simon_lieb (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (r s : ι) (hrs : r ≠ s)
    (hE₀_sep : ∀ e ∈ E₀, ¬ Sym2.Mem r e ∧ ¬ Sym2.Mem s e)
    (h_s0_vanish : scaledCorrelation G E₀ p 0 {r, s} = 0) :
    correlation G p {r, s} ≤ derivBound G E₀ p r s := by
  -- MVT on [0,1]: corr(r,s) = scaledCorr_1 ≤ scaledCorr_0 + derivBound = 0 + derivBound
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s' => scaledCorrelation G E₀ p s' {r, s})
        (p.β * p.J * ∑ e ∈ E₀,
          Sym2.lift ⟨fun u v =>
            scaledCorrelation G E₀ p t (symmDiff {r, s} {u, v}) -
            scaledCorrelation G E₀ p t {r, s} *
            scaledCorrelation G E₀ p t {u, v},
          fun u v => by simp [Finset.pair_comm v u]⟩ e)
        (Set.Icc 0 1) t :=
    fun t _ => (hasDerivAt_scaledCorrelation G E₀ hE₀_nd p t {r, s}).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖p.β * p.J * ∑ e ∈ E₀,
          Sym2.lift ⟨fun u v =>
            scaledCorrelation G E₀ p t (symmDiff {r, s} {u, v}) -
            scaledCorrelation G E₀ p t {r, s} *
            scaledCorrelation G E₀ p t {u, v},
          fun u v => by simp [Finset.pair_comm v u]⟩ e‖ ≤
      ‖derivBound G E₀ p r s‖ := by
    intro t ht
    rw [Real.norm_of_nonneg
          (scaledCorrelation_deriv_nonneg' G E₀ hE₀_nd hE₀_sub p hf t ht.1 {r, s}),
        Real.norm_of_nonneg (derivBound_nonneg G E₀ p hf r s)]
    exact scaledCorrelation_pair_deriv_le_derivBound G E₀ hE₀_nd hE₀_sub p hf hh r s hrs
      hE₀_sep t ht.1 ht.2.le
  -- Apply MVT on [0,1]
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  -- hmvt : ‖scaledCorrelation G E₀ p 1 {r,s} - scaledCorrelation G E₀ p 0 {r,s}‖ ≤ ‖derivBound ...‖
  rw [scaledCorrelation_one G E₀ p {r, s}, h_s0_vanish, sub_zero] at hmvt
  rw [Real.norm_of_nonneg (gks_first G p hf {r, s}),
      Real.norm_of_nonneg (derivBound_nonneg G E₀ p hf r s)] at hmvt
  linarith

/-! ## Tight ball-boundary inequality (Step 137 support)

The tight form removes the extra `⟨σ_r σ_s⟩·⟨σ_k σ_l⟩` term using Lebowitz for the scaled model.
-/

/-- **Odd-cardinality scaled correlations vanish at `h = 0`**:
The scaled model has global spin-flip symmetry when `h = 0`,
so `⟨σ^A⟩_s = 0` for odd `|A|`. -/
theorem scaledCorrelation_odd_vanish (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (hh : p.h = 0)
    (s : ℝ) (A : Finset ι) (hodd : Odd A.card) :
    scaledCorrelation G E₀ p s A = 0 := by
  simp only [scaledCorrelation, scaledGibbsExpectation]
  suffices hsum : ∑ σ : Config ι,
      spinProduct A σ * scaledBoltzmannWeight G E₀ p s σ = 0 by
    rw [hsum, mul_zero]
  -- Scaled Boltzmann weight is flip-invariant at h=0
  have hbw : ∀ σ : Config ι,
      scaledBoltzmannWeight G E₀ p s σ.flip = scaledBoltzmannWeight G E₀ p s σ := by
    intro σ
    simp only [scaledBoltzmannWeight, boltzmannWeight, hamiltonian_flip_eq G p hh σ]
    simp_rw [edgeSpin_flip]
  -- spinProduct negates under flip for odd |A|
  have hflip : ∀ σ : Config ι,
      spinProduct A σ.flip * scaledBoltzmannWeight G E₀ p s σ.flip =
      -(spinProduct A σ * scaledBoltzmannWeight G E₀ p s σ) := by
    intro σ
    rw [hbw σ]
    have hsp : spinProduct A σ.flip = (-1 : ℝ) ^ A.card * spinProduct A σ := by
      simp only [spinProduct, Config.flip]
      simp_rw [Spin.toSign_flip, Int.cast_neg]
      exact Finset.prod_neg _
    rw [hsp]; obtain ⟨k, hk⟩ := hodd; rw [hk]; ring_nf; simp
  -- Reindex via flip: sum = -sum → sum = 0
  let flipEquiv : Equiv.Perm (Config ι) :=
    ⟨Config.flip, Config.flip, Config.flip_flip, Config.flip_flip⟩
  have hreindex : ∑ σ : Config ι,
      spinProduct A σ * scaledBoltzmannWeight G E₀ p s σ =
    ∑ σ : Config ι,
      spinProduct A σ.flip * scaledBoltzmannWeight G E₀ p s σ.flip :=
    (Equiv.sum_comp flipEquiv _).symm
  have hsum2 : ∑ σ : Config ι,
      spinProduct A σ.flip * scaledBoltzmannWeight G E₀ p s σ.flip =
    -(∑ σ : Config ι, spinProduct A σ * scaledBoltzmannWeight G E₀ p s σ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun σ _ => hflip σ)
  linarith [hreindex.trans hsum2]

/-- **Cor. 4.3.3 for the scaled model** (new independent axiom).

For ferromagnetic `p` with `h = 0`, `s ≥ 0`, and four distinct sites `r, a, k, l`:
`scaledCorrelation G E₀ p s (symmDiff {r,a} {k,l}) ≤`
`  scaledCorrelation G E₀ p s {r,a} · scaledCorrelation G E₀ p s {k,l}`
`+ scaledCorrelation G E₀ p s {r,k} · scaledCorrelation G E₀ p s {a,l}`
`+ scaledCorrelation G E₀ p s {r,l} · scaledCorrelation G E₀ p s {a,k}`

This is a **new independent axiom** for models with non-uniform couplings
(`J_e = sJ` for `e ∈ E₀`, `J_e = J` for `e ∉ E₀`). It is mathematically valid via
the φ⁴ approximation argument (same structure as `lebowitz_four` + Cor. 4.3.3 in GHS.lean):
(1) `lebowitz_four_scaled` (a 4-site Lebowitz axiom for the scaled model);
(2) At `h = 0`, 1-point and 3-point scaled correlations vanish (`scaledCorrelation_odd_vanish`);
(3) The symmDiff form follows from `{r,a} ∩ {k,l} = ∅`.
The current repo's `lebowitz_four` covers only uniform couplings and does not directly apply.

References: Glimm–Jaffe §4.3 Cor. 4.3.3 (p. 61); cf. `cor_4_3_3` and `lebowitz_four` in GHS.lean. -/
axiom cor_4_3_3_scaled (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (s : ℝ) (hs : 0 ≤ s) (r a k l : ι)
    (hra : r ≠ a) (hrk : r ≠ k) (hrl : r ≠ l)
    (hak : a ≠ k) (hal : a ≠ l) (hkl : k ≠ l) :
    scaledCorrelation G E₀ p s (symmDiff {r, a} {k, l}) ≤
    scaledCorrelation G E₀ p s {r, a} * scaledCorrelation G E₀ p s {k, l} +
    scaledCorrelation G E₀ p s {r, k} * scaledCorrelation G E₀ p s {a, l} +
    scaledCorrelation G E₀ p s {r, l} * scaledCorrelation G E₀ p s {a, k}

/-- **Tight Lebowitz bound for the scaled model** (disjoint case, h=0):
`⟨σ^{AΔe}⟩_s − ⟨σ^A⟩_s·⟨σ^e⟩_s ≤ ⟨σ_r σ_k⟩_s·⟨σ_a σ_l⟩_s + ⟨σ_r σ_l⟩_s·⟨σ_a σ_k⟩_s`
for `A = {r,a}`, `e = {k,l}` disjoint (4 distinct sites). -/
theorem summand_le_lebowitz_of_disjoint_scaled (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (r a k l : ι) (hra : r ≠ a) (hrk : r ≠ k) (hrl : r ≠ l)
    (hak : a ≠ k) (hal : a ≠ l) (hkl : k ≠ l) :
    scaledCorrelation G E₀ p s (symmDiff {r, a} {k, l}) -
    scaledCorrelation G E₀ p s {r, a} * scaledCorrelation G E₀ p s {k, l} ≤
    scaledCorrelation G E₀ p s {r, k} * scaledCorrelation G E₀ p s {a, l} +
    scaledCorrelation G E₀ p s {r, l} * scaledCorrelation G E₀ p s {a, k} := by
  have h := cor_4_3_3_scaled G E₀ hE₀_sub p hf hh s hs r a k l hra hrk hrl hak hal hkl
  linarith

/-- The tight derivative bound constant (no extra `⟨σ_r σ_s⟩·⟨σ_k σ_l⟩` term). -/
private noncomputable def derivBoundTight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (r s : ι) : ℝ :=
  p.β * p.J * ∑ e ∈ E₀,
    Sym2.lift ⟨fun k l =>
      correlation G p {r, k} * correlation G p {s, l} +
      correlation G p {r, l} * correlation G p {s, k},
    fun k l => by simp only [Finset.pair_comm]; ring⟩ e

/-- The tight derivative bound is non-negative. -/
private lemma derivBoundTight_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r s : ι) :
    0 ≤ derivBoundTight G E₀ p r s := by
  unfold derivBoundTight
  apply mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_nonneg; intro e _
  obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  apply add_nonneg
  · exact mul_nonneg (gks_first G p hf _) (gks_first G p hf _)
  · exact mul_nonneg (gks_first G p hf _) (gks_first G p hf _)

/-- The tight upper bound on `d/ds ⟨σ_r σ_s⟩_s` (without extra `⟨σ_r σ_s⟩·⟨σ_k σ_l⟩`). -/
private theorem scaledCorrelation_pair_deriv_le_derivBoundTight
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (r s : ι) (hrs : r ≠ s)
    (hE₀_sep : ∀ e ∈ E₀, ¬ Sym2.Mem r e ∧ ¬ Sym2.Mem s e)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    p.β * p.J * ∑ e ∈ E₀,
      Sym2.lift ⟨fun k l =>
        scaledCorrelation G E₀ p t (symmDiff {r, s} {k, l}) -
        scaledCorrelation G E₀ p t {r, s} *
        scaledCorrelation G E₀ p t {k, l},
      fun k l => by simp [Finset.pair_comm l k]⟩ e ≤
    derivBoundTight G E₀ p r s := by
  unfold derivBoundTight
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_le_sum; intro e he
  obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  have hkl : k ≠ l := by
    intro h; subst h; exact hE₀_nd _ he (Sym2.mk_isDiag_iff.mpr rfl)
  have hrk : r ≠ k := by
    intro h; subst h; exact (hE₀_sep _ he).1 (Sym2.mem_mk_left r l)
  have hrl : r ≠ l := by
    intro h; subst h; exact (hE₀_sep _ he).1 (Sym2.mem_mk_right k r)
  have hsk : s ≠ k := by
    intro h; subst h; exact (hE₀_sep _ he).2 (Sym2.mem_mk_left s l)
  have hsl : s ≠ l := by
    intro h; subst h; exact (hE₀_sep _ he).2 (Sym2.mem_mk_right k s)
  have hf' : Ferromagnetic (⟨p.J, 0, p.β⟩ : IsingParams ℝ) := ⟨hf.hJ, le_refl 0, hf.hβ⟩
  -- Use tight Lebowitz for scaled model
  have hleb := summand_le_lebowitz_of_disjoint_scaled G E₀ hE₀_sub p hf hh t ht0
                 r s k l hrs hrk hrl hsk hsl hkl
  -- Monotonicity: scaled correlation at t ≤ correlation at 1 = full correlation
  have hmono_rk : scaledCorrelation G E₀ p t {r, k} ≤ correlation G p {r, k} := by
    have := scaledCorrelation_monotoneOn G E₀ hE₀_nd hE₀_sub p hf {r, k}
      (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr zero_le_one) ht1
    simp only [scaledCorrelation_one] at this; exact this
  have hmono_sl : scaledCorrelation G E₀ p t {s, l} ≤ correlation G p {s, l} := by
    have := scaledCorrelation_monotoneOn G E₀ hE₀_nd hE₀_sub p hf {s, l}
      (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr zero_le_one) ht1
    simp only [scaledCorrelation_one] at this; exact this
  have hmono_rl : scaledCorrelation G E₀ p t {r, l} ≤ correlation G p {r, l} := by
    have := scaledCorrelation_monotoneOn G E₀ hE₀_nd hE₀_sub p hf {r, l}
      (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr zero_le_one) ht1
    simp only [scaledCorrelation_one] at this; exact this
  have hmono_sk : scaledCorrelation G E₀ p t {s, k} ≤ correlation G p {s, k} := by
    have := scaledCorrelation_monotoneOn G E₀ hE₀_nd hE₀_sub p hf {s, k}
      (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr zero_le_one) ht1
    simp only [scaledCorrelation_one] at this; exact this
  have hnn_rk : 0 ≤ scaledCorrelation G E₀ p t {r, k} :=
    scaledCorrelation_nonneg G E₀ hE₀_sub p hf t ht0 _
  have hnn_sl : 0 ≤ scaledCorrelation G E₀ p t {s, l} :=
    scaledCorrelation_nonneg G E₀ hE₀_sub p hf t ht0 _
  have hnn_rl : 0 ≤ scaledCorrelation G E₀ p t {r, l} :=
    scaledCorrelation_nonneg G E₀ hE₀_sub p hf t ht0 _
  have hnn_sk : 0 ≤ scaledCorrelation G E₀ p t {s, k} :=
    scaledCorrelation_nonneg G E₀ hE₀_sub p hf t ht0 _
  calc scaledCorrelation G E₀ p t (symmDiff {r, s} {k, l}) -
        scaledCorrelation G E₀ p t {r, s} * scaledCorrelation G E₀ p t {k, l}
      ≤ scaledCorrelation G E₀ p t {r, k} * scaledCorrelation G E₀ p t {s, l} +
        scaledCorrelation G E₀ p t {r, l} * scaledCorrelation G E₀ p t {s, k} := hleb
    _ ≤ correlation G p {r, k} * correlation G p {s, l} +
        correlation G p {r, l} * correlation G p {s, k} := by
          apply add_le_add
          · exact mul_le_mul hmono_rk hmono_sl hnn_sl (gks_first G p hf _)
          · exact mul_le_mul hmono_rl hmono_sk hnn_sk (gks_first G p hf _)

/-- **Tight ball-boundary Simon-Lieb inequality** (GJ §17.8 eq. 17.8.4, tight form):

For a ferromagnetic Ising model at `h = 0`, edge subset `E₀ ⊆ G.edgeFinset`, and distinct
vertices `r, s` with `scaledCorrelation G E₀ p 0 {r, s} = 0`:

  `⟨σ_r σ_s⟩ ≤ β·J · Σ_{(k,l)∈E₀}
    [⟨σ_r σ_k⟩·⟨σ_s σ_l⟩ + ⟨σ_r σ_l⟩·⟨σ_s σ_k⟩]`

This is the tight form without the extra `⟨σ_r σ_s⟩·⟨σ_k σ_l⟩` term.

Reference: Glimm–Jaffe §17.8 eq. 17.8.4–17.8.5, pp. 316–318. -/
theorem ball_boundary_simon_lieb_tight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (r s : ι) (hrs : r ≠ s)
    (hE₀_sep : ∀ e ∈ E₀, ¬ Sym2.Mem r e ∧ ¬ Sym2.Mem s e)
    (h_s0_vanish : scaledCorrelation G E₀ p 0 {r, s} = 0) :
    correlation G p {r, s} ≤ derivBoundTight G E₀ p r s := by
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s' => scaledCorrelation G E₀ p s' {r, s})
        (p.β * p.J * ∑ e ∈ E₀,
          Sym2.lift ⟨fun u v =>
            scaledCorrelation G E₀ p t (symmDiff {r, s} {u, v}) -
            scaledCorrelation G E₀ p t {r, s} *
            scaledCorrelation G E₀ p t {u, v},
          fun u v => by simp [Finset.pair_comm v u]⟩ e)
        (Set.Icc 0 1) t :=
    fun t _ => (hasDerivAt_scaledCorrelation G E₀ hE₀_nd p t {r, s}).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖p.β * p.J * ∑ e ∈ E₀,
          Sym2.lift ⟨fun u v =>
            scaledCorrelation G E₀ p t (symmDiff {r, s} {u, v}) -
            scaledCorrelation G E₀ p t {r, s} *
            scaledCorrelation G E₀ p t {u, v},
          fun u v => by simp [Finset.pair_comm v u]⟩ e‖ ≤
      ‖derivBoundTight G E₀ p r s‖ := by
    intro t ht
    rw [Real.norm_of_nonneg
          (scaledCorrelation_deriv_nonneg' G E₀ hE₀_nd hE₀_sub p hf t ht.1 {r, s}),
        Real.norm_of_nonneg (derivBoundTight_nonneg G E₀ p hf r s)]
    exact scaledCorrelation_pair_deriv_le_derivBoundTight G E₀ hE₀_nd hE₀_sub p hf hh r s hrs
      hE₀_sep t ht.1 ht.2.le
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  rw [scaledCorrelation_one G E₀ p {r, s}, h_s0_vanish, sub_zero] at hmvt
  rw [Real.norm_of_nonneg (gks_first G p hf {r, s}),
      Real.norm_of_nonneg (derivBoundTight_nonneg G E₀ p hf r s)] at hmvt
  linarith

end IsingModel
