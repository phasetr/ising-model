import IsingModel.Conditioning.HighTempClosed

/-!
# Correlation closed form split — free-boundary high-temperature h=0 closed form

Part of the split `IsingModel.Conditioning.CorrelationClosed` development.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Free-boundary correlation closed form -/

/-- **`spinProduct` as vertex-power**: for any `A : Finset ι`,
`∏_{a ∈ A} (σ a).toSign = ∏_v (σ v).toSign^(if v ∈ A then 1 else 0)`. -/
private theorem spinProduct_eq_prod_pow_indicator
    (A : Finset ι) (σ : Config ι) :
    spinProduct A σ
      = ∏ v : ι, ((σ v).toSign : ℝ) ^ (if v ∈ A then (1 : ℕ) else 0) := by
  classical
  unfold spinProduct
  rw [show (A : Finset ι) = (Finset.univ : Finset ι).filter (· ∈ A) by
    ext v; simp]
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  by_cases hv : v ∈ A <;> simp [hv]

/-- **σ-sum of `spinProduct A · edgeSpin product`**: for `X ⊆ G.edgeFinset`,
`∑_σ spinProduct A σ · ∏_{e ∈ X} edgeSpin σ e = 2^|ι|` if the parity
of every vertex `v` matches `(v ∈ A)` (i.e. `deg_X v + 1_A v` is even),
else `0`. This is the free-boundary parity step analogous to the pinned-boundary
calculation behind FV (3.46). -/
private theorem sum_spinProduct_mul_prod_edgeSpin_eq_pow_card_or_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (X : Finset (Sym2 ι))
    (hX : X ⊆ G.edgeFinset) (A : Finset ι) :
    (∑ σ : Config ι,
      spinProduct A σ * ∏ e ∈ X, edgeSpin (K := ℝ) σ e)
      = if (∀ v : ι,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card))
        then (2 : ℝ) ^ Fintype.card ι else 0 := by
  classical
  -- Combine the indicator-power form of σ_A with the edge → vertex-power
  -- bridge from Step 283.
  have hcombine : ∀ σ : Config ι,
      spinProduct A σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e)
        = ∏ v : ι, ((σ v).toSign : ℝ) ^
            ((if v ∈ A then (1 : ℕ) else 0)
             + (X.filter (v ∈ ·)).card) := by
    intro σ
    rw [spinProduct_eq_prod_pow_indicator A σ,
        prod_edgeSpin_eq_prod_pow_filter_card G X hX σ,
        ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [← pow_add]
  simp_rw [hcombine]
  exact sum_prod_toSign_pow_real
    (k := fun v => (if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)

/-- **Numerator high-temperature expansion (h = 0)**: for any `A : Finset ι`,
`∑_σ spinProduct A σ · boltzmannWeight G ⟨J,0,β⟩ σ
  = 2^|ι| · cosh(βJ)^|E| · ∑_{X ⊆ E : every v has parity (v ∈ A)} tanh(βJ)^|X|`,
where the parity condition `(v ∈ A)` means `deg_X v + 1_A v` is even.
Companion to `partitionFunction_high_temp_expansion_h_zero_closed`
for the numerator of `correlation G ⟨J,0,β⟩ A`. -/
private theorem sum_spinProduct_boltzmannWeight_h_zero_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) :
    (∑ σ : Config ι,
      spinProduct A σ * boltzmannWeight G ⟨J, 0, β⟩ σ)
      = (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card := by
  -- Same skeleton as `partitionFunction_high_temp_expansion_h_zero_closed`
  -- but carrying a `spinProduct A σ` factor.
  have hboltz_h_zero : ∀ σ : Config ι,
      boltzmannWeight G ⟨J, 0, β⟩ σ
        = ∏ e ∈ G.edgeFinset, Real.exp (β * J * edgeSpin σ e) := by
    intro σ
    unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
    rw [show -β *
            (-J * ∑ e ∈ G.edgeFinset, edgeSpin σ e
              + -(0 : ℝ) * ∑ i : ι, Spin.sign ℝ (σ i))
          = (β * J) * (∑ e ∈ G.edgeFinset, edgeSpin σ e) from by ring,
        Finset.mul_sum, Real.exp_sum]
  simp_rw [hboltz_h_zero]
  have hedge_decomp : ∀ σ : Config ι, ∀ e ∈ G.edgeFinset,
      Real.exp (β * J * edgeSpin σ e) =
        Real.cosh (β * J) * (1 + Real.tanh (β * J) * edgeSpin σ e) := by
    intros σ e _
    rw [exp_edgeSpin_decomp, Real.tanh_eq_sinh_div_cosh]
    have hcosh_ne : Real.cosh (β * J) ≠ 0 := (Real.cosh_pos _).ne'
    field_simp
  simp_rw [fun σ =>
    Finset.prod_congr rfl (hedge_decomp σ)]
  simp_rw [Finset.prod_mul_distrib, Finset.prod_const]
  -- ∑_σ spinProduct A σ · cosh^|E| · ∏_e (1 + ...) = cosh^|E| · ∑_σ spinProduct A σ · ∏_e (1+...)
  rw [show (∑ σ : Config ι, spinProduct A σ *
        (Real.cosh (β * J) ^ G.edgeFinset.card *
          ∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e)))
      = Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ σ : Config ι, spinProduct A σ *
          ∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    ring]
  -- Subset expansion
  have hexpand : ∀ σ : Config ι,
      (∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e))
        = ∑ X ∈ G.edgeFinset.powerset,
            ∏ e ∈ X, (Real.tanh (β * J) * edgeSpin σ e) := fun σ =>
    Finset.prod_one_add G.edgeFinset
  simp_rw [hexpand]
  -- Pull tanh^|X| out
  have hpull : ∀ σ : Config ι, ∀ X : Finset (Sym2 ι),
      (∏ e ∈ X, (Real.tanh (β * J) * edgeSpin σ e))
        = Real.tanh (β * J) ^ X.card *
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) := by
    intros σ X
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [hpull]
  -- Distribute spinProduct A σ over the X-sum
  rw [show (∑ σ : Config ι, spinProduct A σ *
        ∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card * (∏ e ∈ X, edgeSpin (K := ℝ) σ e))
      = ∑ σ : Config ι,
        ∑ X ∈ G.edgeFinset.powerset,
          spinProduct A σ * (Real.tanh (β * J) ^ X.card *
            ∏ e ∈ X, edgeSpin (K := ℝ) σ e) by
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.mul_sum]]
  -- Swap σ ↔ X and pull tanh^|X| out further
  rw [Finset.sum_comm]
  rw [show (∑ X ∈ G.edgeFinset.powerset, ∑ σ : Config ι,
        spinProduct A σ * (Real.tanh (β * J) ^ X.card *
          ∏ e ∈ X, edgeSpin (K := ℝ) σ e))
      = ∑ X ∈ G.edgeFinset.powerset,
        Real.tanh (β * J) ^ X.card *
          ∑ σ : Config ι,
            spinProduct A σ * ∏ e ∈ X, edgeSpin (K := ℝ) σ e by
    refine Finset.sum_congr rfl (fun X _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    ring]
  -- Apply parity collapse
  have hparity : ∀ X ∈ G.edgeFinset.powerset,
      (∑ σ : Config ι,
        spinProduct A σ * ∏ e ∈ X, edgeSpin (K := ℝ) σ e)
        = if (∀ v : ι,
              Even ((if v ∈ A then (1 : ℕ) else 0)
                    + (X.filter (v ∈ ·)).card))
          then (2 : ℝ) ^ Fintype.card ι else 0 := fun X hX =>
    sum_spinProduct_mul_prod_edgeSpin_eq_pow_card_or_zero G X
      (Finset.mem_powerset.mp hX) A
  rw [Finset.sum_congr rfl
    (fun X hX => by rw [hparity X hX])]
  -- Distribute and collapse via filter
  have hdist : ∀ X : Finset (Sym2 ι),
      Real.tanh (β * J) ^ X.card *
          (if (∀ v : ι,
                Even ((if v ∈ A then (1 : ℕ) else 0)
                      + (X.filter (v ∈ ·)).card))
            then (2 : ℝ) ^ Fintype.card ι else 0)
        = (if (∀ v : ι,
                Even ((if v ∈ A then (1 : ℕ) else 0)
                      + (X.filter (v ∈ ·)).card))
            then (2 : ℝ) ^ Fintype.card ι * Real.tanh (β * J) ^ X.card
            else 0) := fun X => by
    by_cases h : ∀ v : ι, Even ((if v ∈ A then (1 : ℕ) else 0)
                                + (X.filter (v ∈ ·)).card)
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  simp_rw [hdist]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  ring

/-- **Free-boundary correlation closed form at h = 0.**
This arbitrary-observable formula is a free-boundary generalization of the parity expansion behind
Friedli--Velenik §3.7.3, equation (3.46); that equation itself is a plus-boundary singleton ratio:
\[
\langle \sigma_A \rangle_{\beta, 0} =
  \frac{\sum_{X \subseteq E,\, \partial X = A} \tanh(\beta J)^{|X|}}
       {\sum_{X \subseteq E,\, \partial X = \emptyset} \tanh(\beta J)^{|X|}},
\]
where the boundary condition `∂X = A` is encoded as
`∀ v, Even ((1_A v) + (X.filter (v ∈ ·)).card)` (i.e. the parity
of the X-degree at every vertex `v` matches whether `v ∈ A`).

The `2^{|\iota|} \cdot (\cosh \beta J)^{|E|}` prefactor cancels between
numerator and denominator. Combines
`partitionFunction_high_temp_expansion_h_zero_closed` (Step 283) with
`sum_spinProduct_boltzmannWeight_h_zero_closed`.

Reference for the analogous parity expansion: FV §3.7.3, equation (3.46), p. 117 (2017 ed.). -/
theorem correlation_high_temp_expansion_h_zero_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) :
    correlation G ⟨J, 0, β⟩ A =
      (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card) /
      (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card) := by
  unfold correlation gibbsExpectation
  rw [sum_spinProduct_boltzmannWeight_h_zero_closed G J β A,
      partitionFunction_high_temp_expansion_h_zero_closed G J β]
  -- Now: (Z_closed)⁻¹ * N_closed = N_subsum / Z_subsum
  set N_sub : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X => ∀ v : ι,
        Even ((if v ∈ A then (1 : ℕ) else 0)
              + (X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hN_sub
  set Z_sub : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hZ_sub
  -- Goal: ((2^|ι|·cosh^|E|·Z_sub))⁻¹ · (2^|ι|·cosh^|E|·N_sub) = N_sub / Z_sub
  have hcommon_pos :
      (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card := by
    apply mul_pos
    · exact pow_pos (by norm_num) _
    · exact pow_pos (Real.cosh_pos _) _
  have hcommon_ne : (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card ≠ 0 :=
    hcommon_pos.ne'
  field_simp


end IsingModel
