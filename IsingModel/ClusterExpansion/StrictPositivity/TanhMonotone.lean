import IsingModel.ClusterExpansion.StrictPositivity.MayerPartialFerro

/-!
# Cluster expansion strict positivity split — polymer free energy tanh monotonicity in beta and J

Part of the split cluster-expansion strict-positivity layer (Issue #1850).
-/

namespace IsingModel

open Finset

/-! ## §18.4 polymerFreeEnergy tanh monotonicity in β / J bundle

`polymerFreeEnergy(tanh(β·J))` is strictly increasing in β at fixed
`J > 0` and in J at fixed `β > 0`, when polymers exist. Proof
combines `polymerFreeEnergy_lt_of_lt_of_polymers_nonempty` (PR #1559)
with the strict monotonicity of `Real.tanh` (proved here as a local
helper from `sinh_strictMono`). -/

/-- **`polymerFreeEnergy(tanh(β·J))` strictly increasing in β at fixed
`J > 0` under polymers exist** (§18.4 tanh-monotonicity bundle). -/
theorem polymerFreeEnergy_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty)
    {β₁ β₂ J : ℝ} (hβ₁ : 0 ≤ β₁) (hJ : 0 < J) (hβ : β₁ < β₂) :
    polymerFreeEnergy G (Real.tanh (β₁ * J)) <
      polymerFreeEnergy G (Real.tanh (β₂ * J)) := by
  apply polymerFreeEnergy_lt_of_lt_of_polymers_nonempty G h_poly
  · exact real_tanh_nonneg (mul_nonneg hβ₁ hJ.le)
  · exact real_tanh_strictMono (mul_lt_mul_of_pos_right hβ hJ)

/-- **`polymerFreeEnergy(tanh(β·J))` strictly increasing in J at fixed
`β > 0` under polymers exist** (§18.4 tanh-monotonicity bundle). -/
theorem polymerFreeEnergy_tanh_lt_of_lt_in_J_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty)
    {β J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hβ : 0 < β) (hJ : J₁ < J₂) :
    polymerFreeEnergy G (Real.tanh (β * J₁)) <
      polymerFreeEnergy G (Real.tanh (β * J₂)) := by
  apply polymerFreeEnergy_lt_of_lt_of_polymers_nonempty G h_poly
  · exact real_tanh_nonneg (mul_nonneg hβ.le hJ₁)
  · exact real_tanh_strictMono (mul_lt_mul_of_pos_left hJ hβ)

/-- **`polymerFreeEnergy(tanh(β·J))` is `StrictMonoOn (Set.Ici 0)` in β**
under fixed `J > 0` and polymers exist (§18.4). -/
theorem polymerFreeEnergy_tanh_strictMonoOn_beta_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty)
    {J : ℝ} (hJ : 0 < J) :
    StrictMonoOn (fun β : ℝ => polymerFreeEnergy G (Real.tanh (β * J)))
      (Set.Ici 0) :=
  fun _ hβ₁ _ _ hβ =>
    polymerFreeEnergy_tanh_lt_of_lt_in_beta_of_polymers_nonempty
      G h_poly hβ₁ hJ hβ

/-- **`polymerFreeEnergy(tanh(β·J))` is `StrictMonoOn (Set.Ici 0)` in J**
under fixed `β > 0` and polymers exist (§18.4). -/
theorem polymerFreeEnergy_tanh_strictMonoOn_J_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun J : ℝ => polymerFreeEnergy G (Real.tanh (β * J)))
      (Set.Ici 0) :=
  fun _ hJ₁ _ _ hJ =>
    polymerFreeEnergy_tanh_lt_of_lt_in_J_of_polymers_nonempty
      G h_poly hJ₁ hβ hJ



end IsingModel
