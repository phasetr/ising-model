import IsingModel.ClusterExpansion.StrictPositivity.StrictMono

/-!
# Cluster expansion strict positivity split — Mayer partial sum and ferromagnetic strict/iff bundle

Part of the split cluster-expansion strict-positivity layer (Issue #1850).
-/

namespace IsingModel

open Finset

/-! ## §18.4 mayerPartialSum strict positivity / sign bundle

Sign characterisations of `mayerPartialSum` at small N: positivity at
N=1 under `t > 0` and polymers exist; non-positive contribution from
n=2 Mayer term. Bundle of corollaries derivable from existing
mayerExpansionTerm explicit forms (Steps 587, 593, 614, 637). -/

/-- **`mayerPartialSum G 1 t > 0` under `0 < t` and polymers exist**
(§18.4 strict-pos bundle): `mayerPartialSum G 1 t = ∑_{P ∈ allPolymers} t^|P|`
(Step 592), each summand `t^|P| > 0` when `t > 0` and `|P| ≥ 1`, so
the total is positive when `allPolymers G ≠ ∅`. -/
theorem mayerPartialSum_one_pos_of_t_pos_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (h_poly : (allPolymers G).Nonempty) :
    0 < mayerPartialSum G 1 t := by
  rw [mayerPartialSum_one]
  apply Finset.sum_pos
  · intro P hP
    have hP_polymer : IsPolymer G P := mem_allPolymers.mp hP
    have hP_card_pos : 0 < P.card := Finset.card_pos.mpr hP_polymer.nonempty
    exact pow_pos h_t_pos _
  · exact h_poly

/-- **`mayerPartialSum G 1 t ≥ 0` under `0 ≤ t`** (§18.4): total
polymer activity is non-negative. -/
theorem mayerPartialSum_one_nonneg_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ mayerPartialSum G 1 t := by
  rw [mayerPartialSum_one]
  exact Finset.sum_nonneg (fun _ _ => pow_nonneg ht _)

/-! ## §18.4 ferromagnetic strict / iff bundle (J ≥ 0, β ≥ 0)

Ferromagnetic forms of the recent tanh-based iff / strict-mono /
strict-pos theorems. Convention: `J ≥ 0` and `β ≥ 0` (ferromagnetic
high-temperature regime), so `0 ≤ β·J` follows from `mul_nonneg`. -/

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_lt_eps_iff_eps_pos`** under
`J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_lt_eps_iff_eps_pos_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    polymerFreeEnergy G (Real.tanh (β * J)) <
        ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_tanh_lt_eps_iff_eps_pos G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero`** under
`J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    polymerFreeEnergy G (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_pos_iff_eps_pos`** under
`J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_pos_iff_eps_pos_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < polymerFreeEnergy G (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_tanh_pos_iff_eps_pos G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_pos_iff`** characterising via
`tanh > 0 ∧ polymers exist` under `J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_pos_iff_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < polymerFreeEnergy G (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧ (allPolymers G).Nonempty :=
  polymerFreeEnergy_tanh_pos_iff G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_eq_zero_iff`** characterising
via `tanh = 0 ∨ no polymers` under `J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_eq_zero_iff_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    polymerFreeEnergy G (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨ allPolymers G = ∅ :=
  polymerFreeEnergy_tanh_eq_zero_iff G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `vdSum > 1 ↔ tanh > 0 ∧ polymers exist`** under
`J ≥ 0` and `β ≥ 0`. -/
theorem vdPolymerFamilies_sum_tanh_gt_one_iff_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    1 < (∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧ (allPolymers G).Nonempty :=
  vdPolymerFamilies_sum_tanh_gt_one_iff G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `vdSum = 1 ↔ tanh = 0 ∨ no polymers`** under
`J ≥ 0` and `β ≥ 0`. -/
theorem vdPolymerFamilies_sum_tanh_eq_one_iff_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨ allPolymers G = ∅ :=
  vdPolymerFamilies_sum_tanh_eq_one_iff G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos`**
under `J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    polymerFreeEnergy G (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^ G.edgeFinset.card - 1 :=
  polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos G (mul_nonneg hβ hJ) h_eps_pos

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_lt_eps_of_eps_pos`** under
`J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_lt_eps_of_eps_pos_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    polymerFreeEnergy G (Real.tanh (β * J)) <
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_tanh_lt_eps_of_eps_pos G (mul_nonneg hβ hJ) h_eps_pos


end IsingModel
