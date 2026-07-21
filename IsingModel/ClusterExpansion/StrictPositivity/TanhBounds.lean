import IsingModel.ClusterExpansion.HighTempGeneralRegularity

/-!
# Cluster expansion strict positivity split — tanh-substituted strict and iff bounds

Part of the split cluster-expansion strict-positivity layer (Issue #1850).
-/

namespace IsingModel

open Finset

/-! ## Tanh-substituted forms of the new strict / iff polymerFreeEnergy bounds -/

/-- **`polymerFreeEnergy < ε(tanh) ↔ ε(tanh) > 0` under `0 ≤ β·J`** (§18.4
sharpening, tanh form): tanh-substituted form of
`polymerFreeEnergy_lt_eps_iff_eps_pos`. -/
theorem polymerFreeEnergy_tanh_lt_eps_iff_eps_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) <
        ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_lt_eps_iff_eps_pos G (real_tanh_nonneg hβJ)

/-- **`polymerFreeEnergy = 0 ↔ ε(tanh) = 0` under `0 ≤ β·J`** (§18.4
sharpening, tanh form). -/
theorem polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  polymerFreeEnergy_eq_zero_iff_eps_eq_zero G (real_tanh_nonneg hβJ)

/-- **`0 < polymerFreeEnergy ↔ 0 < ε(tanh)` under `0 ≤ β·J`** (§18.4
sharpening, tanh form). -/
theorem polymerFreeEnergy_tanh_pos_iff_eps_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < polymerFreeEnergy G (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_pos_iff_eps_pos G (real_tanh_nonneg hβJ)

/-- **`polymerFreeEnergy < ε(tanh) when ε(tanh) > 0` under `0 ≤ β·J`**
(§18.4 sharpening, tanh form). -/
theorem polymerFreeEnergy_tanh_lt_eps_of_eps_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (_ : 0 ≤ β * J)
    (h_eps_pos : 0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    polymerFreeEnergy G (Real.tanh (β * J)) <
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_lt_eps_of_eps_pos G h_eps_pos

/-- **Connected G(ω) for n=2 ↔ incompatibility of the pair** (§18.4
sharpening): for `ω : Fin 2 → polymers`, the index-side incompatibility
graph `polymerSeqIncompatibilityGraph ω` is `Connected` iff
`PolymersIncompatible (ω 0) (ω 1)`. Provides an explicit
characterisation linking the filter-connected form (PR #1521) to the
existing pair Ursell formula (Step 585). -/
theorem polymerSeqIncompatibilityGraph_two_connected_iff_incompatible
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ω : Fin 2 → Finset (Sym2 ι)) :
    (polymerSeqIncompatibilityGraph ω).Connected ↔
      PolymersIncompatible (ω 0) (ω 1) := by
  refine ⟨?_, ?_⟩
  · -- Forward: Connected ⇒ Adj 0 1 ⇒ incompatibility (use contrapositive).
    intro h_conn
    by_contra h_compat
    -- If not incompatible, graph has no edges; 0 and 1 not reachable.
    have h_no_adj : ∀ a b : Fin 2,
        ¬ (polymerSeqIncompatibilityGraph ω).Adj a b := by
      intro a b hab
      rw [polymerSeqIncompatibilityGraph_adj] at hab
      obtain ⟨hne, hincompat⟩ := hab
      -- a, b ∈ Fin 2 and a ≠ b. So {a, b} = {0, 1}.
      fin_cases a <;> fin_cases b <;>
        first
          | exact hne rfl
          | exact h_compat hincompat
          | exact h_compat hincompat.symm
    obtain ⟨w⟩ := h_conn.preconnected 0 1
    cases w with
    | cons hadj _ =>
      exact h_no_adj _ _ hadj
  · intro h_incompat
    refine { preconnected := ?_, nonempty := ⟨0⟩ }
    intro u v
    have h_adj : (polymerSeqIncompatibilityGraph ω).Adj 0 1 := by
      rw [polymerSeqIncompatibilityGraph_adj]
      exact ⟨by decide, h_incompat⟩
    have h_reach_0 : ∀ w : Fin 2,
        (polymerSeqIncompatibilityGraph ω).Reachable w 0 := by
      intro w
      fin_cases w
      · exact SimpleGraph.Reachable.refl 0
      · exact ⟨SimpleGraph.Walk.cons h_adj.symm SimpleGraph.Walk.nil⟩
    exact (h_reach_0 u).trans (h_reach_0 v).symm


end IsingModel
