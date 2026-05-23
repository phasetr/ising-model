import IsingModel.ClusterExpansion.Families.PolymerPartition

/-!
# Cluster polymer families split — partition expansion and vd-polymer sandwich bounds

Part of the split cluster-expansion families layer (Issue #1850).
-/

namespace IsingModel

open Finset

/-- **FV (3.45) closed form via `evenSubgraphs G`**: under no further
hypotheses, the FV (3.45) closed form may be rewritten as
`Z(J,0,β) = 2^|ι| · cosh(β·J)^|E| · ∑ X ∈ evenSubgraphs G, tanh(β·J)^|X|`.

Direct corollary of `partitionFunction_high_temp_expansion_h_zero_closed`
(Step 283) plus `evenSubgraphs_eq_inline_filter` (Step 516). -/
theorem partitionFunction_high_temp_expansion_h_zero_closed_evenSubgraphs
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    partitionFunction G ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
      ∑ X ∈ evenSubgraphs G, Real.tanh (β * J) ^ X.card := by
  rw [partitionFunction_high_temp_expansion_h_zero_closed G J β,
      evenSubgraphs_eq_inline_filter]

/-- **Z FV (3.45) polymer-family form**: under no further hypotheses,
`Z(J,0,β) = 2^|ι| · cosh(β·J)^|E| · ∑_{Γ ∈ vdCompatiblePolymerFamilies G,
∏_{P ∈ Γ} tanh(β·J)^|P|}`.

Combines Step 517 (FV (3.45) via `evenSubgraphs G`) with Step 547
(`evenSubgraphs_sum_eq_vdPolymerFamilies_sum`). -/
theorem partitionFunction_high_temp_expansion_h_zero_polymer_family
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    partitionFunction G ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card := by
  rw [partitionFunction_high_temp_expansion_h_zero_closed_evenSubgraphs G J β,
      evenSubgraphs_sum_eq_vdPolymerFamilies_sum G (Real.tanh (β * J))]

/-- **Sum of polymer cardinalities is bounded by `|E|`**: in a
vertex-disjoint compatible polymer family, the total edge count is at
most `G.edgeFinset.card` since the biUnion is a subset of the edge set. -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.sum_card_le_edgeFinset_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Γ : Finset (Finset (Sym2 ι))}
    (hΓ : IsCompatiblePolymerFamilyVertexDisjoint G Γ) :
    ∑ P ∈ Γ, P.card ≤ G.edgeFinset.card := by
  rw [← hΓ.card_biUnion]
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_biUnion] at he
  obtain ⟨P, hP, heP⟩ := he
  exact (hΓ.1 P hP).isEven.subset heP

/-- **VD polymer-family sum ≤ 2^|E|**: under `0 ≤ β·J`,
`∑_{Γ ∈ vdCompatiblePolymerFamilies G} ∏ tanh(β·J)^|P| ≤ 2^|E|`.

Direct via the bijection (Step 547) plus the existing even-subgraph
upper bound `sum_pow_tanh_even_subgraph_le_two_pow` (Step 319). -/
theorem vdPolymerFamilies_sum_le_two_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ G.edgeFinset.card := by
  rw [← evenSubgraphs_sum_eq_vdPolymerFamilies_sum G (Real.tanh (β * J))]
  rw [evenSubgraphs_eq_inline_filter]
  exact sum_pow_tanh_even_subgraph_le_two_pow G J β hβJ

/-- **VD polymer-family sum ≥ 1**: under `0 ≤ β·J`,
`1 ≤ ∑_{Γ ∈ vdCompatiblePolymerFamilies G} ∏ tanh(β·J)^|P|`.

Direct via the bijection (Step 547) plus `one_le_sum_pow_tanh_even_subgraph`
(Step 318). The empty family contributes 1; non-empty families add
non-negative weights. -/
theorem one_le_vdPolymerFamilies_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card := by
  rw [← evenSubgraphs_sum_eq_vdPolymerFamilies_sum G (Real.tanh (β * J))]
  rw [evenSubgraphs_eq_inline_filter]
  exact one_le_sum_pow_tanh_even_subgraph G J β hβJ

/-- **Sharper VD polymer-family sum upper bound**: under `0 ≤ β·J`,
`∑_Γ ∏ tanh(β·J)^|P| ≤ (1 + tanh(β·J))^|E|`. Tightens Step 551
(2^|E|) using Step 392 \`sum_pow_tanh_even_subgraph_le_one_plus_tanh_pow\`. -/
theorem vdPolymerFamilies_sum_le_one_plus_tanh_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^ G.edgeFinset.card := by
  rw [← evenSubgraphs_sum_eq_vdPolymerFamilies_sum G (Real.tanh (β * J))]
  rw [evenSubgraphs_eq_inline_filter]
  exact sum_pow_tanh_even_subgraph_le_one_plus_tanh_pow G J β hβJ

/-- **Sharper VD polymer-family sum sandwich**: under `0 ≤ β·J`,
`1 ≤ ∑_Γ ∏ tanh(β·J)^|P| ≤ (1 + tanh(β·J))^|E|`. Bundles Steps 550
and 553. -/
theorem vdPolymerFamilies_sum_sandwich_sharp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^ G.edgeFinset.card :=
  ⟨one_le_vdPolymerFamilies_sum G hβJ,
   vdPolymerFamilies_sum_le_one_plus_tanh_pow G hβJ⟩

/-- **VD polymer-family sum sandwich**: under `0 ≤ β·J`,
`1 ≤ ∑_Γ ∏ tanh(β·J)^|P| ≤ 2^|E|`. Bundles Steps 550 and 551. -/
theorem vdPolymerFamilies_sum_sandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ G.edgeFinset.card :=
  ⟨one_le_vdPolymerFamilies_sum G hβJ,
   vdPolymerFamilies_sum_le_two_pow G hβJ⟩

/-- **VD polymer-family sum sandwich (ferromagnetic)**: under
`0 ≤ J, 0 < β`, the same `1 ≤ ∑_Γ ∏ tanh(β·J)^|P| ≤ 2^|E|`. -/
theorem vdPolymerFamilies_sum_sandwich_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    1 ≤ (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ G.edgeFinset.card :=
  vdPolymerFamilies_sum_sandwich G (mul_nonneg hβ.le hJ)

/-- **VD polymer-family sum sharp sandwich (ferromagnetic)**: under
`0 ≤ J, 0 < β`, the same `1 ≤ ∑_Γ ∏ tanh(β·J)^|P| ≤
(1+tanh(β·J))^|E|`. -/
theorem vdPolymerFamilies_sum_sandwich_sharp_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    1 ≤ (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^ G.edgeFinset.card :=
  vdPolymerFamilies_sum_sandwich_sharp G (mul_nonneg hβ.le hJ)

/-- **Polymer activity for the lattice Ising model**: the natural
weight `t^|P|` arising from the FV (3.45) closed form
`Z = 2^|ι|·cosh^|E|·∑_{X ⊆ E, even} tanh(β·J)^|X|`.

Set `t = tanh(β·J)` to recover the FV (3.45) summand. -/
def polymerActivity (t : ℝ) (P : Finset (Sym2 ι)) : ℝ := t ^ P.card


end IsingModel
