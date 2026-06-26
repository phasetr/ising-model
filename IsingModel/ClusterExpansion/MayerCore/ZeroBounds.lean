import IsingModel.ClusterExpansion.MayerCore.Terms
import IsingModel.RealTanhAux

/-!
# Cluster Expansion Mayer Core Zero and Bounds

Mechanical child split from `ClusterExpansion/MayerCore.lean`.
-/

namespace IsingModel

open Finset

/-- **Mayer expansion `n = 2` term as filter sum** (Step 597): the
ordered-pair sum from Step 593 reduces to a sum over the incompatible
pairs only,
`mayerExpansionTerm G 2 t = (-1/2) · ∑_{(P, Q) ∈ allPolymers² with
PolymersIncompatible P Q} t^|P| · t^|Q|`.
The if-then-else summand vanishes on compatible pairs, so the sum
restricts to the filter `(allPolymers G ×ˢ allPolymers G).filter
(fun pq => PolymersIncompatible pq.1 pq.2)`. -/
theorem mayerExpansionTerm_two_filter
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerExpansionTerm G 2 t =
      (-1/2 : ℝ) *
        ∑ pq ∈ ((allPolymers G) ×ˢ (allPolymers G)).filter
            (fun pq => PolymersIncompatible pq.1 pq.2),
          (t ^ pq.1.card * t ^ pq.2.card) := by
  rw [mayerExpansionTerm_two]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]

/-- **Mayer expansion term vanishes at `t = 0`** (Step 598):
`mayerExpansionTerm G n 0 = 0` for every `n : ℕ`. For `n = 0`,
`ursellCoefficient` already vanishes (Step 587). For `n ≥ 1`, every
polymer `ω i` has `|ω i| ≥ 1`, so `0 ^ |ω i| = 0` and the product
`clusterSeqActivity 0 ω = ∏ i, 0 ^ |ω i|` contains a zero factor. -/
theorem mayerExpansionTerm_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) :
    mayerExpansionTerm G n 0 = 0 := by
  match n with
  | 0 => exact mayerExpansionTerm_zero G 0
  | k + 1 =>
    unfold mayerExpansionTerm
    refine Finset.sum_eq_zero (fun ω hω => ?_)
    rw [Fintype.mem_piFinset] at hω
    have h_polymer : IsPolymer G (ω 0) := mem_allPolymers.mp (hω 0)
    have h_pos : 0 < (ω 0).card := h_polymer.nonempty.card_pos
    have h_zero : (0 : ℝ) ^ (ω 0).card = 0 := zero_pow h_pos.ne'
    have h_prod : clusterSeqActivity (0 : ℝ) ω = 0 := by
      unfold clusterSeqActivity
      exact Finset.prod_eq_zero (Finset.mem_univ 0) h_zero
    rw [h_prod, mul_zero]

/-- **Mayer partial sum vanishes at `t = 0`** (Step 598): consequence
of `mayerExpansionTerm_at_zero` summed over `Finset.range (N + 1)`. -/
theorem mayerPartialSum_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    mayerPartialSum G N 0 = 0 := by
  unfold mayerPartialSum
  refine Finset.sum_eq_zero (fun n _ => ?_)
  exact mayerExpansionTerm_at_zero G n

/-- **Polymer-family sum at `t = 0`** (Step 599):
`∑_{Γ ∈ vdCompatiblePolymerFamilies G} ∏_{P ∈ Γ} 0^|P| = 1`. Only the
empty family `Γ = ∅` contributes (its empty product equals `1`); any
non-empty `Γ` contains a polymer with `|P| ≥ 1`, so `0^|P| = 0` and
the product vanishes. -/
theorem vdPolymerFamilies_sum_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 := by
  classical
  have h_empty_in :
      (∅ : Finset (Finset (Sym2 ι))) ∈ vdCompatiblePolymerFamilies G := by
    rw [mem_vdCompatiblePolymerFamilies]
    exact ⟨Finset.empty_subset _, IsCompatiblePolymerFamilyVertexDisjoint.empty G⟩
  have h_nonempty_zero : ∀ Γ ∈ vdCompatiblePolymerFamilies G,
      Γ ≠ ∅ → (∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 := by
    intro Γ hΓ hne
    rw [mem_vdCompatiblePolymerFamilies] at hΓ
    obtain ⟨P, hP⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hP_polymer : IsPolymer G P := mem_allPolymers.mp (hΓ.1 hP)
    have hP_pos : 0 < P.card := hP_polymer.nonempty.card_pos
    exact Finset.prod_eq_zero hP (zero_pow hP_pos.ne')
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.prod_empty]
  · intro Γ hΓ hne
    exact h_nonempty_zero Γ hΓ hne
  · intro h
    exact absurd h_empty_in h

/-- **`connectedSpanningEdgeSubsets` cardinality bound** (Step 602):
the connected-spanning edge subsets are a filter of the powerset of
`G.edgeFinset`, hence their count is at most `2^|G.edgeFinset|`. -/
theorem connectedSpanningEdgeSubsets_card_le_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (connectedSpanningEdgeSubsets G).card ≤ 2 ^ G.edgeFinset.card := by
  classical
  unfold connectedSpanningEdgeSubsets
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_powerset]

/-- **Ursell coefficient absolute bound** (Step 601): the triangle
inequality on the alternating-sign sum gives
`|ϕ^T(ω)| ≤ |connectedSpanningEdgeSubsets G(ω)| / n!`. Since each
summand `(-1)^|S|` has absolute value `1`, summing `|·|` gives the
cardinality of the index set. Useful for convergence estimates of the
Mayer expansion. -/
theorem ursellCoefficient_abs_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    |ursellCoefficient ω| ≤
      ((connectedSpanningEdgeSubsets (polymerSeqIncompatibilityGraph ω)).card : ℝ)
        / n.factorial := by
  unfold ursellCoefficient
  rw [abs_div]
  have h_fact_abs : |((n.factorial : ℝ))| = n.factorial :=
    abs_of_nonneg (Nat.cast_nonneg _)
  rw [h_fact_abs]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h_each : ∀ S ∈ connectedSpanningEdgeSubsets (polymerSeqIncompatibilityGraph ω),
      |((-1 : ℝ) ^ S.card)| = 1 := by
    intro S _
    rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Nat.smul_one_eq_cast]

/-- **Uniform Ursell coefficient bound** (Step 603): combining Step
601 (|ϕ^T| ≤ card / n!) and Step 602 (card ≤ 2^|E|) gives
`|ϕ^T(ω)| ≤ 2^|E(G(ω))| / n!`. The classical Mayer-expansion uniform
bound from connected-spanning subgraphs of the incompatibility graph. -/
theorem ursellCoefficient_abs_le_pow_div_factorial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    |ursellCoefficient ω| ≤
      (2 ^ (polymerSeqIncompatibilityGraph ω).edgeFinset.card : ℝ)
        / (n.factorial : ℝ) := by
  refine (ursellCoefficient_abs_le ω).trans ?_
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast connectedSpanningEdgeSubsets_card_le_pow _

/-- **Polymer-family sum ≥ 1 under `t ≥ 0`** (Step 605): for any
non-negative activity parameter `t`, the empty family `Γ = ∅`
contributes `1` and all other families contribute non-negative
products `∏ P ∈ Γ, t^|P| ≥ 0`. Hence the total is at least `1`.
This generalises `one_le_vdPolymerFamilies_sum` (Step 549) from the
tanh form to a generic non-negative activity. -/
theorem vdPolymerFamilies_sum_ge_one_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card := by
  classical
  have h_empty_in :
      (∅ : Finset (Finset (Sym2 ι))) ∈ vdCompatiblePolymerFamilies G := by
    rw [mem_vdCompatiblePolymerFamilies]
    exact ⟨Finset.empty_subset _, IsCompatiblePolymerFamilyVertexDisjoint.empty G⟩
  have h_nonneg : ∀ Γ ∈ vdCompatiblePolymerFamilies G,
      0 ≤ ∏ P ∈ Γ, t ^ P.card :=
    fun _ _ => Finset.prod_nonneg (fun _ _ => pow_nonneg ht _)
  have h_empty_eq : (1 : ℝ) =
      ∏ P ∈ (∅ : Finset (Finset (Sym2 ι))), t ^ P.card := (Finset.prod_empty).symm
  rw [h_empty_eq]
  exact Finset.single_le_sum h_nonneg h_empty_in

/-- **Polymer-family sum ≤ `(1+t)^|E|` under `t ≥ 0`** (Step 629):
generic upper bound generalising Step 552's tanh-form bound. Proof:
`evenSubgraphs G ⊆ G.edgeFinset.powerset`, so the sum over even
subgraphs of `t^|X|` is at most the sum over all subsets, which equals
`(1+t)^|E|` by binomial expansion (`Finset.prod_one_add`). -/
theorem vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ G.edgeFinset.card := by
  classical
  rw [← evenSubgraphs_sum_eq_vdPolymerFamilies_sum G t,
      evenSubgraphs_eq_inline_filter]
  have hpower :
      (1 + t) ^ G.edgeFinset.card =
        ∑ X ∈ G.edgeFinset.powerset, t ^ X.card := by
    rw [← Finset.prod_const, Finset.prod_one_add]
    refine Finset.sum_congr rfl (fun X _ => ?_)
    rw [Finset.prod_const]
  rw [hpower]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro X _ _
  exact pow_nonneg ht _

/-- **Polymer-family sum > 0 under `t ≥ 0`** (Step 605):
strict positivity follows from `≥ 1` and `0 < 1`. Useful to ensure
`Real.log (vdPolymerFamilies_sum G t)` is well-defined. -/
theorem vdPolymerFamilies_sum_pos_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card :=
  lt_of_lt_of_le zero_lt_one (vdPolymerFamilies_sum_ge_one_of_nonneg G ht)

/-- **`log (vdPolymerFamilies_sum)` is real-analytic at any `t ≥ 0`**
(Step 606): `AnalyticAt ℝ (Real.log ∘ vdPolymerFamilies_sum G) t` via
`AnalyticAt.log` (Step 561) plus positivity (Step 605). Sets up the
LHS of the Mayer expansion identity as a real-analytic function on
the non-negative axis. -/
theorem log_vdPolymerFamilies_sum_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ
      (fun s : ℝ => Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
                                 ∏ P ∈ Γ, s ^ P.card)) t :=
  (vdPolymerFamilies_sum_analyticAt G t).log
    (vdPolymerFamilies_sum_pos_of_nonneg G ht)

/-- **`log (vdPolymerFamilies_sum)` AnalyticOnNhd over `[0, ∞)`**
(Step 607): global form of Step 606 — at every `t ∈ Set.Ici 0`, the
function is `AnalyticAt`, hence `AnalyticOnNhd ℝ _ (Set.Ici 0)`. -/
theorem log_vdPolymerFamilies_sum_analyticOnNhd_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    AnalyticOnNhd ℝ
      (fun s : ℝ => Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
                                 ∏ P ∈ Γ, s ^ P.card)) (Set.Ici 0) :=
  fun _ ht => log_vdPolymerFamilies_sum_analyticAt G ht

/-- **`Real.tanh` is strictly monotone** (shared §18.4 helper): `tanh` is
strictly increasing on `ℝ`. Proved from `tanh = sinh / cosh` (`cosh > 0`) and
`sinh (y - x) > 0` for `x < y`. Mathlib does not yet export
`Real.tanh_strictMono`, so this single project-local copy is reused across the
`ClusterExpansion` tanh-monotonicity lemmas. -/
theorem real_tanh_strictMono : StrictMono Real.tanh := by
  intro x y hxy
  have hx_pos : 0 < Real.cosh x := Real.cosh_pos x
  have hy_pos : 0 < Real.cosh y := Real.cosh_pos y
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
      div_lt_div_iff₀ hx_pos hy_pos]
  have h_sub : Real.sinh y * Real.cosh x - Real.sinh x * Real.cosh y =
      Real.sinh (y - x) := by rw [Real.sinh_sub]; ring
  have h_sinh_pos : 0 < Real.sinh (y - x) := by
    rw [show (0 : ℝ) = Real.sinh 0 from Real.sinh_zero.symm]
    exact Real.sinh_strictMono (sub_pos.mpr hxy)
  linarith

/-- **`log (vdPolymerFamilies_sum tanh(β·J))` analyticAt in `β`**
(Step 608): under `0 ≤ β·J`, the function
`β' ↦ Real.log (∑_Γ ∏_{P ∈ Γ} tanh(β'·J)^|P|)` is `AnalyticAt ℝ` at `β`.
Combines Step 562 (vdSum analytic in β via tanh chain) with positivity
of vdSum at `tanh(β·J) ≥ 0` (Steps 605 + helper). -/
theorem log_vdPolymerFamilies_sum_tanh_analyticAt_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ
      (fun β' : ℝ => Real.log
        (∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card)) β := by
  refine (vdPolymerFamilies_sum_tanh_analyticAt_beta G J β).log ?_
  exact vdPolymerFamilies_sum_pos_of_nonneg G (real_tanh_nonneg hβJ)

/-- **`log (vdPolymerFamilies_sum tanh(β·J))` analyticAt in `J`**
(Step 608): dual of `_beta`. -/
theorem log_vdPolymerFamilies_sum_tanh_analyticAt_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ
      (fun J' : ℝ => Real.log
        (∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card)) J := by
  refine (vdPolymerFamilies_sum_tanh_analyticAt_J G β J).log ?_
  exact vdPolymerFamilies_sum_pos_of_nonneg G (real_tanh_nonneg hβJ)

/-- **Mayer expansion term absolute bound** (Step 604): the triangle
inequality applied to the Mayer term gives
`|mayerExpansionTerm G n t| ≤ ∑_ω |ϕ^T(ω)| · |z(t, ω)|`. -/
theorem mayerExpansionTerm_abs_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (t : ℝ) :
    |mayerExpansionTerm G n t| ≤
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
        |ursellCoefficient ω| * |clusterSeqActivity t ω| := by
  unfold mayerExpansionTerm
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun ω _ => abs_mul _ _)

/-- **Uniform Ursell bound** (Step 615): independent-of-ω bound
`|ϕ^T(ω)| ≤ 2^(n choose 2) / n!`. Combines Step 603 (`2^|E(G(ω))| / n!`)
with Mathlib's `SimpleGraph.card_edgeFinset_le_card_choose_two`
(graph on `Fin n` has at most `n.choose 2` edges). -/
theorem ursellCoefficient_abs_le_choose_pow_div_factorial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    |ursellCoefficient ω| ≤ (2 ^ (n.choose 2) : ℝ) / (n.factorial : ℝ) := by
  refine (ursellCoefficient_abs_le_pow_div_factorial ω).trans ?_
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
  have h := SimpleGraph.card_edgeFinset_le_card_choose_two
              (G := polymerSeqIncompatibilityGraph ω)
  rw [show Fintype.card (Fin n) = n from Fintype.card_fin n] at h
  exact h

/-- **Mayer identity at `t = 0`** (Step 600, milestone): the first
verified instance of the Mayer expansion identity
`log Ξ = ∑_{n ≥ 0} mayerExpansionTerm G n t`. At `t = 0`,
both sides equal `0`:
- `log (vdPolymerFamilies_sum G 0) = log 1 = 0` via Step 599
- `mayerPartialSum G N 0 = 0` via Step 598

This is a trivial special case symbolically marking the structural
target. The general identity for non-zero `t` requires substantial
combinatorial work (Mayer/Ursell algebraic manipulations of formal
power series); it remains deferred. -/
theorem mayer_identity_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
              ∏ P ∈ Γ, (0 : ℝ) ^ P.card) =
      mayerPartialSum G N 0 := by
  rw [vdPolymerFamilies_sum_at_zero, Real.log_one, mayerPartialSum_at_zero]

/-- **Mayer identity at `β·J = 0`** (Step 609): trivial extension of
Step 600 to the β/J directions. When `β·J = 0`, `tanh(β·J) = 0`,
reducing both sides to the t=0 case. -/
theorem mayer_identity_at_betaJ_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
              ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) =
      mayerPartialSum G N (Real.tanh (β * J)) := by
  rw [hβJ, Real.tanh_zero]
  exact mayer_identity_at_zero G N

/-- **Mayer identity at `β = 0`** (Step 609 specialisation). -/
theorem mayer_identity_at_beta_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
              ∏ P ∈ Γ, Real.tanh ((0 : ℝ) * J) ^ P.card) =
      mayerPartialSum G N (Real.tanh ((0 : ℝ) * J)) :=
  mayer_identity_at_betaJ_zero G (zero_mul J) N

/-- **Mayer identity at `J = 0`** (Step 609 specialisation). -/
theorem mayer_identity_at_J_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
              ∏ P ∈ Γ, Real.tanh (β * (0 : ℝ)) ^ P.card) =
      mayerPartialSum G N (Real.tanh (β * (0 : ℝ))) :=
  mayer_identity_at_betaJ_zero G (mul_zero β) N


end IsingModel
