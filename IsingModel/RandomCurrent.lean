import IsingModel.RandomCurrent.Core
import IsingModel.RandomCurrent.BoundedExpansion
import IsingModel.RandomCurrent.Switching
import IsingModel.AmbientLattice
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Random current foundation (GJ §5.1 Simon-Lieb attempt, step 1)

A current on a finite induced subgraph is an `ℕ`-valued function
on its (finite) edge set. This file fixes the type and the basic
algebraic operations (`Zero`, `Add`); subsequent PRs will add the
parity, the source/sink characterisation, and ultimately the
Aizenman switching lemma feeding the random-current expression of
`⟨σ^A⟩^Λ` and Simon-Lieb (FV Prop 9.31).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 76–79;
Friedli–Velenik §3.7, Prop 9.31. -/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Source set has even cardinality**: `|(∂n)|` is always even.
Derived from `sum_parity_eq_zero` by casting the filter-card formula
through `ZMod 2`: `|sources| ≡ ∑_v parity v = 0 (mod 2)`.
This is the switching-lemma prerequisite; Aizenman's argument reduces
to the 2-source case `∂n = {i, j}`, which requires `|∂n|` even. -/
theorem Current.sources_card_even
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    Even (n.sources G Λ).card := by
  have h : ((n.sources G Λ).card : ZMod 2) = 0 := by
    calc ((n.sources G Λ).card : ZMod 2)
        = ∑ v : ↑Λ, n.parity G Λ v := by
          rw [Current.sources, Finset.card_filter, Nat.cast_sum]
          apply Finset.sum_congr rfl
          intro v _
          exact Current.cast_indicator_parity G Λ n v
      _ = 0 := Current.sum_parity_eq_zero G Λ n
  exact ZMod.natCast_eq_zero_iff_even.mp h

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`Current.Adj` is decidable**: a noncomputable `DecidableRel`
instance for `n.Adj G Λ` via `Classical.propDecidable`. Since
`n.support` is noncomputable, the instance is classical rather than
constructive; it is still logically valid and unlocks mathlib's finite
`SimpleGraph` API — `neighborFinset`, `degree`, `edgeFinset`, and the
`Reachable` decision procedure — for `Current.toSimpleGraph`. -/
noncomputable instance Current.instDecidableAdj
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) : DecidableRel (n.Adj G Λ) := fun u v => by
  unfold Current.Adj
  exact Classical.propDecidable _

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Source vertices lie in `toSimpleGraph.support`**: if
`v ∈ n.sources G Λ`, then `v ∈ (n.toSimpleGraph G Λ).support`, i.e.
`v` has at least one neighbour in `n.toSimpleGraph`.
`SimpleGraph.support G = {v | ∃ w, G.Adj v w}` requires no `Fintype`
or `DecidableRel`. This follows from `exists_adj_of_mem_sources`
(step 94) plus `toSimpleGraph_adj_iff`. -/
theorem Current.mem_toSimpleGraph_support_of_mem_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {v : ↑Λ} (hv : v ∈ n.sources G Λ) :
    v ∈ (n.toSimpleGraph G Λ).support := by
  rw [SimpleGraph.mem_support]
  obtain ⟨u, hu⟩ := Current.exists_adj_of_mem_sources G Λ n hv
  exact ⟨u, (Current.toSimpleGraph_adj_iff G Λ n v u).mpr (Current.Adj_symm G Λ n hu)⟩

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Local ZMod 2 handshake for closed Finsets**: for any `R : Finset ↑Λ`
that is closed under active-edge adjacency (v ∈ R and e ∈ n.support with
v ∈ e forces the other endpoint w into R), the sum of parities over R
is zero in `ZMod 2`. Each active edge contributes `|R ∩ e| ∈ {0, 2}`
to the ℕ-valued sum, making it even. The reachable set from any vertex
is the canonical closed Finset; applied there, this gives the switching
lemma prerequisite. -/
theorem Current.sum_parity_closed_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {R : Finset ↑Λ}
    (hclosed : ∀ v ∈ R, ∀ w : ↑Λ, n.Adj G Λ v w → w ∈ R) :
    ∑ v ∈ R, n.parity G Λ v = 0 := by
  classical
  simp only [Current.parity_eq_degreeAt, ← Nat.cast_sum]
  rw [ZMod.natCast_eq_zero_iff_even, even_iff_two_dvd]
  unfold Current.degreeAt
  rw [Finset.sum_comm]
  apply Finset.dvd_sum
  intro e _
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  rcases eq_or_ne (n e) 0 with he0 | he0
  · simp [he0]
  · have hesupp : e ∈ n.support G Λ := (Current.mem_support_iff G Λ n e).mpr he0
    have hle2 : (R.filter (fun v => v ∈ (e : Sym2 ↑Λ))).card ≤ 2 := by
      apply (Finset.card_le_card _).trans
          (Current.edgeSet_toFinset_card_eq_two G Λ e).le
      intro v hv; exact Sym2.mem_toFinset.mpr (Finset.mem_filter.mp hv).2
    have hne1 : (R.filter (fun v => v ∈ (e : Sym2 ↑Λ))).card ≠ 1 := by
      intro h1
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
      have hafilter : a ∈ R.filter (fun v => v ∈ (e : Sym2 ↑Λ)) :=
        ha ▸ Finset.mem_singleton_self a
      obtain ⟨haR, hae⟩ := Finset.mem_filter.mp hafilter
      set b := Sym2.Mem.other hae
      have hbmem : b ∈ (e : Sym2 ↑Λ) := Sym2.other_mem hae
      have hab : b ≠ a :=
        Sym2.other_ne (SimpleGraph.not_isDiag_of_mem_edgeSet _ e.2) hae
      have hadj : n.Adj G Λ a b := ⟨hab.symm, e, hesupp, hae, hbmem⟩
      have hbR : b ∈ R := hclosed a haR b hadj
      exact hab (Finset.mem_singleton.mp
        (ha ▸ Finset.mem_filter.mpr ⟨hbR, hbmem⟩))
    rcases Nat.eq_zero_or_pos (R.filter (fun v => v ∈ (e : Sym2 ↑Λ))).card with h | h
    · rw [h, zero_mul]; exact dvd_zero 2
    · rw [show (R.filter (fun v => v ∈ (e : Sym2 ↑Λ))).card = 2 from by omega]
      exact dvd_mul_right 2 _

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **2-source currents have connected sources**: if
`n.sources G Λ = {i, j}` with `i ≠ j`, then
`(n.toSimpleGraph G Λ).Reachable i j`. Proof: the reachable set R
from i is closed under active-edge adjacency; by `sum_parity_closed_eq_zero`,
`|sources ∩ R|` is even; since `i ∈ sources ∩ R`, `|sources ∩ R| ≥ 2`,
forcing `j ∈ R`. This is the key switching-lemma prerequisite for
Aizenman's 2-source reduction and the Simon-Lieb inequality. -/
theorem Current.sources_reachable_of_sources_eq_pair
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {i j : ↑Λ} (hne : i ≠ j)
    (h : n.sources G Λ = {i, j}) :
    (n.toSimpleGraph G Λ).Reachable i j := by
  classical
  -- R = reachable set from i (classical Finset)
  let R : Finset ↑Λ := Finset.univ.filter (fun v => (n.toSimpleGraph G Λ).Reachable i v)
  -- R is closed under active-edge adjacency
  have hclosed : ∀ v ∈ R, ∀ w : ↑Λ, n.Adj G Λ v w → w ∈ R := by
    intro v hv w hadj
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.trans ((Current.toSimpleGraph_adj_iff G Λ n v w).mpr hadj).reachable
  -- Local handshake: (sources ∩ R).card ≡ 0 (mod 2)
  have heven : ((n.sources G Λ ∩ R).card : ZMod 2) = 0 := by
    have hsum := Current.sum_parity_closed_eq_zero G Λ n hclosed
    have hinter : n.sources G Λ ∩ R = R.filter (· ∈ n.sources G Λ) := by
      ext v; simp [Finset.mem_inter, Finset.mem_filter, and_comm]
    calc ((n.sources G Λ ∩ R).card : ZMod 2)
        = ∑ v ∈ R, n.parity G Λ v := by
          rw [hinter, Finset.card_filter, Nat.cast_sum]
          apply Finset.sum_congr rfl
          intro v _
          have : (if v ∈ n.sources G Λ then (1 : ℕ) else 0) =
                 if n.parity G Λ v ≠ 0 then 1 else 0 := by simp [Current.mem_sources_iff]
          rw [this]; exact Current.cast_indicator_parity G Λ n v
      _ = 0 := hsum
  -- i ∈ sources ∩ R
  have hi : i ∈ n.sources G Λ ∩ R := by
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · exact h ▸ Finset.mem_insert_self i {j}
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.rfl⟩
  -- |sources ∩ R| ≥ 2
  have hge2 : 2 ≤ (n.sources G Λ ∩ R).card := by
    obtain ⟨k, hk⟩ := ZMod.natCast_eq_zero_iff_even.mp heven
    have hpos : 0 < (n.sources G Λ ∩ R).card := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  -- sources ∩ R = {i, j}
  have hboth : n.sources G Λ ∩ R = {i, j} :=
    Finset.eq_of_subset_of_card_le
      (fun v hv => by have hvsrc := (Finset.mem_inter.mp hv).1; rwa [h] at hvsrc)
      (by rw [Finset.card_pair hne]; exact hge2)
  -- j ∈ R → Reachable i j
  have hjSR : j ∈ n.sources G Λ ∩ R := by rw [hboth]; simp
  exact (Finset.mem_filter.mp (Finset.mem_inter.mp hjSR).2).2

omit [DecidableEq V] in
/-- **Weight peeling identity**: subtracting one unit from active edge `e₀`
factors the weight by `β * J / n e₀`. Key identity: `(β*J)^k / k! = β*J/k *
(β*J)^(k-1) / (k-1)!` applied at `k = n e₀` via `k! = k * (k-1)!`.
Foundational algebraic step for the Simon-Lieb inequality (GJ §5.1). -/
theorem Current.weight_pred_edge
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (n : Current G Λ) (e₀ : (inducedGraph G Λ).edgeSet)
    (he : 0 < n e₀) :
    n.weight G Λ β J =
      β * J / (n e₀ : ℝ) *
        (n - Current.fromEdgeFinset G Λ {e₀}).weight G Λ β J := by
  unfold Current.weight
  have hsub_e₀ : (n - Current.fromEdgeFinset G Λ {e₀}) e₀ = n e₀ - 1 := by
    simp [Current.fromEdgeFinset]
  have hsub_ne : ∀ e : (inducedGraph G Λ).edgeSet, e ≠ e₀ →
      (n - Current.fromEdgeFinset G Λ {e₀}) e = n e := by
    intro e he_ne
    simp [Current.fromEdgeFinset, Finset.mem_singleton, he_ne]
  -- Key single-edge identity: (β*J)^k / k! = β*J/k * (β*J)^(k-1) / (k-1)!
  have hkey : (β * J) ^ n e₀ / ((n e₀).factorial : ℝ) =
      β * J / (n e₀ : ℝ) * ((β * J) ^ (n e₀ - 1) / ((n e₀ - 1).factorial : ℝ)) := by
    have hpos : (n e₀ : ℝ) > 0 := Nat.cast_pos.mpr he
    rw [← Nat.succ_pred_eq_of_pos he, pow_succ, Nat.factorial_succ]
    push_cast
    field_simp
  -- Split product at e₀
  have hlhs : ∏ e : (inducedGraph G Λ).edgeSet, (β * J) ^ n e / ((n e).factorial : ℝ) =
      (β * J) ^ n e₀ / ((n e₀).factorial : ℝ) *
      ∏ e ∈ Finset.univ.erase e₀, (β * J) ^ n e / ((n e).factorial : ℝ) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ e₀)).symm
  have hrhs : ∏ e : (inducedGraph G Λ).edgeSet,
      (β * J) ^ (n - Current.fromEdgeFinset G Λ {e₀}) e /
      (((n - Current.fromEdgeFinset G Λ {e₀}) e).factorial : ℝ) =
      (β * J) ^ (n e₀ - 1) / ((n e₀ - 1).factorial : ℝ) *
      ∏ e ∈ Finset.univ.erase e₀, (β * J) ^ n e / ((n e).factorial : ℝ) := by
    rw [(Finset.mul_prod_erase _ _ (Finset.mem_univ e₀)).symm, hsub_e₀]
    congr 1
    apply Finset.prod_congr rfl
    intro e he_mem
    rw [Finset.mem_erase] at he_mem
    rw [hsub_ne e he_mem.1]
  rw [hlhs, hrhs, hkey]
  ring

omit [DecidableEq V] in
/-- **Weight peeling bound**: for `0 ≤ β * J` and `0 < n e₀`, the weight
satisfies `n.weight β J ≤ β * J * (n - fromEdgeFinset {e₀}).weight β J`.
Since `n e₀ ≥ 1`, we have `β*J / n e₀ ≤ β*J`. Used in the edge-peeling
argument for Simon-Lieb (GJ §5.1 / FV Prop 9.31). -/
theorem Current.weight_le_mul_pred_edge
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : Current G Λ)
    (e₀ : (inducedGraph G Λ).edgeSet) (he : 0 < n e₀) :
    n.weight G Λ β J ≤
      β * J * (n - Current.fromEdgeFinset G Λ {e₀}).weight G Λ β J := by
  rw [Current.weight_pred_edge G Λ β J n e₀ he]
  have hpos : (n e₀ : ℝ) > 0 := Nat.cast_pos.mpr he
  have hle : β * J / (n e₀ : ℝ) ≤ β * J :=
    div_le_self hβJ (by exact_mod_cast he)
  exact mul_le_mul_of_nonneg_right hle (Current.weight_nonneg G Λ hβJ _)

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Bridge lemma — sources after edge subtraction**: subtracting
`fromEdgeFinset {e₀}` from a current `n` with `0 < n e₀` transforms
sources by symmetric difference with the two endpoints of `e₀`:
`(n - 1_{e₀}).sources = symmDiff (n.sources) (e₀.toFinset)`.
Proof: `0 < n e₀` implies `fromEdgeFinset {e₀} ≤ n` pointwise, then
`sub_sources_eq_symmDiff` (PR #870) gives the symmDiff formula, and
`fromEdgeFinset_singleton_sources` (PR #813) identifies the
singleton-edge sources with the endpoint pair. Used in the edge-peeling
step of Simon-Lieb (GJ §5.1 / FV Prop 9.31). -/
theorem Current.sources_sub_edge_symmDiff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (e₀ : (inducedGraph G Λ).edgeSet) (he : 0 < n e₀) :
    (n - Current.fromEdgeFinset G Λ {e₀}).sources G Λ =
      symmDiff (n.sources G Λ) (e₀ : Sym2 ↑Λ).toFinset := by
  have hle : Current.fromEdgeFinset G Λ {e₀} ≤ n := by
    intro e
    unfold Current.fromEdgeFinset
    simp only [Finset.mem_singleton]
    split_ifs with h
    · subst h; exact he
    · exact Nat.zero_le _
  rw [Current.sub_sources_eq_symmDiff G Λ hle,
      Current.fromEdgeFinset_singleton_sources]

set_option linter.unusedDecidableInType false in
/-- Helper: sum of weights over `boundedFinset N` is bounded by `exp(β*J)^|edgeSet|`.
Extracted from `CurrentBounded.weightSum_le_exp_pow_card` without the source indicator. -/
private theorem Current.sum_weight_boundedFinset_le
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (N : ℕ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    ∑ n ∈ Current.boundedFinset G Λ N, n.weight G Λ β J ≤
      Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet := by
  -- Step 1: rewrite boundedFinset as univ.map emb (avoids DecidableEq in sum)
  set emb : CurrentBounded G Λ N ↪ Current G Λ :=
    ⟨CurrentBounded.toCurrent G Λ,
     fun x y h => funext (fun e => Fin.val_injective (congrFun h e))⟩
  have hmapeq : Current.boundedFinset G Λ N = Finset.univ.map emb := by
    classical
    ext n
    simp only [Current.mem_boundedFinset_iff, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · intro hn
      exact ⟨fun e => ⟨n e, Nat.lt_succ_iff.mpr (hn e)⟩, funext fun e => rfl⟩
    · rintro ⟨a, rfl⟩
      exact fun e => Nat.lt_succ_iff.mp (a e).is_lt
  -- Step 2: sum over map equals sum over source via Finset.sum_map
  have h_conv : ∑ n ∈ Current.boundedFinset G Λ N, n.weight G Λ β J =
      ∑ n : CurrentBounded G Λ N, (n.toCurrent G Λ).weight G Λ β J := by
    rw [hmapeq, Finset.sum_map]; rfl
  -- Step 3: product-sum exchange for CurrentBounded
  have h_prod : ∑ n : CurrentBounded G Λ N, (n.toCurrent G Λ).weight G Λ β J =
      ∏ e : (inducedGraph G Λ).edgeSet,
        ∑ k : Fin (N + 1), (β * J) ^ (k : ℕ) / ((k : ℕ).factorial : ℝ) :=
    (Fintype.prod_sum (κ := fun _ => Fin (N + 1))
      (fun _ k => (β * J) ^ (k : ℕ) / ((k : ℕ).factorial : ℝ))).symm
  rw [h_conv, h_prod]
  calc ∏ e : (inducedGraph G Λ).edgeSet,
          ∑ k : Fin (N + 1), (β * J) ^ (k : ℕ) / ((k : ℕ).factorial : ℝ)
      ≤ ∏ _ : (inducedGraph G Λ).edgeSet, Real.exp (β * J) :=
          Finset.prod_le_prod
            (fun e _ => Finset.sum_nonneg (fun k _ =>
              div_nonneg (pow_nonneg hβJ _) (Nat.cast_nonneg _)))
            (fun e _ => by
              rw [Fin.sum_univ_eq_sum_range
                (fun k => (β * J) ^ k / (k.factorial : ℝ)) (N + 1)]
              exact Real.partial_sum_le_exp_of_nonneg hβJ N)
    _ = Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet := by
          rw [Finset.prod_const, Finset.card_univ]

set_option linter.unusedDecidableInType false in
/-- Helper: for any source set `A` and `0 ≤ β * J`, the source-filtered weight function
`fun n => if n.sources G Λ = A then n.weight β J else 0` is summable.
Proof by `summable_of_sum_le`: every finite partial sum is bounded by
`exp(β*J)^|edgeSet|` via `sum_weight_boundedFinset_le`. -/
private theorem Current.summable_weight_if_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    Summable (fun n : Current G Λ => if n.sources G Λ = A then n.weight G Λ β J else 0) := by
  have hnn : ∀ n : Current G Λ, 0 ≤ (if n.sources G Λ = A then n.weight G Λ β J else 0) := by
    intro n
    by_cases h : n.sources G Λ = A
    · rw [if_pos h]; exact Current.weight_nonneg G Λ hβJ _
    · simp [h]
  refine summable_of_sum_le
      (c := Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet) hnn ?_
  intro s
  have hs : s ⊆ Current.boundedFinset G Λ (s.sup (fun n => Finset.univ.sup n)) := by
    intro n hn; rw [Current.mem_boundedFinset_iff]
    exact fun e => Nat.le_trans (Finset.le_sup (Finset.mem_univ e)) (Finset.le_sup hn)
  calc ∑ n ∈ s, (if n.sources G Λ = A then n.weight G Λ β J else 0)
      ≤ ∑ n ∈ s, n.weight G Λ β J :=
          Finset.sum_le_sum (fun n _ => by
            rcases Classical.em (n.sources G Λ = A) with h | h
            · exact le_of_eq (if_pos h)
            · exact le_trans (le_of_eq (if_neg h)) (Current.weight_nonneg G Λ hβJ n))
    _ ≤ ∑ n ∈ Current.boundedFinset G Λ _, n.weight G Λ β J :=
          Finset.sum_le_sum_of_subset_of_nonneg hs (fun n _ _ => Current.weight_nonneg G Λ hβJ n)
    _ ≤ Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet :=
          Current.sum_weight_boundedFinset_le G Λ _ hβJ

set_option linter.unusedDecidableInType false in
/-- **`Current.weightSum` equals the supremum of bounded sums**: for `0 ≤ β J`,
\(Current.weightSum A β J = ⨆_N CurrentBounded.weightSum N A β J\).
Proof by uniqueness of limits: the bounded sums converge to both
`Current.weightSum` (via `tendsto_weightSum_atTop_currentWeightSum` using
`summable_weight_if_sources`) and to the `⨆`
(via `tendsto_weightSum_atTop_iSup_of_nonneg`). -/
theorem Current.weightSum_eq_iSup
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    Current.weightSum G Λ A β J = ⨆ N : ℕ, CurrentBounded.weightSum G Λ N A β J :=
  tendsto_nhds_unique
    (CurrentBounded.tendsto_weightSum_atTop_currentWeightSum G Λ β J A
      (Current.summable_weight_if_sources G Λ A hβJ))
    (CurrentBounded.tendsto_weightSum_atTop_iSup_of_nonneg G Λ A hβJ)

set_option linter.unusedDecidableInType false in
/-- Helper: for each edge `e` at `i`, a finite sum of peeled weights over currents
with sources `{i,j}` and `n e ≥ 1` is bounded by `weightSum(symmDiff {i,j} endpoints(e))`.
Uses: `Finset.sum_image` (injection n ↦ n - 1_e) + `sources_sub_edge_symmDiff`
(bridge: sources of n - 1_e = symmDiff {i,j} endpoints(e)) + `Summable.sum_le_tsum`. -/
private theorem Current.sum_filter_le_weightSum_symmDiff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {i j : ↑Λ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    (e : (inducedGraph G Λ).edgeSet) (u : Finset (Current G Λ)) :
    ∑ n ∈ u, (if n.sources G Λ = {i, j} ∧ 1 ≤ n e then
        (n - Current.fromEdgeFinset G Λ {e}).weight G Λ β J else 0) ≤
      ∑' n : Current G Λ,
        (if n.sources G Λ = symmDiff {i, j} (e : Sym2 ↑Λ).toFinset then
          n.weight G Λ β J else 0) := by
  classical
  -- Rewrite as sum over the filter {src={i,j} ∧ n_e ≥ 1}
  rw [← Finset.sum_filter]
  -- Injectivity of n ↦ n - 1_e on the filter
  have hinj : ∀ n₁ ∈ u.filter (fun n => n.sources G Λ = {i, j} ∧ 1 ≤ n e),
      ∀ n₂ ∈ u.filter (fun n => n.sources G Λ = {i, j} ∧ 1 ≤ n e),
      n₁ - Current.fromEdgeFinset G Λ {e} = n₂ - Current.fromEdgeFinset G Λ {e} → n₁ = n₂ := by
    intro n₁ h₁ n₂ h₂ heq
    have h₁e := (Finset.mem_filter.mp h₁).2.2
    have h₂e := (Finset.mem_filter.mp h₂).2.2
    funext edge
    have := congrFun heq edge
    simp only [Current.sub_apply, Current.fromEdgeFinset, Finset.mem_singleton] at this
    by_cases hedge : edge = e
    · subst hedge; simp only [↓reduceIte] at this; omega
    · simp only [hedge, ↓reduceIte, Nat.sub_zero] at this; exact this
  -- Each element in the filter image has sources = symmDiff (by bridge lemma)
  have h_src : ∀ n ∈ u.filter (fun n => n.sources G Λ = {i, j} ∧ 1 ≤ n e),
      (n - Current.fromEdgeFinset G Λ {e}).sources G Λ =
        symmDiff {i, j} (e : Sym2 ↑Λ).toFinset := by
    intro n hn
    rw [Current.sources_sub_edge_symmDiff G Λ n e (Finset.mem_filter.mp hn).2.2,
        (Finset.mem_filter.mp hn).2.1]
  -- The sum over the filter equals the sum of f_sd over the image (using sum_image + bridge)
  have h_image_eq :
      ∑ n ∈ u.filter (fun n => n.sources G Λ = {i, j} ∧ 1 ≤ n e),
        (n - Current.fromEdgeFinset G Λ {e}).weight G Λ β J =
      ∑ m ∈ (u.filter (fun n => n.sources G Λ = {i, j} ∧ 1 ≤ n e)).image
          (fun n => n - Current.fromEdgeFinset G Λ {e}),
        (if m.sources G Λ = symmDiff {i, j} (e : Sym2 ↑Λ).toFinset then
          m.weight G Λ β J else 0) := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun n hn => (if_pos (h_src n hn)).symm)
  rw [h_image_eq]
  -- Apply sum_le_tsum with summability
  exact (Current.summable_weight_if_sources G Λ _ hβJ).sum_le_tsum _
    (fun m _ => by
      split_ifs with h
      · exact Current.weight_nonneg G Λ hβJ _
      · exact le_refl _)

set_option linter.unusedDecidableInType false in
set_option linter.unusedVariables false in
/-- **Edge-peeling bound for `weightSum`**: for `i ≠ j` in `Λ` and
`0 ≤ β * J`, the pair-source weighted sum satisfies
`weightSum G Λ {i,j} β J ≤ β*J * ∑_{e ∋ i} weightSum G Λ (symmDiff {i,j} endpoints(e)) β J`.
Proof: apply `Real.tsum_le_of_sum_le`; for each Finset `u` of currents,
for each n with sources `{i,j}`, pick an active edge `e₀` at `i` via
`supportAt_nonempty_of_mem_sources`, bound `w(n) ≤ β*J * w(n - 1_{e₀})` via
`weight_le_mul_pred_edge`, then `Finset.single_le_sum` absorbs `w(n - 1_{e₀})` into
the edge sum. After `Finset.sum_comm`, each inner per-edge sum is bounded by
`weightSum(symmDiff)` via `sum_filter_le_weightSum_symmDiff`. (GJ §5.1 / FV Prop 9.31) -/
theorem Current.weightSum_pair_le_edge_sum
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {i j : ↑Λ} (hij : i ≠ j) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    Current.weightSum G Λ {i, j} β J ≤
      β * J *
        ∑ e ∈ Finset.univ.filter
            (fun e : (inducedGraph G Λ).edgeSet => i ∈ (e : Sym2 ↑Λ)),
          Current.weightSum G Λ (symmDiff {i, j} (e : Sym2 ↑Λ).toFinset) β J := by
  unfold Current.weightSum
  apply Real.tsum_le_of_sum_le
    (fun n => by
      split_ifs with h
      · exact Current.weight_nonneg G Λ hβJ _
      · exact le_refl _)
  intro u
  classical
  set E := Finset.univ.filter (fun e : (inducedGraph G Λ).edgeSet => i ∈ (e : Sym2 ↑Λ))
  -- Step 1: pointwise bound n.weight ≤ β*J * ∑_{e ∈ E, src={i,j}∧n_e≥1} (n-1_e).weight
  calc ∑ n ∈ u, (if n.sources G Λ = {i, j} then n.weight G Λ β J else 0)
      ≤ ∑ n ∈ u, β * J * ∑ e ∈ E,
            (if n.sources G Λ = {i, j} ∧ 1 ≤ n e then
              (n - Current.fromEdgeFinset G Λ {e}).weight G Λ β J else 0) := by
        apply Finset.sum_le_sum; intro n _
        by_cases h : n.sources G Λ = {i, j}
        · -- src = {i,j}: get active edge e₀ at i
          rw [if_pos h]
          obtain ⟨e₀, he₀⟩ := Current.supportAt_nonempty_of_mem_sources G Λ n
              (h ▸ Finset.mem_insert_self i {j})
          rw [Current.mem_supportAt_iff] at he₀
          obtain ⟨he₀_supp, he₀_i⟩ := he₀
          have he₀_pos : 0 < n e₀ :=
              Nat.pos_of_ne_zero ((Current.mem_support_iff G Λ n e₀).mp he₀_supp)
          have he₀_E : e₀ ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he₀_i⟩
          calc n.weight G Λ β J
              ≤ β * J * (n - Current.fromEdgeFinset G Λ {e₀}).weight G Λ β J :=
                  Current.weight_le_mul_pred_edge G Λ hβJ n e₀ he₀_pos
            _ = β * J * (if n.sources G Λ = {i, j} ∧ 1 ≤ n e₀ then
                    (n - Current.fromEdgeFinset G Λ {e₀}).weight G Λ β J else 0) :=
                  by rw [if_pos ⟨h, he₀_pos⟩]
            _ ≤ β * J * ∑ e ∈ E, (if n.sources G Λ = {i, j} ∧ 1 ≤ n e then
                    (n - Current.fromEdgeFinset G Λ {e}).weight G Λ β J else 0) :=
                  mul_le_mul_of_nonneg_left
                    (Finset.single_le_sum
                      (f := fun e => if n.sources G Λ = {i, j} ∧ 1 ≤ n e then
                          (n - Current.fromEdgeFinset G Λ {e}).weight G Λ β J else 0)
                      (fun e _ => by
                        dsimp only
                        split_ifs with h
                        · exact Current.weight_nonneg G Λ hβJ _
                        · exact le_refl _)
                      he₀_E)
                    hβJ
        · -- src ≠ {i,j}: trivial
          rw [if_neg h]
          exact mul_nonneg hβJ (Finset.sum_nonneg (fun e _ => by
            split_ifs with h
            · exact Current.weight_nonneg G Λ hβJ _
            · exact le_refl _))
    -- Step 2: interchange sums
    _ = β * J * ∑ e ∈ E, ∑ n ∈ u,
            (if n.sources G Λ = {i, j} ∧ 1 ≤ n e then
              (n - Current.fromEdgeFinset G Λ {e}).weight G Λ β J else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    -- Step 3: bound each inner per-edge sum by weightSum(symmDiff)
    _ ≤ β * J * ∑ e ∈ E,
          (∑' m : Current G Λ, if m.sources G Λ = symmDiff {i, j} (e : Sym2 ↑Λ).toFinset then
              m.weight G Λ β J else 0) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun e _ =>
            Current.sum_filter_le_weightSum_symmDiff G Λ hβJ e u))
          hβJ

end Ambient

end IsingModel
