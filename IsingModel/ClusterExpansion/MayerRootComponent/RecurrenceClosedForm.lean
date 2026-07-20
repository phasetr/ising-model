import IsingModel.ClusterExpansion.AlternatingCompleteGraph
import IsingModel.ClusterExpansion.MayerRootComponent.FiberProduct
import IsingModel.ClusterExpansion.MayerRootComponent.FactorReindex

/-!
# Mayer K_n root-component recurrence (4/5): the recurrence and its closed form

Structural split (4/5) of `IsingModel.ClusterExpansion.MayerRootComponent`.
This child assembles the root-component recurrence over `K_n`, identifies the surviving
root-component sets, derives the collapse `c_n + (n-1) c_{n-1} = 0` and solves it into the
closed form `c_n = (-1)^(n-1) (n-1)!`.  See the
`IsingModel.ClusterExpansion.MayerRootComponent` facade module for the full contents
overview.
-/

namespace IsingModel

open Finset

/-- **Root-component recurrence for the complete graph** (Mayer Phase B): the
signed all-subgraph sum of `K_n` decomposes over the root component `C ∋ r` as
`D_n = ∑_{C ∋ r} c(K_C) · D(K_{Cᶜ})`, i.e.
`D_n = ∑_{C ∋ 0} c_{|C|} D_{n-|C|}` once `c`, `D` are seen to depend only on the
cardinalities. Assembles the fibrewise decomposition
`allSignedSubgraphSum_eq_sum_fiber_product` (lemma 7) with the inside and outside
reindexes (`insideConnectedEdgeSubsets_completeGraph_signed_sum`,
`outsideEdgeSubsets_completeGraph_signed_sum`). The combinatorial core of the
Mayer identity `alternatingConnectedSubgraphSum K_n = (-1)^(n-1)(n-1)!` (GJ §18.4);
the remaining step is the collapse `D_m = 0` (`m ≥ 2`), `D_0 = D_1 = 1` to
`c_n + (n-1)c_{n-1} = 0`. -/
theorem allSignedSubgraphSum_completeGraph_root_recurrence {V : Type*} [Fintype V] [DecidableEq V]
    (r : V) :
    allSignedSubgraphSum (⊤ : SimpleGraph V)
      = ∑ C ∈ Finset.univ.powerset.filter (fun C : Finset V => r ∈ C),
          alternatingConnectedSubgraphSum (⊤ : SimpleGraph (C : Finset V))
            * allSignedSubgraphSum (⊤ : SimpleGraph (Cᶜ : Finset V)) := by
  rw [allSignedSubgraphSum_eq_sum_fiber_product (⊤ : SimpleGraph V) r]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [insideConnectedEdgeSubsets_completeGraph_signed_sum,
    outsideEdgeSubsets_completeGraph_signed_sum]

/-- **Surviving root-component sets**: in the recurrence over `K_n`, the vertex
sets `C` containing the root `0` whose complement has `≤ 1` element are exactly
`univ` (full set) together with the cofinite singletons `{j}ᶜ` for `j ≠ 0`. The
sets with `|Cᶜ| ≥ 2` contribute `0` (since `D(K_{Cᶜ}) = 0`), so only these survive
the collapse `D_n = c_n + (n-1)c_{n-1}`. -/
theorem mayer_surviving_set {n : ℕ} [NeZero n] :
    Finset.univ.powerset.filter
        (fun C : Finset (Fin n) => (0 : Fin n) ∈ C ∧ Cᶜ.card ≤ 1)
      = insert Finset.univ
          ((Finset.univ.erase (0 : Fin n)).image (fun j => ({j}ᶜ : Finset (Fin n)))) := by
  classical
  ext C
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
    Finset.mem_insert, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨h0, hcard⟩
    by_cases hCc : Cᶜ = ∅
    · left
      rw [← compl_compl C, hCc, compl_empty]
    · right
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hCc
      have hCcj : Cᶜ = {j} := by
        apply Finset.Subset.antisymm
        · intro a ha
          rw [Finset.mem_singleton]
          exact Finset.card_le_one.mp hcard a ha j hj
        · rw [Finset.singleton_subset_iff]; exact hj
      refine ⟨j, fun h => (Finset.mem_compl.mp (h ▸ hj)) h0, ?_⟩
      rw [← compl_compl C, hCcj]
  · rintro (rfl | ⟨j, hj0, rfl⟩)
    · exact ⟨Finset.mem_univ 0, by rw [compl_univ]; simp⟩
    · refine ⟨?_, ?_⟩
      · rw [Finset.mem_compl, Finset.mem_singleton]
        exact fun h => hj0 h.symm
      · rw [compl_compl, Finset.card_singleton]

/-- **Mayer recurrence for the complete-graph connected-spanning sum**: for
`n ≥ 2`, `c_n + (n-1)·c_{n-1} = 0` where `c_m = alternatingConnectedSubgraphSum
(⊤ : SimpleGraph (Fin m))`. Collapses the root-component recurrence
`allSignedSubgraphSum_completeGraph_root_recurrence`: `D_n = ∑_{C ∋ 0} c(K_C)·D(K_{Cᶜ})`,
using `D(K_{Cᶜ}) = 0` unless `|Cᶜ| ≤ 1` (so only `C = univ` and the `n-1` cofinite
singletons `{j}ᶜ` survive, `mayer_surviving_set`), `c`'s cardinality-invariance,
and `D_n = 0` for `n ≥ 2`. The recurrence yielding the closed form
`c_n = (-1)^(n-1)(n-1)!`. -/
theorem alternatingConnectedSubgraphSum_completeGraph_recurrence {n : ℕ} (hn : 2 ≤ n) :
    alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin n))
      + (↑(n - 1) : ℝ) * alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin (n - 1))) = 0 := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hrec := allSignedSubgraphSum_completeGraph_root_recurrence (V := Fin n) (0 : Fin n)
  rw [allSignedSubgraphSum_completeGraph_eq_zero_of_two_le hn] at hrec
  -- fold `D(K_Cᶜ)` into an `ite` and restrict to the surviving sets
  have key : ∀ C : Finset (Fin n),
      alternatingConnectedSubgraphSum (⊤ : SimpleGraph (C : Finset (Fin n)))
          * allSignedSubgraphSum (⊤ : SimpleGraph (Cᶜ : Finset (Fin n)))
        = if Cᶜ.card ≤ 1 then
            alternatingConnectedSubgraphSum (⊤ : SimpleGraph (C : Finset (Fin n))) else 0 := by
    intro C
    rw [allSignedSubgraphSum_completeGraph_subtype_eq_ite]
    split <;> simp
  simp_rw [key] at hrec
  rw [← Finset.sum_filter, Finset.filter_filter, mayer_surviving_set] at hrec
  -- the two surviving groups: `univ` and the cofinite singletons `{j}ᶜ`
  have hnotmem : (Finset.univ : Finset (Fin n)) ∉
      (Finset.univ.erase (0 : Fin n)).image (fun j => ({j}ᶜ : Finset (Fin n))) := by
    rw [Finset.mem_image]
    rintro ⟨j, _, hj⟩
    have : ({j} : Finset (Fin n)) = ∅ := by
      rw [← compl_compl ({j} : Finset (Fin n)), hj, compl_univ]
    simp at this
  have himinj : Set.InjOn (fun j => ({j}ᶜ : Finset (Fin n)))
      (Finset.univ.erase (0 : Fin n)) := by
    intro a _ b _ hab
    simpa using compl_injective hab
  rw [Finset.sum_insert hnotmem, Finset.sum_image himinj] at hrec
  -- evaluate the `univ` term as `c_n`
  have huniv : alternatingConnectedSubgraphSum (⊤ : SimpleGraph ((Finset.univ : Finset (Fin n)))) =
      alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin n)) := by
    rw [alternatingConnectedSubgraphSum_completeGraph_card]
    rw [show Fintype.card (((Finset.univ : Finset (Fin n)) : Finset (Fin n))) = n by
      rw [Fintype.card_coe, Finset.card_univ, Fintype.card_fin]]
  -- evaluate each singleton term as `c_{n-1}`
  have hsingle : ∀ j ∈ Finset.univ.erase (0 : Fin n),
      alternatingConnectedSubgraphSum (⊤ : SimpleGraph (({j}ᶜ : Finset (Fin n)))) =
        alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin (n - 1))) := by
    intro j _
    rw [alternatingConnectedSubgraphSum_completeGraph_card]
    rw [show Fintype.card ((({j}ᶜ : Finset (Fin n)) : Finset (Fin n))) = n - 1 by
      rw [Fintype.card_coe, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]]
  rw [huniv, Finset.sum_congr rfl hsingle, Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hrec
  -- hrec : 0 = c_n + (↑(n-1)) * c_{n-1}
  linarith [hrec]

/-- **Mayer closed form** (GJ §18.4, the general-`n` Mayer coefficient identity):
`alternatingConnectedSubgraphSum K_n = (-1)^(n-1)(n-1)!` for `n ≥ 1`. Proved by
induction from the recurrence `alternatingConnectedSubgraphSum_completeGraph_recurrence`
(`c_n = -(n-1)c_{n-1}`) with base case `alternatingConnectedSubgraphSum_K1`
(`c_1 = 1`); the step uses `m! = m·(m-1)!` and `(-1)^m = -(-1)^(m-1)`. This is the
Mayer/Ursell coefficient of the complete-graph cluster expansion, completing the
root-component recurrence programme for the connected-spanning signed sum. -/
theorem alternatingConnectedSubgraphSum_completeGraph_closed_form {n : ℕ} (hn : 1 ≤ n) :
    alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin n))
      = (-1 : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [alternatingConnectedSubgraphSum_K1]
    norm_num
  | succ m hm ih =>
    have hrec := alternatingConnectedSubgraphSum_completeGraph_recurrence (n := m + 1) (by omega)
    rw [Nat.add_sub_cancel] at hrec
    have hc : alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin (m + 1)))
        = -(↑m : ℝ) * alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin m)) := by
      linarith [hrec]
    have hfac : (Nat.factorial m : ℝ) = (m : ℝ) * (Nat.factorial (m - 1) : ℝ) := by
      rw [← Nat.mul_factorial_pred (show m ≠ 0 by omega)]
      push_cast
      ring
    have hpow : (-1 : ℝ) ^ m = -((-1 : ℝ) ^ (m - 1)) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
      ring
    rw [hc, ih, Nat.add_sub_cancel, hfac, hpow]
    ring

end IsingModel
