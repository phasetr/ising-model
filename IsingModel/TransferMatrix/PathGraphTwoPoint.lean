import IsingModel.TransferMatrix.PathGraphEdges
import IsingModel.Conditioning.CorrelationClosed.ClosedForm

/-!
# Exact open 1D chain two-point function `⟨σ₀σₙ⟩ = (tanh βJ)ⁿ` (GJ §17.1)

The open path graph `pathGraph (n+1)` is a tree, so the FV (3.46) high-temperature
expansion of its two-point function `correlation (pathGraph (n+1)) ⟨J,0,β⟩ {0, n}`
collapses: the even-degree subgraph denominator is `{∅}` (sum `1`) and the
`{0,n}`-odd-boundary numerator is the single full edge set (sum `tanhⁿ`).  Hence

  `correlation (pathGraph (n+1)) ⟨J,0,β⟩ {0, Fin.last n} = (tanh βJ)ⁿ`.

This is the exact finite-volume open-chain two-point function — the input (no
boundary correction) to the infinite-volume limit `twoPointFunction 1 = (tanh βJ)^dist`
(Issue #3532).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators
open SimpleGraph Finset

/-- **Per-vertex incidence card on the open path** (index-set form): for an index
subset `S : Finset (Fin n)` and a vertex `⟨k,_⟩`, the number of edges
`s(i.castSucc, i.succ)` (`i ∈ S`) incident to `⟨k,_⟩` splits into the
left-endpoint contribution (`i.val = k`) and the right-endpoint contribution
(`i.val + 1 = k`). -/
theorem incident_filter_card (n : ℕ) (S : Finset (Fin n)) (k : ℕ) (hk : k < n + 1) :
    ((S.image (fun i : Fin n => s(i.castSucc, i.succ))).filter
        (fun e => (⟨k, hk⟩ : Fin (n + 1)) ∈ e)).card
      = (S.filter (fun i : Fin n => (i : ℕ) = k)).card
        + (S.filter (fun i : Fin n => (i : ℕ) + 1 = k)).card := by
  classical
  rw [Finset.filter_image, Finset.card_image_of_injOn ((pathPair_injective n).injOn)]
  have hpred : (S.filter (fun i : Fin n => (⟨k, hk⟩ : Fin (n + 1)) ∈ s(i.castSucc, i.succ)))
      = S.filter (fun i : Fin n => (i : ℕ) = k ∨ (i : ℕ) + 1 = k) := by
    apply Finset.filter_congr
    intro i _
    rw [Sym2.mem_iff]
    simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    omega
  rw [hpred, Finset.filter_or, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro i _ h1 h2
  omega

/-- `S.filter (i.val = k)` has card `1` when the index `⟨k,_⟩ ∈ S` and `0` otherwise. -/
theorem filter_val_eq_card (n : ℕ) (S : Finset (Fin n)) (k : ℕ) (hk : k < n) :
    (S.filter (fun i : Fin n => (i : ℕ) = k)).card
      = if (⟨k, hk⟩ : Fin n) ∈ S then 1 else 0 := by
  classical
  have : (S.filter (fun i : Fin n => (i : ℕ) = k))
      = S.filter (fun i : Fin n => i = ⟨k, hk⟩) := by
    apply Finset.filter_congr; intro i _
    rw [Fin.ext_iff]
  rw [this, Finset.filter_eq']
  by_cases h : (⟨k, hk⟩ : Fin n) ∈ S <;> simp [h]

/-- On the open path, every index `i ∈ Fin n` lies below `n`, so `i.val = n` is
never satisfied: the right-end vertex `n` only sees the left-end contribution. -/
theorem filter_val_eq_n_card (n : ℕ) (S : Finset (Fin n)) :
    (S.filter (fun i : Fin n => (i : ℕ) = n)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  exact Nat.ne_of_lt i.isLt

/-- `S.filter (i.val + 1 = k)` (`1 ≤ k`, `k-1 < n`) has card `1` iff the predecessor
index `⟨k-1,_⟩ ∈ S`. -/
theorem filter_val_succ_card (n : ℕ) (S : Finset (Fin n)) (k : ℕ) (hk1 : k - 1 < n)
    (hk0 : 1 ≤ k) :
    (S.filter (fun i : Fin n => (i : ℕ) + 1 = k)).card
      = if (⟨k - 1, hk1⟩ : Fin n) ∈ S then 1 else 0 := by
  classical
  have : (S.filter (fun i : Fin n => (i : ℕ) + 1 = k))
      = S.filter (fun i : Fin n => i = ⟨k - 1, hk1⟩) := by
    apply Finset.filter_congr; intro i _
    rw [Fin.ext_iff]; simp only []; omega
  rw [this, Finset.filter_eq']
  by_cases h : (⟨k - 1, hk1⟩ : Fin n) ∈ S <;> simp [h]

/-- `S.filter (i.val + 1 = 0)` is empty: `i.val + 1 = 0` is unsatisfiable. -/
theorem filter_val_succ_zero_card (n : ℕ) (S : Finset (Fin n)) :
    (S.filter (fun i : Fin n => (i : ℕ) + 1 = 0)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _; omega

/-- **Index set of an edge subset of the open path**: the indices `i : Fin n`
whose edge `s(i.castSucc, i.succ)` belongs to `X`. -/
def idx (n : ℕ) (X : Finset (Sym2 (Fin (n + 1)))) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => s(i.castSucc, i.succ) ∈ X)

/-- An edge subset of the open path is the `pathPair`-image of its index set. -/
theorem image_idx_eq (n : ℕ) (X : Finset (Sym2 (Fin (n + 1))))
    (hX : X ⊆ (pathGraph (n + 1)).edgeFinset) :
    X = (idx n X).image (fun i : Fin n => s(i.castSucc, i.succ)) := by
  ext e
  constructor
  · intro he
    have he' : e ∈ (pathGraph (n + 1)).edgeFinset := hX he
    rw [pathGraph_edgeFinset_eq_image, Finset.mem_image] at he'
    obtain ⟨i, _, rfl⟩ := he'
    rw [Finset.mem_image]
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
  · intro he
    rw [Finset.mem_image] at he
    obtain ⟨i, hi, rfl⟩ := he
    exact (Finset.mem_filter.mp hi).2

/-- **Vertex degree of an open-path edge subset** in index-set form: for
`X ⊆ edgeFinset` and vertex `⟨k,_⟩`, the degree splits into the left
(`i.val = k`) and right (`i.val + 1 = k`) index contributions over `idx n X`. -/
theorem deg_eq_of_subset (n : ℕ) (X : Finset (Sym2 (Fin (n + 1))))
    (hX : X ⊆ (pathGraph (n + 1)).edgeFinset) (k : ℕ) (hk : k < n + 1) :
    (X.filter (fun e => (⟨k, hk⟩ : Fin (n + 1)) ∈ e)).card
      = ((idx n X).filter (fun i : Fin n => (i : ℕ) = k)).card
        + ((idx n X).filter (fun i : Fin n => (i : ℕ) + 1 = k)).card := by
  conv_lhs => rw [image_idx_eq n X hX]
  exact incident_filter_card n (idx n X) k hk

/-- **Empty subgraph has even degree everywhere** (GJ §17.1): trivially the empty
edge set has degree `0` at every vertex. -/
theorem empty_even_parity (n : ℕ) :
    ∀ v : Fin (n + 1),
      Even ((∅ : Finset (Sym2 (Fin (n + 1)))).filter (v ∈ ·)).card := by
  intro v; simp

/-- **Even-subgraph denominator on the open path is the empty set** (GJ §17.1): any
edge subset of `pathGraph (n+1)` with even degree at every vertex is `∅` (the path
is a tree). -/
theorem even_subgraph_eq_empty (n : ℕ) (X : Finset (Sym2 (Fin (n + 1))))
    (hXsub : X ⊆ (pathGraph (n + 1)).edgeFinset)
    (hpar : ∀ v : Fin (n + 1), Even (X.filter (v ∈ ·)).card) : X = ∅ := by
  classical
  rw [image_idx_eq n X hXsub, Finset.image_eq_empty]
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  set S := idx n X with hS
  -- pick the minimal index; the vertex at its left endpoint has odd degree
  have hmin : ∀ j ∈ S, S.min' ⟨i₀, hi₀⟩ ≤ j := fun j hj => Finset.min'_le S j hj
  set i := S.min' ⟨i₀, hi₀⟩ with hi
  have hiS : i ∈ S := Finset.min'_mem S ⟨i₀, hi₀⟩
  have hk : (i : ℕ) < n + 1 := by omega
  have hdeg := deg_eq_of_subset n X hXsub (i : ℕ) hk
  rw [← hS] at hdeg
  -- left contribution = 1
  have hleft : (S.filter (fun j : Fin n => (j : ℕ) = (i : ℕ))).card = 1 := by
    rw [filter_val_eq_card n S (i : ℕ) i.isLt]
    have : (⟨(i : ℕ), i.isLt⟩ : Fin n) = i := by ext; rfl
    rw [this, if_pos hiS]
  -- right contribution = 0
  have hright : (S.filter (fun j : Fin n => (j : ℕ) + 1 = (i : ℕ))).card = 0 := by
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [h0]; exact filter_val_succ_zero_card n S
    · have hk1 : (i : ℕ) - 1 < n := by omega
      rw [filter_val_succ_card n S (i : ℕ) hk1 h0, if_neg]
      intro hmem
      have := hmin _ hmem
      have : (i : ℕ) ≤ (i : ℕ) - 1 := this
      omega
  have hdeg1 : (X.filter (fun e => ((⟨(i : ℕ), hk⟩ : Fin (n + 1)) ∈ e))).card = 1 := by
    rw [hdeg, hleft, hright]
  have := hpar ⟨(i : ℕ), hk⟩
  rw [hdeg1] at this
  exact (Nat.not_even_one) this

/-- **The full edge set has odd degree exactly at the two endpoints** (GJ §17.1):
on `pathGraph (n+1)`, every vertex of the full edge set has degree `1` at the
endpoints `0`, `n` and `2` in the interior, matching the `{0,n}`-odd-boundary
parity condition. -/
theorem edgeFinset_endpoint_parity (n : ℕ) (hn : 0 < n) :
    ∀ v : Fin (n + 1),
      Even ((if v ∈ ({0, Fin.last n} : Finset (Fin (n + 1))) then 1 else 0)
        + ((pathGraph (n + 1)).edgeFinset.filter (v ∈ ·)).card) := by
  intro v
  have hdeg := deg_eq_of_subset n _ (Finset.Subset.refl _) (v : ℕ) v.isLt
  have hidx : idx n (pathGraph (n + 1)).edgeFinset = Finset.univ := by
    ext i; simp only [idx, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rw [pathGraph_edgeFinset_eq_image, Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, rfl⟩
  rw [hidx] at hdeg
  have hve : (⟨(v : ℕ), v.isLt⟩ : Fin (n + 1)) = v := by ext; rfl
  rw [hve] at hdeg
  -- compute degree by the value of v
  rcases Nat.lt_or_ge (v : ℕ) n with hvn | hvn
  · -- v.val < n : left contribution 1
    rw [filter_val_eq_card n Finset.univ (v : ℕ) hvn, if_pos (Finset.mem_univ _)] at hdeg
    rcases Nat.eq_zero_or_pos (v : ℕ) with h0 | h0
    · -- v = 0 ∈ A : right contribution 0, deg = 1, (1) + 1 even
      rw [h0, filter_val_succ_zero_card n Finset.univ] at hdeg
      have hv0 : v = 0 := by ext; rw [h0]; rfl
      rw [if_pos (by rw [hv0]; exact Finset.mem_insert_self _ _)]
      rw [hdeg]; decide
    · -- 0 < v.val < n : interior, right contribution 1, deg = 2, even
      have hk1 : (v : ℕ) - 1 < n := by omega
      rw [filter_val_succ_card n Finset.univ (v : ℕ) hk1 h0,
        if_pos (Finset.mem_univ _)] at hdeg
      have hvA : v ∉ ({0, Fin.last n} : Finset (Fin (n + 1))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        · rw [h] at h0; simp at h0
        · rw [h] at hvn; simp [Fin.last] at hvn
      rw [if_neg hvA, hdeg]; decide
  · -- v.val = n (the last vertex) : left contribution 0, right contribution 1
    have hvn' : (v : ℕ) = n := by omega
    rw [hvn', filter_val_eq_n_card n Finset.univ] at hdeg
    have hk1 : n - 1 < n := by omega
    rw [filter_val_succ_card n Finset.univ n hk1 hn, if_pos (Finset.mem_univ _)] at hdeg
    have hvlast : v = Fin.last n := by ext; rw [hvn']; rfl
    rw [if_pos (by rw [hvlast]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
      hdeg]
    decide

/-- **`{0,n}`-odd-boundary subgraph on the open path is the full edge set** (GJ §17.1):
any edge subset of `pathGraph (n+1)` with odd degree exactly at the two endpoints
`0`, `n` (even elsewhere) is the full edge set (the path is a tree). -/
theorem endpoint_subgraph_eq_edgeFinset (n : ℕ)
    (X : Finset (Sym2 (Fin (n + 1))))
    (hXsub : X ⊆ (pathGraph (n + 1)).edgeFinset)
    (hpar : ∀ v : Fin (n + 1),
      Even ((if v ∈ ({0, Fin.last n} : Finset (Fin (n + 1))) then 1 else 0)
        + (X.filter (v ∈ ·)).card)) :
    X = (pathGraph (n + 1)).edgeFinset := by
  classical
  -- show idx X = univ, then X = edgeFinset
  have hidxuniv : idx n X = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    by_contra hne
    simp only [not_forall] at hne
    obtain ⟨j₀, hj₀⟩ := hne
    set S := idx n X with hS
    set T := Finset.univ \ S with hT
    have hTne : T.Nonempty := ⟨j₀, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj₀⟩⟩
    set i := T.min' hTne with hi
    have hiT : i ∈ T := Finset.min'_mem T hTne
    have hiS : i ∉ S := (Finset.mem_sdiff.mp hiT).2
    have hmin : ∀ j ∈ T, i ≤ j := fun j hj => Finset.min'_le T j hj
    -- all smaller indices are in S
    have hsmall : ∀ j : Fin n, (j : ℕ) < (i : ℕ) → j ∈ S := by
      intro j hj
      by_contra hjS
      have hjT : j ∈ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjS⟩
      have := hmin j hjT
      have : (i : ℕ) ≤ (j : ℕ) := this
      omega
    have hk : (i : ℕ) < n + 1 := by omega
    have hdeg := deg_eq_of_subset n X hXsub (i : ℕ) hk
    rw [← hS] at hdeg
    -- left contribution 0 (i ∉ S)
    have hleft : (S.filter (fun j : Fin n => (j : ℕ) = (i : ℕ))).card = 0 := by
      rw [filter_val_eq_card n S (i : ℕ) i.isLt]
      have : (⟨(i : ℕ), i.isLt⟩ : Fin n) = i := by ext; rfl
      rw [this, if_neg hiS]
    have hpari := hpar ⟨(i : ℕ), hk⟩
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · -- i.val = 0 : vertex 0 ∈ A, right contribution 0, deg = 0, but need odd → contradiction
      have hright : (S.filter (fun j : Fin n => (j : ℕ) + 1 = (i : ℕ))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro j _; omega
      have hdeg0 : (X.filter (fun e => ((⟨(i : ℕ), hk⟩ : Fin (n + 1)) ∈ e))).card = 0 := by
        rw [hdeg, hleft, hright]
      have hv0 : (⟨(i : ℕ), hk⟩ : Fin (n + 1)) = 0 := by ext; rw [h0]; rfl
      rw [hdeg0, if_pos (by rw [hv0]; exact Finset.mem_insert_self _ _)] at hpari
      simp at hpari
    · -- 0 < i.val : right contribution 1, interior vertex, deg = 1 odd, even → contradiction
      have hk1 : (i : ℕ) - 1 < n := by omega
      have hpredS : (⟨(i : ℕ) - 1, hk1⟩ : Fin n) ∈ S :=
        hsmall _ (by simp only []; omega)
      rw [filter_val_succ_card n S (i : ℕ) hk1 h0, if_pos hpredS] at hdeg
      have hdeg1 : (X.filter (fun e => ((⟨(i : ℕ), hk⟩ : Fin (n + 1)) ∈ e))).card = 1 := by
        rw [hdeg, hleft]
      have hvA : (⟨(i : ℕ), hk⟩ : Fin (n + 1)) ∉ ({0, Fin.last n} : Finset (Fin (n + 1))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        · have := congrArg Fin.val h; simp only [Fin.val_zero] at this; omega
        · have := congrArg Fin.val h; simp only [Fin.val_last] at this
          have := i.isLt; omega
      rw [hdeg1, if_neg hvA] at hpari
      simp at hpari
  conv_lhs => rw [image_idx_eq n X hXsub]
  rw [hidxuniv, ← pathGraph_edgeFinset_eq_image]

/-- **Exact open 1D chain two-point function** (Glimm–Jaffe §17.1): the Gibbs
two-point function of the endpoints of the open chain `pathGraph (n+1)` is the exact
geometric `(tanh βJ)ⁿ`,
`correlation (pathGraph (n+1)) ⟨J,0,β⟩ {0, last} = (tanh βJ)ⁿ`.
Via the FV (3.46) high-temperature expansion: the path is a tree, so the even-degree
denominator is `{∅}` (sum `1`) and the `{0,n}`-odd-boundary numerator is the single
full edge set (sum `tanhⁿ`).  Unlike the cyclic chain there is **no boundary
correction**, which makes this the clean finite-volume input to the infinite-volume
limit. -/
theorem correlation_pathGraph_eq_tanh_pow (n : ℕ) (hn : 0 < n) {J β : ℝ} :
    correlation (pathGraph (n + 1)) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({0, Fin.last n} : Finset (Fin (n + 1)))
      = Real.tanh (β * J) ^ n := by
  rw [correlation_high_temp_expansion_h_zero_closed]
  -- the goal's filters use `Fintype.decidableForallFintype`; normalise both to the
  -- fresh `Nat.decidableForallFin` instance so memberships synthesised here unify
  rw [Finset.filter_congr_decidable
        (p := fun X : Finset (Sym2 (Fin (n + 1))) => ∀ v : Fin (n + 1),
          Even ((if v ∈ ({0, Fin.last n} : Finset (Fin (n + 1))) then 1 else 0)
            + (X.filter (v ∈ ·)).card)),
      Finset.filter_congr_decidable
        (p := fun X : Finset (Sym2 (Fin (n + 1))) => ∀ v : Fin (n + 1),
          Even (X.filter (v ∈ ·)).card)]
  rw [Finset.sum_eq_single_of_mem (pathGraph (n + 1)).edgeFinset ?memN ?othN,
      Finset.sum_eq_single_of_mem (∅ : Finset (Sym2 (Fin (n + 1)))) ?memD ?othD,
      card_pathGraph_edgeFinset, Finset.card_empty, pow_zero, div_one]
  -- the numerator collapses to the single full edge set, the denominator to `{∅}`;
  -- membership is discharged against each filter's own `DecidablePred` instance via
  -- the instance-independent parity/uniqueness propositions
  case memN =>
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), edgeFinset_endpoint_parity n hn⟩
  case othN =>
    intro b hb hbne
    rw [Finset.mem_filter] at hb
    exact absurd
      (endpoint_subgraph_eq_edgeFinset n b (Finset.mem_powerset.mp hb.1) hb.2) hbne
  case memD =>
    rw [Finset.mem_filter]
    exact ⟨Finset.empty_mem_powerset _, empty_even_parity n⟩
  case othD =>
    intro b hb hbne
    rw [Finset.mem_filter] at hb
    exact absurd (even_subgraph_eq_empty n b (Finset.mem_powerset.mp hb.1) hb.2) hbne

end TransferMatrix

end IsingModel
