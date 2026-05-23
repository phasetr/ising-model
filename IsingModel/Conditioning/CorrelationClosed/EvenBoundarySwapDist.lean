import IsingModel.Conditioning.CorrelationClosed.EvenBoundaryBasics

/-!
# Correlation closed form split — even-subgraph pair boundary swap and distance bound

Part of the split `IsingModel.Conditioning.CorrelationClosed` development.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Parity transition for `X.erase s(i, k)` when `∂X = {i, j}`,
`k ∉ {i, j}` (GJ §18.7 foundation)**: under `i ≠ j`, `k ≠ i`, `k ≠ j`,
if `X` is in the FV (3.46) numerator filter for `A = {i, j}` and
`s(i, k) ∈ X`, then `X.erase s(i, k)` is in the FV (3.46) numerator
filter for `A' = {k, j}`.

The boundary "moves" from `{i, j}` to `{k, j}`: erasing the edge
`s(i, k)` flips parity at both endpoints `i` and `k` (Step 570),
turning `i`'s odd degree into even (so `i` leaves the boundary) and
`k`'s even degree into odd (so `k` joins the boundary). The vertex
`j`'s parity is preserved.

The mod-2 identity verified: for every `v`,
`[v ∈ {i, j}] + [v ∈ s(i, k)] ≡ [v ∈ {k, j}] (mod 2)`. -/
theorem evenSubgraph_pair_boundary_erase_swap
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j k : ι) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (X : Finset (Sym2 ι))
    (hX : X ∈ G.edgeFinset.powerset.filter
        (fun X' : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                + (X'.filter (v ∈ ·)).card)))
    (he_in : s(i, k) ∈ X) :
    X.erase s(i, k) ∈ G.edgeFinset.powerset.filter
      (fun X' : Finset (Sym2 ι) => ∀ v : ι,
        Even ((if v ∈ ({k, j} : Finset ι) then (1 : ℕ) else 0)
              + (X'.filter (v ∈ ·)).card)) := by
  classical
  rcases Finset.mem_filter.mp hX with ⟨h_pow, h_par⟩
  refine Finset.mem_filter.mpr ⟨?_, fun v => ?_⟩
  · exact Finset.mem_powerset.mpr
      ((Finset.erase_subset _ _).trans (Finset.mem_powerset.mp h_pow))
  · have h_par_v := h_par v
    have h_step570 := filter_mem_card_erase X (s(i, k)) he_in v
    rw [h_step570] at h_par_v
    -- Both indicators concretely:
    have h_v_in_e_iff : v ∈ (s(i, k) : Sym2 ι) ↔ v = i ∨ v = k := Sym2.mem_iff
    have h_in_ij_iff : v ∈ ({i, j} : Finset ι) ↔ v = i ∨ v = j := by simp
    have h_in_kj_iff : v ∈ ({k, j} : Finset ι) ↔ v = k ∨ v = j := by simp
    -- Compute the indicator parity sum: [v ∈ {i, j}] + [v ∈ s(i, k)] + [v ∈ {k, j}]
    -- has the same parity for all v (always even, by case analysis).
    -- Strategy: express both sides via the "X.erase ...".filter card and
    -- reduce to comparing indicator sums.
    by_cases hvi : v = i
    · -- v = i: indicators (1, 1, 0)
      have h1 : v ∈ ({i, j} : Finset ι) := by rw [hvi]; exact Finset.mem_insert_self _ _
      have h2 : v ∈ (s(i, k) : Sym2 ι) := by rw [hvi]; exact Sym2.mem_mk_left _ _
      have h3 : v ∉ ({k, j} : Finset ι) := by
        intro hv_in
        rw [h_in_kj_iff, hvi] at hv_in
        rcases hv_in with heq | heq
        · exact hki heq.symm
        · exact hij heq
      rw [if_pos h1, if_pos h2] at h_par_v
      rw [if_neg h3]
      -- h_par_v : Even (1 + ((X.erase s(i,k)).filter (v ∈ ·)).card + 1))
      -- Goal: Even (0 + ((X.erase s(i,k)).filter (v ∈ ·)).card)
      have h_eq_orig : (1 : ℕ) + (((X.erase s(i, k)).filter (v ∈ ·)).card + 1) =
          ((X.erase s(i, k)).filter (v ∈ ·)).card + 2 := by ring
      rw [h_eq_orig] at h_par_v
      have h_eq_goal : (0 : ℕ) + ((X.erase s(i, k)).filter (v ∈ ·)).card =
          ((X.erase s(i, k)).filter (v ∈ ·)).card := by ring
      rw [h_eq_goal]
      exact (Nat.even_add.mp h_par_v).mpr (by decide : Even 2)
    · by_cases hvj : v = j
      · -- v = j: indicators (1, 0, 1) — note j ≠ i, j ≠ k so j ∉ s(i, k)
        have h1 : v ∈ ({i, j} : Finset ι) := by rw [hvj]; simp
        have h2 : v ∉ (s(i, k) : Sym2 ι) := by
          intro hv_in
          rw [h_v_in_e_iff, hvj] at hv_in
          rcases hv_in with heq | heq
          · exact hij heq.symm
          · exact hkj heq.symm
        have h3 : v ∈ ({k, j} : Finset ι) := by rw [hvj]; simp
        rw [if_pos h1, if_neg h2] at h_par_v
        rw [if_pos h3]
        -- h_par_v : Even (1 + ((X.erase s(i,k)).filter (v ∈ ·)).card + 0))
        -- Goal: Even (1 + ((X.erase s(i,k)).filter (v ∈ ·)).card)
        simpa using h_par_v
      · by_cases hvk : v = k
        · -- v = k: indicators (0, 1, 1) — k ∉ {i, j}, k ∈ s(i, k), k ∈ {k, j}
          have h1 : v ∉ ({i, j} : Finset ι) := by
            intro hv_in
            rw [h_in_ij_iff, hvk] at hv_in
            rcases hv_in with heq | heq
            · exact hki heq
            · exact hkj heq
          have h2 : v ∈ (s(i, k) : Sym2 ι) := by rw [hvk]; exact Sym2.mem_mk_right _ _
          have h3 : v ∈ ({k, j} : Finset ι) := by rw [hvk]; exact Finset.mem_insert_self _ _
          rw [if_neg h1, if_pos h2] at h_par_v
          rw [if_pos h3]
          -- h_par_v : Even (0 + ((X.erase s(i,k)).filter (v ∈ ·)).card + 1))
          -- Goal: Even (1 + ((X.erase s(i,k)).filter (v ∈ ·)).card)
          have h_eq_orig : (0 : ℕ) + (((X.erase s(i, k)).filter (v ∈ ·)).card + 1) =
              ((X.erase s(i, k)).filter (v ∈ ·)).card + 1 := by ring
          have h_eq_goal : (1 : ℕ) + ((X.erase s(i, k)).filter (v ∈ ·)).card =
              ((X.erase s(i, k)).filter (v ∈ ·)).card + 1 := by ring
          rw [h_eq_orig] at h_par_v
          rw [h_eq_goal]
          exact h_par_v
        · -- v ∉ {i, j, k}: indicators (0, 0, 0)
          have h1 : v ∉ ({i, j} : Finset ι) := by
            intro hv_in
            rw [h_in_ij_iff] at hv_in
            rcases hv_in with heq | heq
            · exact hvi heq
            · exact hvj heq
          have h2 : v ∉ (s(i, k) : Sym2 ι) := by
            intro hv_in
            rw [h_v_in_e_iff] at hv_in
            rcases hv_in with heq | heq
            · exact hvi heq
            · exact hvk heq
          have h3 : v ∉ ({k, j} : Finset ι) := by
            intro hv_in
            rw [h_in_kj_iff] at hv_in
            rcases hv_in with heq | heq
            · exact hvk heq
            · exact hvj heq
          rw [if_neg h1, if_neg h2] at h_par_v
          rw [if_neg h3]
          simpa using h_par_v

/-- **Pair-boundary graph-distance bound (GJ §18.7 capstone, key step)**:
under `∂X = {i, j}` (i.e. `X` is in the FV (3.46) numerator filter for
`A = {i, j}`), the graph distance satisfies `G.dist i j ≤ X.card`.

Strong induction on `X.card`, building an explicit walk:
- `i = j`: walk = `nil`, length `0 ≤ X.card` (and `dist_self = 0`).
- `i ≠ j`, `X.card ≥ 1` (Step 567): pick `e = s(i, k) ∈ X` (Step 569),
  giving `G.Adj i k` (since `e ∈ G.edgeFinset`).
  - `k = j`: walk = `cons hadj nil`, length `1 ≤ X.card`.
  - `k ≠ j`: erase `e`. Parity transition (Step 572) gives
    `∂(X.erase e) = {k, j}`. IH on `X.erase e` (with
    `(X.erase e).card < X.card`) yields a walk `k → j` of length
    `≤ X.card - 1`. Prepend the `i → k` edge to get a walk `i → j` of
    length `≤ X.card`.

Combined with Step 568 (numerator counting via `tanh(β·J)^|X|`) and a
`tanh(β·J)^k ≤ tanh(β·J)^{d_G(i,j)}` reduction (using `|X| ≥ d_G(i, j)`
shown here), gives the §18.7 capstone exponential decay
`⟨σ_iσ_j⟩ ≤ ... · tanh(β·J)^{d_G(i,j)}` at high temperature. -/
theorem evenSubgraph_pair_boundary_dist_le
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι)
    (X : Finset (Sym2 ι))
    (hX : X ∈ G.edgeFinset.powerset.filter
        (fun X' : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                + (X'.filter (v ∈ ·)).card))) :
    G.dist i j ≤ X.card := by
  classical
  -- Reduce to constructing a walk of bounded length, then apply dist_le.
  suffices h : ∀ (n : ℕ) (i' j' : ι) (X' : Finset (Sym2 ι)),
      i' ≠ j' → X'.card = n →
      X' ∈ G.edgeFinset.powerset.filter
          (fun X'' : Finset (Sym2 ι) => ∀ v : ι,
            Even ((if v ∈ ({i', j'} : Finset ι) then (1 : ℕ) else 0)
                  + (X''.filter (v ∈ ·)).card)) →
      ∃ p : G.Walk i' j', p.length ≤ X'.card by
    by_cases hij : i = j
    · subst hij
      rw [G.dist_self]
      exact Nat.zero_le _
    · obtain ⟨p, hp⟩ := h X.card i j X hij rfl hX
      exact (G.dist_le p).trans hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i' j' X' hij' hcard hX'
    have h_card_pos : 1 ≤ X'.card := evenSubgraph_pair_boundary_card_pos G i' j' X' hX'
    -- Pick edge incident to i' (Step 569)
    obtain ⟨e, he_in, hi_in⟩ :=
      evenSubgraph_pair_boundary_exists_edge_incident_to G i' j' X' hX'
    -- Other endpoint k via Sym2.Mem.other
    have he_eq : s(i', Sym2.Mem.other hi_in) = e := Sym2.other_spec hi_in
    have hX_sub : X' ⊆ G.edgeFinset :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hX').1
    have he_in_G : e ∈ G.edgeFinset := hX_sub he_in
    have he_in_edgeSet : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp he_in_G
    have he_not_diag : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet he_in_edgeSet
    have hk_ne_i : Sym2.Mem.other hi_in ≠ i' := Sym2.other_ne he_not_diag hi_in
    -- G.Adj i' k from e = s(i', k) ∈ G.edgeSet
    have hadj_ik : G.Adj i' (Sym2.Mem.other hi_in) := by
      have h_in : s(i', Sym2.Mem.other hi_in) ∈ G.edgeSet := he_eq.symm ▸ he_in_edgeSet
      rwa [SimpleGraph.mem_edgeSet] at h_in
    -- Case: k = j' or k ≠ j'
    by_cases hk_eq : Sym2.Mem.other hi_in = j'
    · -- k = j': single-edge walk of length 1
      have hadj_ij : G.Adj i' j' := hk_eq ▸ hadj_ik
      refine ⟨SimpleGraph.Walk.cons hadj_ij SimpleGraph.Walk.nil, ?_⟩
      rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
      -- goal: 0 + 1 ≤ X'.card
      omega
    · -- k ≠ j': erase e, recurse via parity transition (Step 572)
      have h_erase_card : (X'.erase e).card = n - 1 := by
        rw [Finset.card_erase_of_mem he_in, hcard]
      have h_erase_lt : (X'.erase e).card < n := by
        rw [h_erase_card]; omega
      -- Convert e back to s(i', k) for Step 572 application
      have he_actual : e = s(i', Sym2.Mem.other hi_in) := he_eq.symm
      have he_in' : s(i', Sym2.Mem.other hi_in) ∈ X' := he_actual ▸ he_in
      have hX_swap : X'.erase s(i', Sym2.Mem.other hi_in) ∈
          G.edgeFinset.powerset.filter
            (fun X'' : Finset (Sym2 ι) => ∀ v : ι,
              Even ((if v ∈ ({Sym2.Mem.other hi_in, j'} : Finset ι) then (1 : ℕ) else 0)
                    + (X''.filter (v ∈ ·)).card)) :=
        evenSubgraph_pair_boundary_erase_swap G i' j' (Sym2.Mem.other hi_in)
          hij' hk_ne_i hk_eq X' hX' he_in'
      -- Convert the erase to use e
      have hX_swap' : (X'.erase e) ∈ G.edgeFinset.powerset.filter
          (fun X'' : Finset (Sym2 ι) => ∀ v : ι,
            Even ((if v ∈ ({Sym2.Mem.other hi_in, j'} : Finset ι) then (1 : ℕ) else 0)
                  + (X''.filter (v ∈ ·)).card)) := by
        rwa [← he_actual] at hX_swap
      -- Apply IH
      obtain ⟨p_kj, hp_kj⟩ := ih (X'.erase e).card h_erase_lt
        (Sym2.Mem.other hi_in) j' (X'.erase e) hk_eq rfl hX_swap'
      -- Build walk i' → j' as cons (i' → k) (k → j')
      refine ⟨SimpleGraph.Walk.cons hadj_ik p_kj, ?_⟩
      rw [SimpleGraph.Walk.length_cons, h_erase_card] at *
      omega


end IsingModel
