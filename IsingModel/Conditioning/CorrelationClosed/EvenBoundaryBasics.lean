import IsingModel.Conditioning.CorrelationClosed.Z2Symmetry

/-!
# Correlation closed form split — even-subgraph pair boundary basics

Part of the split `IsingModel.Conditioning.CorrelationClosed` development.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Pair numerator filter forces `1 ≤ |X|` (GJ §18.7 foundation)**:
for any `i j : ι`, every `X` in the FV (3.46) numerator filter for
`A = {i, j}` satisfies `1 ≤ X.card`.

The empty subgraph cannot occur: at `v = i` (which lies in `A = {i, j}`),
the constraint `Even (1 + (X.filter (i ∈ ·)).card)` forces
`(X.filter (i ∈ ·)).card` to be **odd**; if `X = ∅` this would give
`(X.filter (i ∈ ·)).card = 0`, even, and `1 + 0 = 1` is *not* even —
contradiction.

Note that `i ≠ j` is *not* needed: when `i = j`, `A = {i}` and the same
parity argument at `v = i` excludes `X = ∅`.

Building block toward the §18.7 capstone graph-distance bound
`d_G(i, j) ≤ X.card`. -/
theorem evenSubgraph_pair_boundary_card_pos
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι)
    (X : Finset (Sym2 ι))
    (hX : X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card))) :
    1 ≤ X.card := by
  rcases Finset.mem_filter.mp hX with ⟨_, hparity⟩
  rcases Nat.eq_zero_or_pos X.card with h | h
  · exfalso
    have hX_empty : X = ∅ := Finset.card_eq_zero.mp h
    have h_at_i := hparity i
    have hi_mem : i ∈ ({i, j} : Finset ι) := Finset.mem_insert_self i {j}
    rw [hX_empty] at h_at_i
    simp [hi_mem] at h_at_i
  · exact h

omit [Fintype ι] in
/-- **Erase-edge filter card transition (GJ §18.7 foundation)**:
for `X : Finset (Sym2 ι)`, `e ∈ X`, and any vertex `v`,
\[
|\{X' \in X \mid v \in X'\}|
  = |\{X' \in X.\mathrm{erase}\,e \mid v \in X'\}|
    + [v \in e],
\]
i.e., erasing `e` decreases the per-vertex filter card by `1` exactly
when `v` is incident to `e`, and leaves it unchanged otherwise.

Encodes the parity-flip behaviour `∂(X.erase e) = ∂X △ e` underlying
the inductive proof of `d_G(i, j) ≤ |X|` (planned Step 571+).

Proof: combine `Finset.filter_erase` (filter and erase commute) with
case analysis on whether `v ∈ e`. -/
theorem filter_mem_card_erase
    (X : Finset (Sym2 ι)) (e : Sym2 ι) (hX : e ∈ X) (v : ι) :
    (X.filter (v ∈ ·)).card =
      ((X.erase e).filter (v ∈ ·)).card + (if v ∈ e then 1 else 0) := by
  classical
  rw [Finset.filter_erase]
  by_cases hv : v ∈ e
  · have h_e_in_filter : e ∈ X.filter (v ∈ ·) :=
      Finset.mem_filter.mpr ⟨hX, hv⟩
    rw [Finset.card_erase_of_mem h_e_in_filter, if_pos hv]
    have h_pos : 0 < (X.filter (v ∈ ·)).card := Finset.card_pos.mpr ⟨e, h_e_in_filter⟩
    omega
  · have h_e_notin_filter : e ∉ X.filter (v ∈ ·) := by
      intro h_in
      exact hv (Finset.mem_filter.mp h_in).2
    rw [Finset.erase_eq_of_notMem h_e_notin_filter, if_neg hv, Nat.add_zero]

/-- **Pair-boundary numerator: `i` is incident to some edge in `X`
(GJ §18.7 foundation)**: for any `X` in the FV (3.46) numerator filter
for `A = {i, j}`, there exists an edge `e ∈ X` with `i ∈ e`.

Direct from the parity constraint at `v = i`: since `i ∈ A`, we get
`Even (1 + (X.filter (i ∈ ·)).card)`, forcing the filter card to be
**odd**, hence `≥ 1`, hence non-empty.

Building block toward the §18.7 graph-distance lower bound
`d_G(i, j) ≤ X.card` via induction on `X.card`. -/
theorem evenSubgraph_pair_boundary_exists_edge_incident_to
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι)
    (X : Finset (Sym2 ι))
    (hX : X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card))) :
    ∃ e ∈ X, i ∈ e := by
  rcases Finset.mem_filter.mp hX with ⟨_, hparity⟩
  have h_at_i := hparity i
  have hi_mem : i ∈ ({i, j} : Finset ι) := Finset.mem_insert_self i {j}
  rw [if_pos hi_mem] at h_at_i
  -- h_at_i : Even (1 + (X.filter (i ∈ ·)).card)
  -- Hence (X.filter (i ∈ ·)).card is odd, hence ≥ 1
  have h_filter_card_pos : 0 < (X.filter (i ∈ ·)).card := by
    rcases Nat.eq_zero_or_pos (X.filter (i ∈ ·)).card with h_zero | h_pos
    · exfalso
      rw [h_zero] at h_at_i
      simp at h_at_i
    · exact h_pos
  -- Filter is non-empty, pick any element
  obtain ⟨e, he⟩ := Finset.card_pos.mp h_filter_card_pos
  rcases Finset.mem_filter.mp he with ⟨he_in_X, he_contains_i⟩
  exact ⟨e, he_in_X, he_contains_i⟩

/-- **Card-1 case of pair-boundary numerator: `X = {s(i,j)}` and
`G.Adj i j` (GJ §18.7 foundation)**: if `i ≠ j`, `X.card = 1`, and `X`
is in the FV (3.46) numerator filter for `A = {i, j}`, then
`X = {s(i, j)}` and `i, j` are adjacent in `G`.

Establishes the base case for the inductive `d_G(i, j) ≤ X.card`
proof: when `X.card = 1`, the unique edge in `X` connects `i` and `j`
directly, so the graph distance is `≤ 1 = X.card`.

Proof: from Step 569 applied to both `i` and `j` (using
symmetry of `A = {i, j}` for the second invocation), the unique edge
in `X` must contain both `i` and `j`. Since `i ≠ j`, this edge is
exactly `s(i, j)`. Membership in `G.edgeFinset` gives `G.Adj i j`. -/
theorem evenSubgraph_pair_boundary_card_one_adj
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι) (hij : i ≠ j)
    (X : Finset (Sym2 ι))
    (hX : X ∈ G.edgeFinset.powerset.filter
        (fun X' : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                + (X'.filter (v ∈ ·)).card)))
    (hcard : X.card = 1) :
    X = {s(i, j)} ∧ G.Adj i j := by
  classical
  obtain ⟨e, hX_eq⟩ := Finset.card_eq_one.mp hcard
  -- Step 569 at (i, j): ∃ e' ∈ X, i ∈ e'. With X = {e}, e' = e, so i ∈ e.
  obtain ⟨e_i, he_i, hi_in⟩ :=
    evenSubgraph_pair_boundary_exists_edge_incident_to G i j X hX
  rw [hX_eq, Finset.mem_singleton] at he_i
  rw [he_i] at hi_in
  -- Symmetry: A = {i, j} = {j, i}, so we can apply Step 569 with (j, i).
  have hX_swap : X ∈ G.edgeFinset.powerset.filter
      (fun X' : Finset (Sym2 ι) => ∀ v : ι,
        Even ((if v ∈ ({j, i} : Finset ι) then (1 : ℕ) else 0)
              + (X'.filter (v ∈ ·)).card)) := by
    have h_set_eq : ({j, i} : Finset ι) = ({i, j} : Finset ι) := by
      ext x; simp [or_comm]
    rw [h_set_eq]; exact hX
  obtain ⟨e_j, he_j, hj_in⟩ :=
    evenSubgraph_pair_boundary_exists_edge_incident_to G j i X hX_swap
  rw [hX_eq, Finset.mem_singleton] at he_j
  rw [he_j] at hj_in
  -- e contains both i and j; since i ≠ j, e = s(i, j)
  have he_eq : e = s(i, j) := by
    induction e using Sym2.ind with
    | _ a b =>
      rcases Sym2.mem_iff.mp hi_in with hi_eq | hi_eq
      · subst hi_eq
        rcases Sym2.mem_iff.mp hj_in with hj_eq | hj_eq
        · exact absurd hj_eq.symm hij
        · subst hj_eq; rfl
      · subst hi_eq
        rcases Sym2.mem_iff.mp hj_in with hj_eq | hj_eq
        · subst hj_eq; exact Sym2.eq_swap
        · exact absurd hj_eq.symm hij
  -- X ⊆ G.edgeFinset gives e ∈ G.edgeFinset, so G.Adj i j
  have hX_sub : X ⊆ G.edgeFinset :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hX).1
  rw [hX_eq] at hX_sub
  have he_in_G : e ∈ G.edgeFinset := hX_sub (Finset.mem_singleton_self _)
  rw [he_eq, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he_in_G
  refine ⟨?_, he_in_G⟩
  rw [hX_eq, he_eq]


end IsingModel
