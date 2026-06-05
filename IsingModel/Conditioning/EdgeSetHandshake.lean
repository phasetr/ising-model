import IsingModel.Conditioning.EdgeSetDistance
import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# Handshake parity for edge sets and the second odd-degree vertex

The handshake lemma for edge subsets and its parity consequence: a vertex of odd degree in
an edge set is accompanied by a second one. Combined with the distance bound
(`EdgeSetDistance.lean`), this shows the origin's component must reach a second odd-degree
vertex, the FV §3.7.3 contour-reaches-boundary mechanism towards `m*(β)=0` (Issue #3613).

* `sum_filter_card_eq_two_mul_card` — `∑_v deg_X(v) = 2|X|`.
* `exists_ne_odd_filter_card` — odd degree at `z` forces a second odd-degree vertex.
* `exists_dist_le_card_componentOfZero` — the origin component reaches a second
  odd-degree vertex within distance `|C|`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, eqs. (3.48)–(3.49), pp. 117–118.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- **Handshake lemma for edge subsets**: for `X ⊆ G.edgeFinset` (so all edges are
non-diagonal), `∑_v (X.filter (v ∈ ·)).card = 2·|X|` (the sum of degrees is twice the
edge count). -/
theorem sum_filter_card_eq_two_mul_card [Fintype ι] (G : SimpleGraph ι) [Fintype G.edgeSet]
    (X : Finset (Sym2 ι)) (hX : X ⊆ G.edgeFinset) :
    ∑ v : ι, (X.filter (v ∈ ·)).card = 2 * X.card := by
  classical
  have hper_v : ∀ v : ι,
      (X.filter (v ∈ ·)).card = ∑ e ∈ X, (if v ∈ e then 1 else 0) := by
    intro v
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [hper_v]
  rw [Finset.sum_comm]
  have hinner : ∀ e ∈ X, ∑ v : ι, (if v ∈ e then (1 : ℕ) else 0) = 2 := by
    intro e he
    have heq : (∑ v : ι, if v ∈ e then (1 : ℕ) else 0)
        = ((Finset.univ : Finset ι).filter (· ∈ e)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [heq]
    have hf_eq : (Finset.univ : Finset ι).filter (· ∈ e) = e.toFinset := by
      ext v; simp
    rw [hf_eq]
    exact e.card_toFinset_of_not_isDiag
      (G.not_isDiag_of_mem_edgeSet (G.mem_edgeFinset.mp (hX he)))
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  ring

/-- **The set of odd-degree vertices has even cardinality**: from the handshake identity
`∑_v deg_X(v) = 2|X|` and `Finset.even_sum_iff_even_card_odd`. -/
theorem even_card_odd_filter_card [Fintype ι] (G : SimpleGraph ι) [Fintype G.edgeSet]
    (X : Finset (Sym2 ι)) (hX : X ⊆ G.edgeFinset) :
    Even ((Finset.univ.filter (fun v => Odd ((X.filter (v ∈ ·)).card))).card) := by
  have hsum := sum_filter_card_eq_two_mul_card G X hX
  have h_even : Even (∑ v : ι, (X.filter (v ∈ ·)).card) := by rw [hsum]; exact ⟨X.card, by ring⟩
  exact (Finset.even_sum_iff_even_card_odd _).mp h_even

/-- **A second odd-degree vertex**: if `X ⊆ G.edgeFinset` has odd degree at `z`, then some
other vertex `j ≠ z` also has odd degree in `X`. (The odd-degree set has even cardinality
and contains `z`, so it is not the singleton `{z}`.) -/
theorem exists_ne_odd_filter_card [Finite ι] (G : SimpleGraph ι) [Fintype G.edgeSet]
    (X : Finset (Sym2 ι)) (hX : X ⊆ G.edgeFinset) {z : ι}
    (hz : Odd ((X.filter (z ∈ ·)).card)) :
    ∃ j, j ≠ z ∧ Odd ((X.filter (j ∈ ·)).card) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  set S := Finset.univ.filter (fun v => Odd ((X.filter (v ∈ ·)).card)) with hS
  have hzS : z ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩
  have heven := even_card_odd_filter_card G X hX
  have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨z, hzS⟩
  have hne1 : S.card ≠ 1 := fun h =>
    (Nat.not_even_iff_odd.mpr odd_one) (h ▸ heven)
  have h1lt : 1 < S.card := lt_of_le_of_ne hpos (Ne.symm hne1)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1lt
  rw [hS, Finset.mem_filter] at ha hb
  rcases eq_or_ne a z with rfl | haz
  · exact ⟨b, Ne.symm hab, hb.2⟩
  · exact ⟨a, haz, ha.2⟩

/-- **The origin component reaches a second odd-degree vertex** (FV §3.7.3 toward (3.49)):
if `X ⊆ G.edgeFinset` has an edge at `z` and the origin component has odd degree at `z`,
then there is a vertex `j ≠ z` with `G.dist z j ≤ |componentOfZero X z|`. The contour from
the origin reaches a second odd-degree site, which in the cubic-box `+` setup is a boundary
site at distance `≥ n`. -/
theorem exists_dist_le_card_componentOfZero [Finite ι] (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} (hXG : X ⊆ G.edgeFinset) {z : ι} {e₀ : Sym2 ι}
    (he₀ : e₀ ∈ X) (hz : z ∈ e₀)
    (hzodd : Odd (((componentOfZero X z).filter (z ∈ ·)).card)) :
    ∃ j, j ≠ z ∧ G.dist z j ≤ (componentOfZero X z).card := by
  classical
  have hCG : componentOfZero X z ⊆ G.edgeFinset := (componentOfZero_subset X z).trans hXG
  obtain ⟨j, hjz, hjodd⟩ := exists_ne_odd_filter_card G (componentOfZero X z) hCG hzodd
  obtain ⟨ev, hev⟩ := Finset.card_pos.mp hjodd.pos
  rw [Finset.mem_filter] at hev
  exact ⟨j, hjz, dist_le_card_componentOfZero G hXG he₀ hz hev.1 hev.2⟩

end IsingModel
