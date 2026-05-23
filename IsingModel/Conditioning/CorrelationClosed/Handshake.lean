import IsingModel.Conditioning.CorrelationClosed.ClosedForm

/-!
# Correlation closed form split — handshake lemma for arbitrary edge subsets

Part of the split `IsingModel.Conditioning.CorrelationClosed` development.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Handshake lemma for arbitrary edge subsets

For `X ⊆ G.edgeFinset` on a `SimpleGraph` (edges non-diagonal),
`∑_v (X.filter (v ∈ ·)).card = 2 · |X|`, the standard handshake
identity. Combined with `Finset.even_sum_iff_even_card_odd`, this
gives that the number of odd `X`-degree vertices is always even —
the parity argument behind the FV (3.46) Z₂ symmetry. -/

/-- **Handshake lemma for arbitrary edge subsets**: for `X ⊆ G.edgeFinset`
on a `SimpleGraph` (so all edges are non-diagonal),
`∑_v (X.filter (v ∈ ·)).card = 2 · |X|`. -/
private theorem sum_filter_card_eq_two_mul_card
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (X : Finset (Sym2 ι)) (hX : X ⊆ G.edgeFinset) :
    ∑ v : ι, (X.filter (v ∈ ·)).card = 2 * X.card := by
  classical
  -- per-v rewrite: card filter = ∑ over X of indicator
  have hper_v : ∀ v : ι,
      (X.filter (v ∈ ·)).card = ∑ e ∈ X, (if v ∈ e then 1 else 0) := by
    intro v
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [hper_v]
  rw [Finset.sum_comm]
  -- inner sum: ∑_v (if v ∈ e then 1 else 0) = e.toFinset.card = 2 (non-diag)
  have hinner : ∀ e ∈ X,
      ∑ v : ι, (if v ∈ e then (1 : ℕ) else 0) = 2 := by
    intros e he
    have heq :
        (∑ v : ι, if v ∈ e then (1 : ℕ) else 0)
          = ((Finset.univ : Finset ι).filter (· ∈ e)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [heq]
    have hf_eq : (Finset.univ : Finset ι).filter (· ∈ e) = e.toFinset := by
      ext v; simp
    rw [hf_eq]
    have hnd : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet
      (G.mem_edgeFinset.mp (hX he))
    exact e.card_toFinset_of_not_isDiag hnd
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  ring

/-- **Even count of odd-degree vertices**: for `X ⊆ G.edgeFinset`,
`Even |{v | Odd (X.filter (v ∈ ·)).card}|`. The number of vertices with
odd `X`-degree is always even. Direct consequence of the handshake
identity `∑_v deg_X v = 2|X|` plus `Finset.even_sum_iff_even_card_odd`. -/
private theorem even_card_odd_filter_card
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (X : Finset (Sym2 ι)) (hX : X ⊆ G.edgeFinset) :
    Even ((Finset.univ : Finset ι).filter
      (fun v => Odd ((X.filter (v ∈ ·)).card))).card := by
  have hsum := sum_filter_card_eq_two_mul_card G X hX
  have h_even : Even (∑ v : ι, (X.filter (v ∈ ·)).card) := by
    rw [hsum]; exact ⟨X.card, by ring⟩
  exact (Finset.even_sum_iff_even_card_odd _).mp h_even

/-- **FV (3.46) numerator filter is empty for odd-cardinality A**:
the filtered powerset
`{X ⊆ G.edgeFinset : ∀ v, Even ((1_A v) + (X.filter (v ∈ ·)).card)}`
is *empty* whenever `|A|` is odd.

Direct consequence of the handshake lemma: for any `X` in this filter,
the condition forces `{v | Odd (deg_X v)} = A`, but the LHS has even
cardinality (handshake), so `|A|` even — contradicting odd `|A|`.

A sharper version of `sum_high_temp_numerator_h_zero_odd_card_eq_zero`
(Step 291): instead of "the sum vanishes", we show "the index set is
empty". Independent of the `correlation_odd_vanish` Z₂-flip argument. -/
theorem high_temp_numerator_filter_eq_empty_of_odd_card
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (hA_odd : Odd A.card) :
    G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro X hX
  rw [Finset.mem_filter, Finset.mem_powerset] at hX
  obtain ⟨hXsub, hcond⟩ := hX
  -- Translate hcond: ∂X = A (set of v with odd X-degree = A)
  have hboundary_eq_A :
      (Finset.univ : Finset ι).filter
          (fun v => Odd ((X.filter (v ∈ ·)).card)) = A := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hodd
      by_contra hvA
      have := hcond v
      rw [if_neg hvA, zero_add] at this
      exact (Nat.not_even_iff_odd.mpr hodd) this
    · intro hvA
      have := hcond v
      rw [if_pos hvA] at this
      rw [show (1 : ℕ) + (X.filter (v ∈ ·)).card
            = (X.filter (v ∈ ·)).card + 1 from Nat.add_comm _ _,
          Nat.even_add_one, Nat.not_even_iff_odd] at this
      exact this
  have h_even := even_card_odd_filter_card G X hXsub
  rw [hboundary_eq_A] at h_even
  exact (Nat.not_even_iff_odd.mpr hA_odd) h_even


end IsingModel
