import IsingModel.TransferMatrix.PathGraphTwoPoint

/-!
# General-pair open 1D chain two-point function `⟨σₐσᵦ⟩ = (tanh βJ)^|a-b|` (GJ §17.1)

Generalises the endpoint open-chain two-point function (#3533) to an arbitrary
distinct pair `{a, b}` of vertices of `pathGraph (m+1)`:

  `correlation (pathGraph (m+1)) ⟨J,0,β⟩ {a, b} = (tanh βJ)^(|a.val - b.val|)`.

Via the FV (3.46) high-temperature closed form: the even-degree denominator is
still `{∅}` (the path is a tree), and the `{a,b}`-odd-boundary numerator is the
single **segment** subgraph `{edges i : a.val ≤ i < b.val}` (the path connecting
`a` to `b`), of cardinality `b.val - a.val`.  The segment characterisation is the
discrete-derivative parity recurrence `deg(k) = [edge (k-1) ∈ S] + [edge k ∈ S]`.

This is the input to the infinite-volume lift (Issue #3532): under the box≅path
relabelling the lattice endpoints `{0, r}` map to interior path vertices.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators
open SimpleGraph Finset

/-- The **segment index set** `{i : Fin m | a ≤ i.val < b}`: the edges of the path
connecting the vertices at positions `a` and `b`. -/
def segmentIdx (m a b : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i : Fin m => a ≤ (i : ℕ) ∧ (i : ℕ) < b)

@[simp] theorem mem_segmentIdx {m a b : ℕ} (i : Fin m) :
    i ∈ segmentIdx m a b ↔ a ≤ (i : ℕ) ∧ (i : ℕ) < b := by
  simp [segmentIdx]

/-- The segment `{a ≤ i < b}` (with `b ≤ m`, `a ≤ b`) has cardinality `b - a`. -/
theorem card_segmentIdx (m a b : ℕ) (hb : b ≤ m) :
    (segmentIdx m a b).card = b - a := by
  classical
  rw [← Nat.card_Ico a b]
  refine Finset.card_bij' (fun i _ => (i : ℕ)) (fun k hk => ⟨k, by
      rw [Finset.mem_Ico] at hk; omega⟩) ?_ ?_ ?_ ?_
  · intro i hi
    rw [mem_segmentIdx] at hi
    rw [Finset.mem_Ico]; exact hi
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [mem_segmentIdx]; exact hk
  · intro i _; rfl
  · intro k _; rfl

/-- **Segment characterisation of the `{a,b}`-odd-boundary subgraph** (GJ §17.1): an
edge subset `X` of `pathGraph (m+1)` with odd degree exactly at the two vertices
`a`, `b` (`a.val < b.val`, even elsewhere) has index set the segment
`{i : a.val ≤ i < b.val}`.  Proved by the discrete-derivative parity recurrence
`deg(vertex k) = [edge (k-1) ∈ S] + [edge k ∈ S]` via strong induction on `k`. -/
theorem idx_eq_segmentIdx (m : ℕ) (X : Finset (Sym2 (Fin (m + 1))))
    (a b : Fin (m + 1)) (hab : (a : ℕ) < (b : ℕ))
    (hXsub : X ⊆ (pathGraph (m + 1)).edgeFinset)
    (hpar : ∀ v : Fin (m + 1),
      Even ((if v ∈ ({a, b} : Finset (Fin (m + 1))) then 1 else 0)
        + (X.filter (v ∈ ·)).card)) :
    idx m X = segmentIdx m (a : ℕ) (b : ℕ) := by
  classical
  set S := idx m X with hS
  have key : ∀ k, (hk : k < m) →
      ((⟨k, hk⟩ : Fin m) ∈ S ↔ (a : ℕ) ≤ k ∧ k < (b : ℕ)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IH =>
      intro hk
      have hkV : k < m + 1 := by omega
      have hbdy : ((⟨k, hkV⟩ : Fin (m + 1)) ∈ ({a, b} : Finset (Fin (m + 1))))
          ↔ (k = (a : ℕ) ∨ k = (b : ℕ)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      have hdeg := deg_eq_of_subset m X hXsub k hkV
      rw [← hS, filter_val_eq_card m S k hk] at hdeg
      have hpark := hpar ⟨k, hkV⟩
      rw [hdeg] at hpark
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · -- base: k = 0, no predecessor edge
        subst hk0
        rw [filter_val_succ_zero_card, Nat.even_iff] at hpark
        by_cases hmemS : (⟨0, hk⟩ : Fin m) ∈ S <;>
          by_cases hbk : (⟨0, hkV⟩ : Fin (m + 1)) ∈ ({a, b} : Finset (Fin (m + 1))) <;>
          simp only [hmemS, hbk, if_true, if_false, true_iff, false_iff, not_and,
            not_lt] at hpark ⊢ <;>
          rw [hbdy] at hbk <;> omega
      · -- step: k ≥ 1, use IH at k-1
        have hk1 : k - 1 < m := by omega
        rw [filter_val_succ_card m S k hk1 hk0, Nat.even_iff] at hpark
        have hIH := IH (k - 1) (by omega) hk1
        by_cases hmemS : (⟨k, hk⟩ : Fin m) ∈ S <;>
          by_cases hpredS : (⟨k - 1, hk1⟩ : Fin m) ∈ S <;>
          by_cases hbk : (⟨k, hkV⟩ : Fin (m + 1)) ∈ ({a, b} : Finset (Fin (m + 1))) <;>
          simp only [hmemS, hpredS, hbk, if_true, if_false, true_iff, false_iff,
            not_and, not_lt] at hpark hIH ⊢ <;>
          rw [hbdy] at hbk <;> omega
  ext i
  rw [mem_segmentIdx]
  have := key i.val i.isLt
  simpa using this

/-- **The segment subgraph has odd degree exactly at `a`, `b`** (GJ §17.1): the
segment `{a.val ≤ i < b.val}` (`a.val < b.val`) has degree `1` at the two endpoints
`a`, `b`, degree `2` in the interior, and `0` outside — matching the
`{a,b}`-odd-boundary parity. -/
theorem segment_parity (m : ℕ) (a b : Fin (m + 1)) (hab : (a : ℕ) < (b : ℕ)) :
    ∀ v : Fin (m + 1),
      Even ((if v ∈ ({a, b} : Finset (Fin (m + 1))) then 1 else 0)
        + (((segmentIdx m (a : ℕ) (b : ℕ)).image
            (fun i : Fin m => s(i.castSucc, i.succ))).filter (v ∈ ·)).card) := by
  classical
  intro v
  have hv : (⟨(v : ℕ), v.isLt⟩ : Fin (m + 1)) = v := by ext; rfl
  rw [← hv, incident_filter_card m (segmentIdx m (a : ℕ) (b : ℕ)) (v : ℕ) v.isLt]
  set S := segmentIdx m (a : ℕ) (b : ℕ) with hSdef
  have hbdy : ((⟨(v : ℕ), v.isLt⟩ : Fin (m + 1)) ∈ ({a, b} : Finset (Fin (m + 1))))
      ↔ ((v : ℕ) = (a : ℕ) ∨ (v : ℕ) = (b : ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  -- left index contribution `#{i ∈ S : i.val = v.val}`
  have hL : (S.filter (fun i : Fin m => (i : ℕ) = (v : ℕ))).card
      = if (a : ℕ) ≤ (v : ℕ) ∧ (v : ℕ) < (b : ℕ) ∧ (v : ℕ) < m then 1 else 0 := by
    by_cases hvm : (v : ℕ) < m
    · rw [filter_val_eq_card m S (v : ℕ) hvm]
      have hiff : (⟨(v : ℕ), hvm⟩ : Fin m) ∈ S ↔ (a : ℕ) ≤ (v : ℕ) ∧ (v : ℕ) < (b : ℕ) := by
        rw [hSdef, mem_segmentIdx]
      by_cases hmem : (⟨(v : ℕ), hvm⟩ : Fin m) ∈ S
      · rw [if_pos hmem]; rw [hiff] at hmem; rw [if_pos (by omega)]
      · rw [if_neg hmem]; rw [hiff] at hmem; rw [if_neg (by omega)]
    · have hempty : S.filter (fun i : Fin m => (i : ℕ) = (v : ℕ)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro i _; have := i.isLt; omega
      rw [hempty, Finset.card_empty, if_neg (by omega)]
  -- right index contribution `#{i ∈ S : i.val + 1 = v.val}`
  have hR : (S.filter (fun i : Fin m => (i : ℕ) + 1 = (v : ℕ))).card
      = if 1 ≤ (v : ℕ) ∧ (a : ℕ) ≤ (v : ℕ) - 1 ∧ (v : ℕ) - 1 < (b : ℕ) then 1 else 0 := by
    rcases Nat.eq_zero_or_pos (v : ℕ) with hv0 | hv0
    · rw [hv0, filter_val_succ_zero_card, if_neg (by omega)]
    · have hk1 : (v : ℕ) - 1 < m := by omega
      rw [filter_val_succ_card m S (v : ℕ) hk1 hv0]
      have hiff : (⟨(v : ℕ) - 1, hk1⟩ : Fin m) ∈ S
          ↔ (a : ℕ) ≤ (v : ℕ) - 1 ∧ (v : ℕ) - 1 < (b : ℕ) := by
        rw [hSdef, mem_segmentIdx]
      by_cases hmem : (⟨(v : ℕ) - 1, hk1⟩ : Fin m) ∈ S
      · rw [if_pos hmem]; rw [hiff] at hmem; rw [if_pos (by omega)]
      · rw [if_neg hmem]; rw [hiff] at hmem; rw [if_neg (by omega)]
  rw [hL, hR, Nat.even_iff]
  have hbk : (if (⟨(v : ℕ), v.isLt⟩ : Fin (m + 1)) ∈ ({a, b} : Finset (Fin (m + 1)))
      then (1 : ℕ) else 0) = if (v : ℕ) = (a : ℕ) ∨ (v : ℕ) = (b : ℕ) then 1 else 0 := by
    by_cases h : (⟨(v : ℕ), v.isLt⟩ : Fin (m + 1)) ∈ ({a, b} : Finset (Fin (m + 1)))
    · rw [if_pos h]; rw [hbdy] at h; rw [if_pos h]
    · rw [if_neg h]; rw [hbdy] at h; rw [if_neg h]
  rw [hbk]
  split_ifs <;> omega

/-- The `pathPair`-image of the segment has cardinality `b.val - a.val`. -/
theorem card_segment_image (m : ℕ) (a b : Fin (m + 1)) :
    ((segmentIdx m (a : ℕ) (b : ℕ)).image
        (fun i : Fin m => s(i.castSucc, i.succ))).card = (b : ℕ) - (a : ℕ) := by
  rw [Finset.card_image_of_injective _ (pathPair_injective m), card_segmentIdx]
  exact Nat.lt_succ_iff.mp b.isLt

/-- **Exact open 1D chain two-point function, ordered pair** (Glimm–Jaffe §17.1): for
`a.val < b.val`, `correlation (pathGraph (m+1)) ⟨J,0,β⟩ {a, b} = (tanh βJ)^(b.val - a.val)`.
Via the FV (3.46) closed form: the even denominator collapses to `{∅}` and the
`{a,b}`-odd-boundary numerator to the single segment subgraph `{a.val ≤ i < b.val}`. -/
theorem correlation_pathGraph_pair_eq_tanh_pow_of_lt (m : ℕ) (a b : Fin (m + 1))
    (hab : (a : ℕ) < (b : ℕ)) {J β : ℝ} :
    correlation (pathGraph (m + 1)) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({a, b} : Finset (Fin (m + 1)))
      = Real.tanh (β * J) ^ ((b : ℕ) - (a : ℕ)) := by
  classical
  rw [correlation_high_temp_expansion_h_zero_closed]
  -- normalise the `DecidablePred` instances so the membership lemmas unify
  rw [Finset.filter_congr_decidable
        (p := fun X : Finset (Sym2 (Fin (m + 1))) => ∀ v : Fin (m + 1),
          Even ((if v ∈ ({a, b} : Finset (Fin (m + 1))) then 1 else 0)
            + (X.filter (v ∈ ·)).card)),
      Finset.filter_congr_decidable
        (p := fun X : Finset (Sym2 (Fin (m + 1))) => ∀ v : Fin (m + 1),
          Even (X.filter (v ∈ ·)).card)]
  rw [Finset.sum_eq_single_of_mem
        ((segmentIdx m (a : ℕ) (b : ℕ)).image (fun i : Fin m => s(i.castSucc, i.succ)))
        ?memN ?othN,
      Finset.sum_eq_single_of_mem (∅ : Finset (Sym2 (Fin (m + 1)))) ?memD ?othD,
      card_segment_image, Finset.card_empty, pow_zero, div_one]
  case memN =>
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr ?_, segment_parity m a b hab⟩
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨i, _, rfl⟩ := he
    rw [pathGraph_edgeFinset_eq_image, Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, rfl⟩
  case othN =>
    intro X hX hXne
    rw [Finset.mem_filter] at hX
    refine absurd ?_ hXne
    rw [image_idx_eq m X (Finset.mem_powerset.mp hX.1),
      idx_eq_segmentIdx m X a b hab (Finset.mem_powerset.mp hX.1) hX.2]
  case memD =>
    rw [Finset.mem_filter]
    exact ⟨Finset.empty_mem_powerset _, empty_even_parity m⟩
  case othD =>
    intro X hX hXne
    rw [Finset.mem_filter] at hX
    exact absurd (even_subgraph_eq_empty m X (Finset.mem_powerset.mp hX.1) hX.2) hXne

/-- **Exact open 1D chain two-point function, general distinct pair**
(Glimm–Jaffe §17.1): for `a ≠ b`,
`correlation (pathGraph (m+1)) ⟨J,0,β⟩ {a, b} = (tanh βJ)^|a.val - b.val|`,
the exact geometric decay in the path distance between the two sites. -/
theorem correlation_pathGraph_pair_eq_tanh_pow (m : ℕ) (a b : Fin (m + 1))
    (hab : a ≠ b) {J β : ℝ} :
    correlation (pathGraph (m + 1)) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({a, b} : Finset (Fin (m + 1)))
      = Real.tanh (β * J) ^ ((a : ℕ) - (b : ℕ) + ((b : ℕ) - (a : ℕ))) := by
  have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
  rcases Nat.lt_or_ge (a : ℕ) (b : ℕ) with h | h
  · rw [correlation_pathGraph_pair_eq_tanh_pow_of_lt m a b h]
    congr 1; omega
  · have h' : (b : ℕ) < (a : ℕ) := by omega
    rw [show ({a, b} : Finset (Fin (m + 1))) = {b, a} from Finset.pair_comm a b,
      correlation_pathGraph_pair_eq_tanh_pow_of_lt m b a h']
    congr 1; omega

end TransferMatrix

end IsingModel
