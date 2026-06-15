import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The surjective log-weight identity (GJ §18.4, Issue #1499 Phase C)

This file proves the pure finite-combinatorics heart of the Mayer–Montroll
identity, isolated from all graph-theoretic context:
`∑ₖ (-1)^(k-1)/k · #{surjections C → Fin k} = if #C = 1 then 1 else 0`.

The Mayer–Montroll regrouping (in `MayerMontroll.lean`) expands the proper-colouring
side of the cluster expansion edge-by-edge via inclusion–exclusion; the inner colour
count collapses to a sum of *surjections from the set of connected components* of a
chosen edge subset, and this identity supplies the final cancellation, leaving exactly
the connected (single-component) edge subsets.

## Strategy

We work with `surjCount n k = #{surjections Fin n → Fin k}`.  The only hard ingredient
is the surjection recurrence
`surjCount (n+1) (k+1) = (k+1) · (surjCount n (k+1) + surjCount n k)`
(split a surjection `Fin (n+1) → Fin (k+1)` by its last value `v`: the restriction to
`Fin n` either still hits `v` — a surjection onto all `k+1` colours — or misses it — a
surjection onto the remaining `k` colours).  Feeding this recurrence once into the
alternating weighted sum telescopes to `surjCount n 0 = [n = 0]`, giving the result with
no nested induction.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (p. 332).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7.3.
-/

namespace IsingModel

open Finset

/-- **Surjection count**: the number of surjective functions `Fin n → Fin k`. -/
noncomputable def surjCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin n → Fin k => Function.Surjective f)).card

/-- **No surjection onto more points than the domain has**: `surjCount n k = 0`
whenever `n < k`, since a surjection `Fin n → Fin k` forces `k ≤ n`. -/
theorem surjCount_eq_zero_of_lt {n k : ℕ} (h : n < k) : surjCount n k = 0 := by
  rw [surjCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro f _ hf
  have := Fintype.card_le_of_surjective f hf
  simp only [Fintype.card_fin] at this
  omega

/-- **Surjections onto the empty target**: `surjCount n 0 = 1` if `n = 0` and `0`
otherwise.  For `n = 0` the unique empty function is vacuously surjective; for `n > 0`
there is no function into `Fin 0` at all. -/
theorem surjCount_zero_right (n : ℕ) : surjCount n 0 = if n = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [if_pos rfl, surjCount]
    rw [Finset.card_eq_one]
    refine ⟨fun _ => by exact Fin.elim0 (by assumption), ?_⟩
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun b => Fin.elim0 b⟩
    · intro f _
      funext x
      exact Fin.elim0 x
  · rw [if_neg (by omega), surjCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro f _
    exact fun _ => (Fin.elim0 (f ⟨0, hn⟩))

/-- **`surjCount` as a subtype cardinality**: rewriting the filtered-`Finset`
definition as `Fintype.card` of the surjection subtype, the form used for the
`Equiv`-based recurrence. -/
theorem surjCount_eq_card_subtype (n k : ℕ) :
    surjCount n k = Fintype.card {f : Fin n → Fin k // Function.Surjective f} := by
  classical
  rw [surjCount, Fintype.card_subtype]

/-- **Restriction equivalence for the last-value fibre**: surjections
`F : Fin (n+1) → Fin (k+1)` with `F (last) = v` correspond, via restriction to the first
`n` coordinates (`F ∘ castSucc`, inverse `Fin.snoc · v`), to functions `g : Fin n → Fin (k+1)`
whose range covers every colour other than `v`. -/
noncomputable def surjLastFibreEquiv {n k : ℕ} (v : Fin (k + 1)) :
    {F : Fin (n + 1) → Fin (k + 1) // Function.Surjective F ∧ F (Fin.last n) = v} ≃
      {g : Fin n → Fin (k + 1) // ∀ w, w ≠ v → w ∈ Set.range g} where
  toFun F := ⟨F.1 ∘ Fin.castSucc, by
    rintro w hw
    obtain ⟨i, hi⟩ := F.2.1 w
    refine Fin.lastCases (motive := fun i => F.1 i = w → w ∈ Set.range (F.1 ∘ Fin.castSucc))
      ?_ ?_ i hi
    · intro hlast
      rw [F.2.2] at hlast
      exact absurd hlast.symm hw
    · intro j hj
      exact ⟨j, hj⟩⟩
  invFun g := ⟨Fin.snoc g.1 v, by
    refine ⟨fun w => ?_, Fin.snoc_last _ _⟩
    by_cases hwv : w = v
    · exact ⟨Fin.last n, by rw [Fin.snoc_last]; exact hwv.symm⟩
    · obtain ⟨j, hj⟩ := g.2 w hwv
      exact ⟨Fin.castSucc j, by rw [Fin.snoc_castSucc]; exact hj⟩⟩
  left_inv F := by
    apply Subtype.ext
    have h := Fin.snoc_init_self F.1
    rw [F.2.2] at h
    exact h
  right_inv g := by
    apply Subtype.ext
    funext i
    simp only [Function.comp_apply, Fin.snoc_castSucc]

/-- **Colour-removal equivalence**: functions `g : Fin n → Fin (k+1)` that cover every
colour except `v` but never take the value `v` correspond to surjections `Fin n → Fin k`
(remove `v` from the target via `finSuccAboveEquiv v`). -/
noncomputable def surjMissingColourEquiv {n k : ℕ} (v : Fin (k + 1)) :
    {g : Fin n → Fin (k + 1) // (∀ w, w ≠ v → w ∈ Set.range g) ∧ v ∉ Set.range g} ≃
      {h : Fin n → Fin k // Function.Surjective h} where
  toFun g := ⟨fun i => (finSuccAboveEquiv v).symm ⟨g.1 i, fun hi => g.2.2 ⟨i, hi⟩⟩, by
    intro j
    obtain ⟨i, hi⟩ := g.2.1 (v.succAbove j) (v.succAbove_ne j)
    refine ⟨i, ?_⟩
    simp only [Equiv.symm_apply_eq]
    apply Subtype.ext
    simp only [finSuccAboveEquiv_apply, hi]⟩
  invFun h := ⟨fun i => (finSuccAboveEquiv v (h.1 i)).1, by
    refine ⟨fun w hw => ?_, ?_⟩
    · obtain ⟨j, hj⟩ := h.2 ((finSuccAboveEquiv v).symm ⟨w, hw⟩)
      refine ⟨j, ?_⟩
      have hval : finSuccAboveEquiv v (h.1 j) = ⟨w, hw⟩ := by
        rw [hj, Equiv.apply_symm_apply]
      simpa using congrArg Subtype.val hval
    · rintro ⟨i, hi⟩
      exact (finSuccAboveEquiv v (h.1 i)).2 hi⟩
  left_inv g := by
    apply Subtype.ext
    funext i
    simp only [Equiv.apply_symm_apply]
  right_inv h := by
    apply Subtype.ext
    funext i
    simp only [Subtype.coe_eta, Equiv.symm_apply_apply]

/-- **Last-value fibre count**: among surjections `Fin (n+1) → Fin (k+1)` those sending
the last coordinate to a fixed `v` number `surjCount n (k+1) + surjCount n k` — the
restriction to the first `n` coordinates either still hits `v` (a surjection onto all
`k+1` colours) or misses it (a surjection onto the remaining `k`). -/
theorem surjLastFibre_card {n k : ℕ} (v : Fin (k + 1)) :
    Fintype.card {F : Fin (n + 1) → Fin (k + 1) //
        Function.Surjective F ∧ F (Fin.last n) = v}
      = surjCount n (k + 1) + surjCount n k := by
  classical
  rw [Fintype.card_congr (surjLastFibreEquiv v), Fintype.card_subtype,
    ← Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter (fun g : Fin n → Fin (k + 1) => ∀ w, w ≠ v → w ∈ Set.range g))
        (p := fun g => Function.Surjective g)]
  congr 1
  · -- surjective restriction = surjection onto all `k+1` colours
    rw [Finset.filter_filter, surjCount]
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨fun w _ => h w, h⟩⟩
  · -- non-surjective restriction = surjection onto the `k` colours other than `v`
    rw [Finset.filter_filter]
    have hiff : ∀ g : Fin n → Fin (k + 1),
        ((∀ w, w ≠ v → w ∈ Set.range g) ∧ ¬ Function.Surjective g) ↔
        ((∀ w, w ≠ v → w ∈ Set.range g) ∧ v ∉ Set.range g) := by
      intro g
      constructor
      · rintro ⟨hP, hns⟩
        refine ⟨hP, fun hv => hns (fun w => ?_)⟩
        by_cases hwv : w = v
        · rw [hwv]; exact hv
        · exact hP w hwv
      · rintro ⟨hP, hvn⟩
        exact ⟨hP, fun hsurj => hvn (hsurj v)⟩
    rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeEquivRight hiff),
      Fintype.card_congr (surjMissingColourEquiv v), ← surjCount_eq_card_subtype]

/-- **Surjection recurrence**: `surjCount (n+1) (k+1) = (k+1)·(surjCount n (k+1) +
surjCount n k)`, by splitting a surjection `Fin (n+1) → Fin (k+1)` according to its last
value (`k+1` choices), each fibre contributing `surjLastFibre_card`. -/
theorem surjCount_succ_succ (n k : ℕ) :
    surjCount (n + 1) (k + 1) = (k + 1) * (surjCount n (k + 1) + surjCount n k) := by
  classical
  rw [surjCount]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun F : Fin (n + 1) → Fin (k + 1) => F (Fin.last n))
    (t := Finset.univ) (fun F _ => Finset.mem_univ _)]
  have hfib : ∀ v : Fin (k + 1),
      ((Finset.univ.filter (fun F : Fin (n + 1) → Fin (k + 1) => Function.Surjective F)).filter
        (fun F => F (Fin.last n) = v)).card = surjCount n (k + 1) + surjCount n k := by
    intro v
    rw [Finset.filter_filter, ← Fintype.card_subtype]
    exact surjLastFibre_card v
  rw [Finset.sum_congr rfl (fun v _ => hfib v), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul]

/-- **The surjective log-weight identity** (`ℕ`-domain form): for every `n`,
`∑_{k=1}^{n} (-1)^(k-1)/k · surjCount n k = [n = 1]`.  Feeding the surjection recurrence once
into the alternating sum telescopes everything to `surjCount n 0 = [n = 0]`. -/
theorem surjLogWeight_eq (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) * (surjCount n k : ℝ) =
      if n = 1 then 1 else 0 := by
  rcases n with _ | m
  · simp
  · -- n = m + 1: reindex to `range (m+1)`, apply the recurrence, telescope.
    have hmap : Finset.Icc 1 (m + 1) =
        (Finset.range (m + 1)).map ⟨fun j => 1 + j, add_right_injective 1⟩ := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · intro h; exact ⟨k - 1, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩; omega
    rw [hmap, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
    have key : ∀ j ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ (1 + j - 1) / ((1 + j : ℕ) : ℝ)) * (surjCount (m + 1) (1 + j) : ℝ) =
          (-1 : ℝ) ^ j * ((surjCount m (j + 1) : ℝ) + (surjCount m j : ℝ)) := by
      intro j _
      have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
      rw [show (1 + j) = (j + 1) from Nat.add_comm 1 j, surjCount_succ_succ m j,
        Nat.add_sub_cancel]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl key]
    -- split into S1 + S2
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    -- peel S1 (last index, vanishes) and S2 (first index, = surjCount m 0)
    rw [Finset.sum_range_succ (fun j => (-1 : ℝ) ^ j * (surjCount m (j + 1) : ℝ)),
      surjCount_eq_zero_of_lt (Nat.lt_succ_self m), Nat.cast_zero, mul_zero, add_zero,
      Finset.sum_range_succ' (fun j => (-1 : ℝ) ^ j * (surjCount m j : ℝ)) m,
      pow_zero, one_mul]
    -- combine the two range-`m` sums: each summand `(-1)^j + (-1)^(j+1)` cancels
    rw [← add_assoc, ← Finset.sum_add_distrib]
    have hzero : ∑ j ∈ Finset.range m,
        ((-1 : ℝ) ^ j * (surjCount m (j + 1) : ℝ) +
          (-1 : ℝ) ^ (j + 1) * (surjCount m (j + 1) : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [pow_succ]
      ring
    rw [hzero, zero_add, surjCount_zero_right m]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · rw [if_neg (show m ≠ 0 by omega), if_neg (show m + 1 ≠ 1 by omega), Nat.cast_zero]

/-- **Surjection count is type-invariant**: the number of surjections `C → Fin k` for any
finite `C` equals `surjCount (Fintype.card C) k` (transport along `C ≃ Fin (card C)`). -/
theorem card_surjective_eq_surjCount (C : Type*) [Fintype C] [DecidableEq C] (k : ℕ) :
    (Finset.univ.filter (fun f : C → Fin k => Function.Surjective f)).card =
      surjCount (Fintype.card C) k := by
  classical
  rw [surjCount, ← Fintype.card_subtype, ← Fintype.card_subtype]
  apply Fintype.card_congr
  let e := Fintype.equivFin C
  exact
    { toFun := fun f => ⟨fun i => f.1 (e.symm i), f.2.comp e.symm.surjective⟩
      invFun := fun g => ⟨fun c => g.1 (e c), g.2.comp e.surjective⟩
      left_inv := fun f => by apply Subtype.ext; funext c; simp [e]
      right_inv := fun g => by apply Subtype.ext; funext i; simp [e] }

/-- **The surjective log-weight identity** (general finite-type form): for any finite type
`C`, `∑_{k=1}^{#C} (-1)^(k-1)/k · #{surjections C → Fin k} = [#C = 1]`.  This is the pure
combinatorial cancellation feeding the Mayer–Montroll edge expansion: only the
single-component (connected) edge subsets survive. -/
theorem surjective_logWeight_eq_connected_indicator (C : Type*) [Fintype C] [DecidableEq C] :
    ∑ k ∈ Finset.Icc 1 (Fintype.card C),
        ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
          ((Finset.univ.filter fun f : C → Fin k => Function.Surjective f).card : ℝ) =
      if Fintype.card C = 1 then 1 else 0 := by
  simp_rw [card_surjective_eq_surjCount C]
  exact surjLogWeight_eq (Fintype.card C)

end IsingModel
