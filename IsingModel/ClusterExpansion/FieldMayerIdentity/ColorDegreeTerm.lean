import IsingModel.ClusterExpansion.FieldMayerIdentity.Definitions
import IsingModel.ClusterExpansion.FieldMayerIdentity.ColorClassPorts

/-!
# Field Mayer–Montroll identity: colour-degree bridges and summability
(GJ §17.6.1, brick 4 — child 3 of 4)

The L2/L3 log-Taylor and Mayer bridges to `fieldColorDegreeTerm`, plus the L4 double
summability of the colour-degree term via the brick-3 domination.  See
`FieldMayerIdentity.lean` for the full module overview.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## L2 / L3: log-Taylor and Mayer bridges to `fieldColorDegreeTerm` -/

/-- **`ε_{a,b}^n` expansion as a sum over connected family-tuples**: applying
`Finset.sum_pow'`, `ε_{a,b}^n = ∑_ω ∏_i ∏_{P ∈ ω i} w_{a,b}(P)` over `n`-tuples of
nonempty vd connected families.  Field mirror of
`vdPolymerFamilies_sum_minus_one_pow`. -/
theorem fieldVdPolymerFamilies_sum_minus_one_pow (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) (n : ℕ) :
    (∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, fieldPolymerWeight a b P) ^ n =
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin n => (vdConnectedPolymerFamilies G).erase ∅),
        ∏ i : Fin n, ∏ P ∈ ω i, fieldPolymerWeight a b P :=
  Finset.sum_pow' _ _ n

/-- **Log-Taylor term as a connected family-tuple sum**: the `n`-th term
`(-1)^n · ε_{a,b}^(n+1)/(n+1)` expands into a sum over `(n+1)`-tuples of nonempty
vd connected families with the scalar coefficient pulled inside.  Field mirror of
`logTaylor_eps_term_eq_sum_vdFamilyTuples`. -/
theorem fieldLogTaylor_eps_term_eq_sum_vdFamilyTuples (G : SimpleGraph ι)
    [Fintype G.edgeSet] (a b : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n *
        (∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, fieldPolymerWeight a b P) ^ (n + 1) / (n + 1) =
      ∑ Ω ∈ Fintype.piFinset
            (fun _ : Fin (n + 1) => (vdConnectedPolymerFamilies G).erase ∅),
        ((-1 : ℝ) ^ n / (n + 1)) *
          ∏ i : Fin (n + 1), ∏ P ∈ Ω i, fieldPolymerWeight a b P := by
  rw [fieldVdPolymerFamilies_sum_minus_one_pow G a b (n + 1), Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun Ω _ => ?_)
  ring

/-- **Field Mayer term in colouring form**: substituting
`ursellCoefficient_eq_coloring_sum` (reused verbatim) into
`fieldMayerExpansionTerm`, the `r`-th field term is the field activity-weighted sum
over polymer sequences of the alternating proper-surjective-colouring count,
normalised by `r!`.  Field mirror of `mayerExpansionTerm_eq_coloring_form`. -/
theorem fieldMayerExpansionTerm_eq_coloring_form (G : SimpleGraph ι) [Fintype G.edgeSet]
    (r : ℕ) (a b : ℝ) :
    fieldMayerExpansionTerm G r a b =
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
        (∑ k ∈ Finset.Icc 1 r, ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
            ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ)) /
          (r.factorial : ℝ) * fieldClusterSeqActivity a b ω := by
  unfold fieldMayerExpansionTerm
  exact Finset.sum_congr rfl (fun ω _ => by rw [ursellCoefficient_eq_coloring_sum])

/-- **Field Mayer term as a colour-degree double sum**: distributing the
colour-degree sum out of the sequence sum.  Field mirror of
`mayerExpansionTerm_eq_double_sum`. -/
theorem fieldMayerExpansionTerm_eq_double_sum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (r : ℕ) (a b : ℝ) :
    fieldMayerExpansionTerm G r a b =
      ∑ k ∈ Finset.Icc 1 r, ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
            (r.factorial : ℝ) * fieldClusterSeqActivity a b ω := by
  rw [fieldMayerExpansionTerm_eq_coloring_form]
  simp_rw [Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

/-- **Log-Taylor term as a field colouring sum**: combining
`fieldLogTaylor_eps_term_eq_sum_vdFamilyTuples` with the per-`m` identity
`fieldVdFamilyTuple_sum_eq_seq_coloring_sum` (`m = n+1`).  Field mirror of
`logTaylor_term_eq_coloring`. -/
theorem fieldLogTaylor_term_eq_coloring (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n *
        (∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, fieldPolymerWeight a b P) ^ (n + 1) / (n + 1) =
      ∑ r ∈ Finset.range ((n + 1) * (allConnectedPolymers G).card + 1),
        ((-1 : ℝ) ^ n / (n + 1)) *
          ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
            ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) (n + 1)).card : ℝ) /
              (r.factorial : ℝ) * fieldClusterSeqActivity a b ω := by
  rw [fieldLogTaylor_eps_term_eq_sum_vdFamilyTuples, ← Finset.mul_sum,
    fieldVdFamilyTuple_sum_eq_seq_coloring_sum, Finset.mul_sum]

/-- **`fieldColorDegreeTerm` vanishes for `k > r`**: no surjective `k`-colouring of
`Fin r`.  Field mirror of `colorDegreeTerm_eq_zero_of_lt`. -/
theorem fieldColorDegreeTerm_eq_zero_of_lt (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) {r k : ℕ} (hrk : r < k) : fieldColorDegreeTerm G a b r k = 0 := by
  rw [fieldColorDegreeTerm]
  refine mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun ω _ => ?_)))
  rw [properSurjectiveColorings_eq_empty_of_card_lt _ hrk, Finset.card_empty, Nat.cast_zero,
    zero_div, zero_mul]

/-- **`fieldColorDegreeTerm` vanishes at `k = 0`**: the `1/k = 1/0 = 0` factor.
Field mirror of `colorDegreeTerm_zero_right`. -/
theorem fieldColorDegreeTerm_zero_right (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) (r : ℕ) : fieldColorDegreeTerm G a b r 0 = 0 := by
  rw [fieldColorDegreeTerm, Nat.cast_zero, div_zero, zero_mul]

/-- **`fieldColorDegreeTerm` vanishes when `m·|allConnectedPolymers G| < r`**: no
surjective `m`-colouring of a graph on `Fin r` from `r` connected polymers.  Field
mirror of `colorDegreeTerm_eq_zero_of_card_lt`. -/
theorem fieldColorDegreeTerm_eq_zero_of_card_lt (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) {r m : ℕ} (hr : m * (allConnectedPolymers G).card < r) :
    fieldColorDegreeTerm G a b r m = 0 := by
  classical
  rw [fieldColorDegreeTerm]
  refine mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun ω hω => ?_)))
  have hω' : ∀ i, ω i ∈ allConnectedPolymers G := fun i => Fintype.mem_piFinset.mp hω i
  rw [fieldProperSurjectiveColorings_empty_of_card_lt G hω' hr, Finset.card_empty,
    Nat.cast_zero, zero_div, zero_mul]

/-- **Field Mayer term as the `tsum` of its colour-degree row**:
`fieldMayerExpansionTerm G r a b = ∑'_k fieldColorDegreeTerm G a b r k`.  The row is
finitely supported in `Icc 1 r`.  Field mirror of
`mayerExpansionTerm_eq_tsum_colorDegreeTerm`. -/
theorem fieldMayerExpansionTerm_eq_tsum_fieldColorDegreeTerm (G : SimpleGraph ι)
    [Fintype G.edgeSet] (r : ℕ) (a b : ℝ) :
    fieldMayerExpansionTerm G r a b = ∑' k, fieldColorDegreeTerm G a b r k := by
  classical
  rw [fieldMayerExpansionTerm_eq_double_sum,
    tsum_eq_sum (s := Finset.Icc 1 r) (fun k hk => by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le, Nat.lt_one_iff] at hk
      rcases hk with hk0 | hkr
      · rw [hk0, fieldColorDegreeTerm_zero_right]
      · exact fieldColorDegreeTerm_eq_zero_of_lt G a b hkr)]
  rfl

/-- **Log-Taylor term as the `tsum` of its colour-degree column**: the `n`-th
log-Taylor term equals `∑'_r fieldColorDegreeTerm G a b r (n+1)`.  The column is
finitely supported (`r ≤ (n+1)·|allConnectedPolymers G|`).  Field mirror of
`logTaylorTerm_eq_tsum_colorDegreeTerm`. -/
theorem fieldLogTaylorTerm_eq_tsum_fieldColorDegreeTerm (G : SimpleGraph ι)
    [Fintype G.edgeSet] (a b : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n *
        (∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, fieldPolymerWeight a b P) ^ (n + 1) / (n + 1) =
      ∑' r, fieldColorDegreeTerm G a b r (n + 1) := by
  classical
  rw [fieldLogTaylor_term_eq_coloring,
    tsum_eq_sum (s := Finset.range ((n + 1) * (allConnectedPolymers G).card + 1)) (fun r hr => by
      rw [Finset.mem_range, not_lt] at hr
      exact fieldColorDegreeTerm_eq_zero_of_card_lt G a b
        (by omega : (n + 1) * (allConnectedPolymers G).card < r))]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [fieldColorDegreeTerm, Nat.add_sub_cancel]
  push_cast
  ring

/-! ## L4: double summability of `fieldColorDegreeTerm` via brick-3 domination -/

/-- **Per-`(r,k)` field colour-degree bound**: `|fieldColorDegreeTerm G a b r k| ≤
(k^(r-1)/r!)·A_C^r`, `A_C = ∑_{P ∈ allConnectedPolymers G} |tanh a|^|P|`.  Combines
`card_properSurjectiveColorings_le` (verbatim), the brick-3 domination
`abs_fieldClusterSeqActivity_le`, and the factorised total activity
`sum_clusterSeqActivity_piFinset_connected`.  Field/connected mirror of
`abs_colorDegreeTerm_le`. -/
theorem abs_fieldColorDegreeTerm_le (G : SimpleGraph ι) [Fintype G.edgeSet] (a b : ℝ)
    (r k : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    |fieldColorDegreeTerm G a b r k| ≤
      ((k : ℝ) ^ (r - 1) / (r.factorial : ℝ)) *
        (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
  classical
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [fieldColorDegreeTerm, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos hkpos, one_div]
  have hsum : |∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
          (r.factorial : ℝ) * fieldClusterSeqActivity a b ω| ≤
      ((k : ℝ) ^ r / (r.factorial : ℝ)) *
        (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
    calc |∑ ω ∈ _, _|
        ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
            |((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
              (r.factorial : ℝ) * fieldClusterSeqActivity a b ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
            ((k : ℝ) ^ r / (r.factorial : ℝ)) * clusterSeqActivity |Real.tanh a| ω := by
          refine Finset.sum_le_sum (fun ω _ => ?_)
          rw [abs_mul, abs_div, Nat.abs_cast, Nat.abs_cast]
          refine mul_le_mul ?_ (abs_fieldClusterSeqActivity_le a b ω) (abs_nonneg _)
            (by positivity)
          gcongr
          exact_mod_cast card_properSurjectiveColorings_le
            (polymerSeqIncompatibilityGraph ω) k
      _ = ((k : ℝ) ^ r / (r.factorial : ℝ)) *
            (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
          rw [← Finset.mul_sum, sum_clusterSeqActivity_piFinset_connected]
  have hkr : (k : ℝ)⁻¹ * (k : ℝ) ^ r = (k : ℝ) ^ (r - 1) := by
    have h1 : (k : ℝ) ^ r = (k : ℝ) * (k : ℝ) ^ (r - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hr]
    rw [h1, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hkpos), one_mul]
  calc (k : ℝ)⁻¹ * |∑ ω ∈ _, _|
      ≤ (k : ℝ)⁻¹ * (((k : ℝ) ^ r / (r.factorial : ℝ)) *
          (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r) := by gcongr
    _ = ((k : ℝ) ^ (r - 1) / (r.factorial : ℝ)) *
          (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
        rw [← mul_assoc, ← mul_div_assoc, hkr]

/-- **Field colour-degree row bound**: `∑_{k=1}^r |fieldColorDegreeTerm G a b r k| ≤
(r^r/r!)·A_C^r`, summing `abs_fieldColorDegreeTerm_le` over `k ∈ Icc 1 r`.  Field
mirror of `sum_abs_colorDegreeTerm_le`. -/
theorem sum_abs_fieldColorDegreeTerm_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ Finset.Icc 1 r, |fieldColorDegreeTerm G a b r k| ≤
      ((r : ℝ) ^ r / (r.factorial : ℝ)) *
        (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
  calc ∑ k ∈ Finset.Icc 1 r, |fieldColorDegreeTerm G a b r k|
      ≤ ∑ k ∈ Finset.Icc 1 r,
          ((r : ℝ) ^ (r - 1) / (r.factorial : ℝ)) *
            (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_Icc] at hk
        refine (abs_fieldColorDegreeTerm_le G a b r k hk.1 hr).trans ?_
        gcongr
        exact_mod_cast hk.2
    _ = ((r : ℝ) ^ r / (r.factorial : ℝ)) *
          (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        have hrr : (r : ℝ) * (r : ℝ) ^ (r - 1) = (r : ℝ) ^ r := by
          rw [← pow_succ', Nat.sub_add_cancel hr]
        rw [← mul_assoc, ← mul_div_assoc, hrr]

/-- **Field row absolute `tsum` bound**: `∑'_k |fieldColorDegreeTerm G a b r k| ≤
(r^r/r!)·A_C^r`.  Each row is finitely supported (`Icc 1 r`).  Field mirror of
`tsum_abs_colorDegreeTerm_le`. -/
theorem tsum_abs_fieldColorDegreeTerm_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) (r : ℕ) :
    ∑' k, |fieldColorDegreeTerm G a b r k| ≤
      ((r : ℝ) ^ r / (r.factorial : ℝ)) *
        (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
  classical
  rw [tsum_eq_sum (s := Finset.range (r + 1)) (fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    rw [fieldColorDegreeTerm_eq_zero_of_lt G a b (by omega : r < k), abs_zero])]
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · subst hr0
    simp [fieldColorDegreeTerm_zero_right]
  · rw [show Finset.range (r + 1) = insert 0 (Finset.Icc 1 r) from by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
      Finset.sum_insert (by simp), fieldColorDegreeTerm_zero_right, abs_zero, zero_add]
    exact sum_abs_fieldColorDegreeTerm_le G a b r hr1

/-- **Double summability of the field colour-degree term**:
`(r,k) ↦ fieldColorDegreeTerm G a b r k` is summable over `ℕ × ℕ` when
`e·A_C < 1` (`A_C = ∑_{P ∈ allConnectedPolymers G} |tanh a|^|P|`, the brick-3
window).  Rows finitely supported, row absolute sums majorised by the summable
`(r^r/r!)·A_C^r` (`summable_pow_self_div_factorial_mul_abs_pow`, verbatim).  Field
mirror of `summable_uncurry_colorDegreeTerm`; enables the capstone `tsum_comm`. -/
theorem summable_uncurry_fieldColorDegreeTerm (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ)
    (hact : Real.exp 1 * (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) < 1) :
    Summable (fun p : ℕ × ℕ => fieldColorDegreeTerm G a b p.1 p.2) := by
  classical
  have hsumnn : (0 : ℝ) ≤ ∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card :=
    Finset.sum_nonneg (fun P _ => by positivity)
  have hAabs : Real.exp 1 *
      |∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card| < 1 := by
    rwa [abs_of_nonneg hsumnn]
  rw [← summable_abs_iff, summable_prod_of_nonneg (fun p => abs_nonneg _)]
  refine ⟨fun r => ?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := Finset.range (r + 1)) (fun k hk => ?_)
    rw [Finset.mem_range, not_lt] at hk
    rw [fieldColorDegreeTerm_eq_zero_of_lt G a b (by omega : r < k), abs_zero]
  · refine Summable.of_nonneg_of_le (fun r => tsum_nonneg (fun k => abs_nonneg _))
      (fun r => tsum_abs_fieldColorDegreeTerm_le G a b r) ?_
    have hpow : ∀ r : ℕ, ((r : ℝ) ^ r / (r.factorial : ℝ)) *
        (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r =
        ((r : ℝ) ^ r / (r.factorial : ℝ)) *
          |∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card| ^ r := by
      intro r; rw [abs_of_nonneg hsumnn]
    simp_rw [hpow]
    exact summable_pow_self_div_factorial_mul_abs_pow _ hAabs

end IsingModel
