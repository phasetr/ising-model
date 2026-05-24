import IsingModel.FieldDerivative.CorrelationMonotonicity

/-!
# Field antitonicity of truncated two-point functions

GHS-based finite-volume antitonicity in the external field.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## GHS consequence: truncated2 antitone in h (Step 124) -/

/-- Helper: the per-site summand in `d/dh truncated2(i,j)`.

For each `k : ι`, this is
`corr(symmDiff {i,j} {k}) - corr(symmDiff {i} {k}) * corr({j})
- corr({i}) * corr(symmDiff {j} {k}) - corr({i,j}) * corr({k})
+ 2 * corr({i}) * corr({j}) * corr({k})`.

For `k ∉ {i,j}` this equals `truncated3 G p i j k ≤ 0` (GHS).
For `k = i` or `k = j` this equals `-2 * corr({m}) * truncated2 G p i j ≤ 0`. -/
private noncomputable def truncated2FieldDerivSummand
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i j k : ι) : ℝ :=
  correlation G p (symmDiff {i, j} {k})
  - correlation G p (symmDiff {i} {k}) * correlation G p {j}
  - correlation G p {i} * correlation G p (symmDiff {j} {k})
  - correlation G p {i, j} * correlation G p {k}
  + 2 * correlation G p {i} * correlation G p {j} * correlation G p {k}

/-- For `k ∉ {i, j}`, the summand equals `truncated3 G p i j k`. -/
private lemma truncated2FieldDerivSummand_of_not_mem
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) {i j k : ι} (hki : k ≠ i) (hkj : k ≠ j) :
    truncated2FieldDerivSummand G p i j k = truncated3 G p i j k := by
  unfold truncated2FieldDerivSummand truncated3
  have hijk : symmDiff ({i, j} : Finset ι) {k} = {i, j, k} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h | rfl, hk⟩ | ⟨rfl, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact Or.inl ⟨Or.inl rfl, hki.symm⟩
      · exact Or.inl ⟨Or.inr rfl, hkj.symm⟩
      · exact Or.inr ⟨rfl, fun h => h.elim hki hkj⟩
  have hik : symmDiff ({i} : Finset ι) {k} = {i, k} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hki.symm⟩
      · exact Or.inr ⟨rfl, hki⟩
  have hjk : symmDiff ({j} : Finset ι) {k} = {j, k} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hkj.symm⟩
      · exact Or.inr ⟨rfl, hkj⟩
  rw [hijk, hik, hjk]; ring

/-- For `k = i` (with `i ≠ j`), the summand equals `-2 * corr({i}) * truncated2`. -/
private lemma truncated2FieldDerivSummand_of_eq_left
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) {i j : ι} (hij : i ≠ j) :
    truncated2FieldDerivSummand G p i j i =
    -2 * correlation G p {i} * truncated2 G p i j := by
  unfold truncated2FieldDerivSummand truncated2
  have h1 : symmDiff ({i, j} : Finset ι) {i} = {j} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h | rfl, hi⟩ | ⟨rfl, h⟩)
      · exact absurd h hi
      · rfl
      · exact absurd (Or.inl rfl) h
    · intro rfl; exact Or.inl ⟨Or.inr rfl, Ne.symm hij⟩
  have h2 : symmDiff ({i} : Finset ι) {i} = (∅ : Finset ι) := symmDiff_self _
  have h3 : symmDiff ({j} : Finset ι) {i} = {j, i} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, Ne.symm hij⟩
      · exact Or.inr ⟨rfl, hij⟩
  rw [h1, h2, h3]
  simp only [correlation_empty]
  have h4 : ({j, i} : Finset ι) = {i, j} := Finset.pair_comm j i
  rw [h4]
  ring

/-- For `k = j` (with `i ≠ j`), the summand equals `-2 * corr({j}) * truncated2`. -/
private lemma truncated2FieldDerivSummand_of_eq_right
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) {i j : ι} (hij : i ≠ j) :
    truncated2FieldDerivSummand G p i j j =
    -2 * correlation G p {j} * truncated2 G p i j := by
  unfold truncated2FieldDerivSummand truncated2
  have h1 : symmDiff ({i, j} : Finset ι) {j} = {i} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h | rfl, hj⟩ | ⟨rfl, h⟩)
      · exact h
      · exact absurd rfl hj
      · exact absurd (Or.inr rfl) h
    · intro rfl; exact Or.inl ⟨Or.inl rfl, hij⟩
  have h2 : symmDiff ({i} : Finset ι) {j} = {i, j} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hij⟩
      · exact Or.inr ⟨rfl, Ne.symm hij⟩
  have h3 : symmDiff ({j} : Finset ι) {j} = (∅ : Finset ι) := symmDiff_self _
  rw [h1, h2, h3]
  simp only [correlation_empty]
  ring

/-- Each summand is nonpositive for ferromagnetic `p` with `hf.hh ≥ 0`, `i ≠ j`. -/
private lemma truncated2FieldDerivSummand_nonpos
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {i j : ι} (hij : i ≠ j) (k : ι) :
    truncated2FieldDerivSummand G p i j k ≤ 0 := by
  by_cases hki : k = i
  · rw [hki, truncated2FieldDerivSummand_of_eq_left G p hij]
    apply mul_nonpos_of_nonpos_of_nonneg
    · apply mul_nonpos_of_nonpos_of_nonneg
      · norm_num
      · exact gks_first G p hf _
    · exact truncated2_nonneg G p hf i j
  · by_cases hkj : k = j
    · rw [hkj, truncated2FieldDerivSummand_of_eq_right G p hij]
      apply mul_nonpos_of_nonpos_of_nonneg
      · apply mul_nonpos_of_nonpos_of_nonneg
        · norm_num
        · exact gks_first G p hf _
      · exact truncated2_nonneg G p hf i j
    · rw [truncated2FieldDerivSummand_of_not_mem G p hki hkj]
      exact ghs_inequality G p hf i j k hij (Ne.symm hkj) (Ne.symm hki)

/-- The h-derivative of `truncated2 G (⟨J, h, β⟩) i j` equals `β * Σₖ summand`. -/
private lemma hasDerivAt_truncated2_field_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j : ι) :
    HasDerivAt (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j)
      (β * ∑ k : ι, truncated2FieldDerivSummand G (⟨J, h, β⟩ : IsingParams ℝ) i j k) h := by
  unfold truncated2
  have h_ij := hasDerivAt_correlation_field G J h β {i, j}
  have h_i := hasDerivAt_correlation_field G J h β {i}
  have h_j := hasDerivAt_correlation_field G J h β {j}
  have hd := h_ij.sub (h_i.mul h_j)
  convert hd using 1
  set p := (⟨J, h, β⟩ : IsingParams ℝ)
  rw [gibbsExpectation_spinProd_mul_mag G p {i, j},
      gibbsExpectation_spinProd_mul_mag G p {i},
      gibbsExpectation_spinProd_mul_mag G p {j},
      gibbsExpectation_totalMag_eq_sum G p]
  unfold truncated2FieldDerivSummand
  -- Split sums (forward), then factor out constants (backward), then ring identity
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- **GHS consequence (Step 124)**: The truncated 2-point function `⟨σᵢ; σⱼ⟩_T` is antitone
in `h` on `[0, ∞)` for distinct sites `i ≠ j` and ferromagnetic coupling `J ≥ 0`, `β > 0`.

`d/dh ⟨σᵢ; σⱼ⟩_T = β Σₖ (GHS-term_k) ≤ 0`:
each summand equals `truncated3(i,j,k) ≤ 0` (distinct) or
`-2 corr({m}) · truncated2(i,j) ≤ 0` (degenerate).

Reference: Glimm–Jaffe §4.3, Cor. 4.3.4 (GHS inequality);
Friedli–Velenik §3.6.3 (consequences). -/
theorem truncated2_antitoneOn_h_of_ne
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) {i j : ι} (hij : i ≠ j) :
    AntitoneOn (fun h => truncated2 G (⟨J, h, β⟩ : IsingParams ℝ) i j) (Set.Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
  · intro h _
    exact (hasDerivAt_truncated2_field_eq G J h β i j).continuousAt.continuousWithinAt
  · intro h hh
    rw [interior_Ici] at hh ⊢
    exact (hasDerivAt_truncated2_field_eq G J h β i j).hasDerivWithinAt
  · intro h hh
    rw [interior_Ici] at hh
    apply mul_nonpos_of_nonneg_of_nonpos hβ.le
    apply Finset.sum_nonpos
    intro k _
    exact truncated2FieldDerivSummand_nonpos G (⟨J, h, β⟩ : IsingParams ℝ)
      ⟨hJ, le_of_lt hh, hβ⟩ hij k

end IsingModel
