import IsingModel.AmbientLattice.TruncatedFunctions.TwoPoint

/-!
# High-temperature susceptibility tsum bound

Bound infinite-volume susceptibility by the tsum of the truncated two-point
function under a summability assumption.
-/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

/-- **Susceptibility bounded by tsum of truncated 2-point** (GJ §17.1/§5.1):
for ferromagnetic `⟨J, 0, β⟩` and summable `j ↦ truncated2Infinite G Λ ⟨J,0,β⟩ i j`,
the infinite-volume susceptibility is bounded above by the tsum:
`susceptibilityInfinite G Λ ⟨J,0,β⟩ i ≤ ∑' j, truncated2Infinite G Λ ⟨J,0,β⟩ i j`.

**Proof**: by `ciSup_le`, it suffices to bound each `susceptibilityAlongExhaustion n`.
For `i ∈ Λ.volume n`: expand as `∑ j : ↑(Λ.volume n), correlation (inducedGraph Λn) {⟨i,hi⟩, j}`
(using `susceptibility_h_zero`), relate each term to `correlationAlongExhaustion {i,j.val} n`
(via `correlationAlongExhaustion_of_subset` + `liftFinset`), bound by `correlationInfinite`
(via `correlationAlongExhaustion_le_correlationInfinite`), and identify with
`truncated2Infinite` (via `truncated2Infinite_h_zero`). The finite sum over `↑(Λ.volume n)`
is then bounded by the tsum over `V` via `Finset.sum_coe_sort` + `Summable.sum_le_tsum`.
For `i ∉ Λ.volume n`: `susceptibilityAlongExhaustion = 0 ≤ ∑' j, truncated2Infinite ≥ 0`.

**Application**: combined with `truncated2Infinite_summable_of_lt_criticalInverseTemp`
(PR #980), this gives `susceptibilityInfinite ≤ ∑' j, truncated2Infinite < ∞` for `β < β_c`,
completing the GJ §17.1 finite-susceptibility picture. -/
theorem susceptibilityInfinite_le_tsum_truncated2Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J β : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (i : V)
    (hsumm : Summable
      (fun j => truncated2Infinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j)) :
    susceptibilityInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i
      ≤ ∑' j, truncated2Infinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j := by
  simp only [susceptibilityInfinite_eq_ciSup]
  apply ciSup_le
  intro n
  by_cases hi : i ∈ Λ.volume n
  · rw [susceptibilityAlongExhaustion_of_mem G Λ _ hi,
        susceptibilityΛ_apply, susceptibility_h_zero]
    have hstep : ∀ j : ↑(Λ.volume n),
        correlation (inducedGraph G (Λ.volume n))
          (⟨J, 0, β⟩ : IsingParams ℝ) {⟨i, hi⟩, j}
          ≤ truncated2Infinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j.val := by
      intro ⟨j, hj⟩
      have h_ij : ({i, j} : Finset V) ⊆ Λ.volume n :=
        Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hj⟩
      have h_lift : liftFinset ({i, j} : Finset V) h_ij
          = ({⟨i, hi⟩, ⟨j, hj⟩} : Finset ↑(Λ.volume n)) := by
        ext ⟨x, _⟩
        simp [mem_liftFinset, Subtype.ext_iff]
      calc correlation (inducedGraph G (Λ.volume n))
              (⟨J, 0, β⟩ : IsingParams ℝ) {⟨i, hi⟩, ⟨j, hj⟩}
          = truncated2 (inducedGraph G (Λ.volume n))
              (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩ ⟨j, hj⟩ :=
              (truncated2_h_zero (inducedGraph G (Λ.volume n)) J β ⟨i, hi⟩ ⟨j, hj⟩).symm
        _ = correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} n := by
              rw [correlationAlongExhaustion_of_subset G Λ _ h_ij, correlationΛ_apply, h_lift]
              exact truncated2_h_zero (inducedGraph G (Λ.volume n)) J β ⟨i, hi⟩ ⟨j, hj⟩
        _ ≤ correlationInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} :=
              correlationAlongExhaustion_le_correlationInfinite G Λ _ {i, j} n
        _ = truncated2Infinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j :=
              (truncated2Infinite_h_zero G Λ J β i j).symm
    calc ∑ j : ↑(Λ.volume n),
            correlation (inducedGraph G (Λ.volume n)) ⟨J,0,β⟩ {⟨i, hi⟩, j}
        ≤ ∑ j : ↑(Λ.volume n),
            truncated2Infinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j.val :=
            Finset.sum_le_sum (fun j _ => hstep j)
      _ ≤ ∑' j : V, truncated2Infinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j := by
            rw [Finset.sum_coe_sort]
            exact hsumm.sum_le_tsum (Λ.volume n)
              (fun j _ => truncated2Infinite_nonneg G Λ _ hf i j)
  · rw [susceptibilityAlongExhaustion_of_not_mem G Λ _ hi]
    exact tsum_nonneg (fun j => truncated2Infinite_nonneg G Λ _ hf i j)

end IsingModel.Ambient
