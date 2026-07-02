import IsingModel.RandomCurrent.Peeling

/-!
# Global switching identity (`tsum` / `iSup` lift, unbounded form)

The `N → ∞` lift of the bounded global switching identity (Stage A brick 1,
`Current.sum_prod_eq_sum_doubled_subFinset`): it removes the per-edge caps
`m e ≤ N`, `(M − m) e ≤ N` and both bounded truncations, upgrading the finite
weight-preserving bijection to a statement about the actual (unbounded) weight
sums `Current.weightSum`.

Concretely, for source sets `A B : Finset ↑Λ` and `0 ≤ β J`,
`weightSum A · weightSum B` equals a `tsum` over *all* doubled currents `M` of
the *cap-free* finite inner sum `∑_{m ≤ M, ∂m = A, ∂(M − m) = B} w(m) w(M − m)`.

The lift is a genuine limit of the true brick-1 bijection: no new inequality or
combinatorial move is introduced. Both sides are exhibited as limits of the
bounded quantity `L(N) = R(N)`; uniqueness of limits closes the identity. The
right-hand limit is a squeeze between the two cap-free envelopes
`∑_{M ∈ boundedFinset N} F` and `∑_{M ∈ boundedFinset (2 N)} F`, using that the
caps are vacuous once `M` lies below the ceiling (`boundedFinset N`).

This is Stage A brick 2 of the random-current build toward the
lower-semicontinuous half of Glimm–Jaffe Theorem 17.5.1 (issue #4386, thread
#4418). The connectivity (percolation) representation is deferred to Stage B.

## References

* Aizenman, M. (1982). Geometric analysis of φ⁴ fields, Lemma 4.1.
* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and
  Triviality* (1992), Chapter 12.
* Glimm–Jaffe, *Quantum Physics*, §5.1 and §17.5 Theorem 17.5.1 (p. 312);
  Friedli–Velenik, Theorem 9.35.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **Global switching identity, unbounded form (Stage A brick 2)**: for
source sets `A B : Finset ↑Λ` and non-negative coupling `0 ≤ β J`, the product
of the two source-constrained weight sums equals a `tsum` over all doubled
currents `M` of the cap-free finite inner sum over subcurrents `m ≤ M` with
`∂m = A` and `∂(M − m) = B`:
`weightSum A · weightSum B
  = ∑' M, ∑_{m ≤ M, ∂m = A, ∂(M − m) = B} w(m) w(M − m)`.

Proof: both sides are limits of the bounded quantity `L(N) = R(N)` of brick 1
(`Current.sum_prod_eq_sum_doubled_subFinset`). The left side tends to
`weightSum A · weightSum B` by `weightSum_eq_iSup` and monotone convergence of
the bounded sums; the right side is squeezed between the cap-free envelopes
`∑_{M ∈ boundedFinset N} F` and `∑_{M ∈ boundedFinset (2 N)} F`, both converging
to the `tsum` (summable via the uniform bound `exp(β J)^|E|`). Uniqueness of
limits (`tendsto_nhds_unique`) closes the identity. Zero field (`h = 0`) is
baked in. (Aizenman 1982 Lemma 4.1 / FV Theorem 9.35 / GJ §17.5.) -/
theorem Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A B : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    Current.weightSum G Λ A β J * Current.weightSum G Λ B β J
      = ∑' M : Current G Λ,
          ∑ m ∈ (Current.subFinset G Λ M).filter
              (fun m => m.sources G Λ = A ∧ (M - m).sources G Λ = B),
            m.weight G Λ β J * (M - m).weight G Λ β J := by
  classical
  -- The cap-free inner sum `F` (target summand) and the capped inner sum
  -- `Fcap N` of brick 1 (with the per-edge caps retained).
  set F : Current G Λ → ℝ := fun M =>
    ∑ m ∈ (Current.subFinset G Λ M).filter
        (fun m => m.sources G Λ = A ∧ (M - m).sources G Λ = B),
      m.weight G Λ β J * (M - m).weight G Λ β J with hFdef
  set Fcap : ℕ → Current G Λ → ℝ := fun N M =>
    ∑ m ∈ (Current.subFinset G Λ M).filter
        (fun m => m.sources G Λ = A ∧ (M - m).sources G Λ = B
          ∧ ∀ e, m e ≤ N ∧ (M - m) e ≤ N),
      m.weight G Λ β J * (M - m).weight G Λ β J with hFcapdef
  -- Every summand `w(m) w(M − m)` is non-negative under `0 ≤ β J`.
  have hterm_nonneg : ∀ M m : Current G Λ,
      0 ≤ m.weight G Λ β J * (M - m).weight G Λ β J := fun M m =>
    mul_nonneg (Current.weight_nonneg G Λ hβJ m)
      (Current.weight_nonneg G Λ hβJ (M - m))
  have hF_nonneg : ∀ M, 0 ≤ F M := by
    intro M
    simp only [hFdef]
    exact Finset.sum_nonneg (fun m _ => hterm_nonneg M m)
  have hFcap_nonneg : ∀ (N : ℕ) (M : Current G Λ), 0 ≤ Fcap N M := by
    intro N M
    simp only [hFcapdef]
    exact Finset.sum_nonneg (fun m _ => hterm_nonneg M m)
  -- Brick 1 in `Fcap` form: `L(N) = wsB N A · wsB N B = ∑_{M ∈ B_{2N}} Fcap N M`.
  have hLR : ∀ N : ℕ,
      CurrentBounded.weightSum G Λ N A β J * CurrentBounded.weightSum G Λ N B β J
        = ∑ M ∈ Current.boundedFinset G Λ (2 * N), Fcap N M := by
    intro N
    simp only [hFcapdef]
    rw [CurrentBounded.weightSum_eq_sum_boundedFinset,
      CurrentBounded.weightSum_eq_sum_boundedFinset,
      ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_mul_sum]
    exact Current.sum_prod_eq_sum_doubled_subFinset G Λ N A B β J
  -- Caps are vacuous below the ceiling: `Fcap N M = F M` for `M ∈ B_N`.
  have hcapfree : ∀ (N : ℕ) (M : Current G Λ), (∀ e, M e ≤ N) →
      Fcap N M = F M := by
    intro N M hM
    simp only [hFcapdef, hFdef]
    refine Finset.sum_congr (Finset.filter_congr (fun m hm => ?_)) (fun m _ => rfl)
    rw [Current.mem_subFinset_iff] at hm
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, fun e =>
        ⟨le_trans (hm e) (hM e),
          le_trans (Current.sub_le_self G Λ M m e) (hM e)⟩⟩
  -- Deleting the caps only adds non-negative terms: `Fcap N M ≤ F M`.
  have hFcap_le_F : ∀ (N : ℕ) (M : Current G Λ), Fcap N M ≤ F M := by
    intro N M
    simp only [hFcapdef, hFdef]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.monotone_filter_right _ (fun m _ h => ⟨h.1, h.2.1⟩))
      (fun m _ _ => hterm_nonneg M m)
  -- Lower squeeze: `∑_{M ∈ B_N} F ≤ wsB N A · wsB N B`.
  have hLS : ∀ N : ℕ, ∑ M ∈ Current.boundedFinset G Λ N, F M
      ≤ CurrentBounded.weightSum G Λ N A β J * CurrentBounded.weightSum G Λ N B β J := by
    intro N
    rw [hLR N]
    calc ∑ M ∈ Current.boundedFinset G Λ N, F M
        = ∑ M ∈ Current.boundedFinset G Λ N, Fcap N M :=
          Finset.sum_congr rfl (fun M hM =>
            (hcapfree N M ((Current.mem_boundedFinset_iff G Λ N M).mp hM)).symm)
      _ ≤ ∑ M ∈ Current.boundedFinset G Λ (2 * N), Fcap N M :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Current.boundedFinset_mono G Λ (by omega : N ≤ 2 * N))
            (fun M _ _ => hFcap_nonneg N M)
  -- Upper squeeze: `wsB N A · wsB N B ≤ ∑_{M ∈ B_{2N}} F`.
  have hUS : ∀ N : ℕ,
      CurrentBounded.weightSum G Λ N A β J * CurrentBounded.weightSum G Λ N B β J
        ≤ ∑ M ∈ Current.boundedFinset G Λ (2 * N), F M := by
    intro N
    rw [hLR N]
    exact Finset.sum_le_sum (fun M _ => hFcap_le_F N M)
  -- `F` is summable, with the uniform bound `(exp(β J)^|E|)²`.
  have hFsummable : Summable F := by
    refine summable_of_sum_le
      (c := Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet
        * Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet)
      hF_nonneg (fun s => ?_)
    set K : ℕ := s.sup (fun M => Finset.univ.sup M) with hK
    have hsub : s ⊆ Current.boundedFinset G Λ K := by
      intro M hM
      rw [Current.mem_boundedFinset_iff]
      exact fun e =>
        le_trans (Finset.le_sup (Finset.mem_univ e)) (Finset.le_sup hM)
    calc ∑ M ∈ s, F M
        ≤ ∑ M ∈ Current.boundedFinset G Λ K, F M :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun M _ _ => hF_nonneg M)
      _ ≤ CurrentBounded.weightSum G Λ K A β J
            * CurrentBounded.weightSum G Λ K B β J := hLS K
      _ ≤ Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet
            * Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet :=
          mul_le_mul (CurrentBounded.weightSum_le_exp_pow_card G Λ K A hβJ)
            (CurrentBounded.weightSum_le_exp_pow_card G Λ K B hβJ)
            (CurrentBounded.weightSum_nonneg G Λ K B hβJ)
            (pow_nonneg (Real.exp_pos _).le _)
  -- Doubling `N ↦ 2 N` is cofinal in `atTop`.
  have h2N : Filter.Tendsto (fun N : ℕ => 2 * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega)
      (fun b => ⟨b, by omega⟩)
  -- Left limit: `L(N) → weightSum A · weightSum B`.
  have key : Filter.Tendsto
      (fun N : ℕ => CurrentBounded.weightSum G Λ N A β J
        * CurrentBounded.weightSum G Λ N B β J)
      Filter.atTop
      (nhds (Current.weightSum G Λ A β J * Current.weightSum G Λ B β J)) := by
    rw [Current.weightSum_eq_iSup G Λ A hβJ, Current.weightSum_eq_iSup G Λ B hβJ]
    exact (CurrentBounded.tendsto_weightSum_atTop_iSup_of_nonneg G Λ A hβJ).mul
      (CurrentBounded.tendsto_weightSum_atTop_iSup_of_nonneg G Λ B hβJ)
  -- Right limit: `L(N) = R(N) → ∑' F` by the cap-free squeeze.
  have key2 : Filter.Tendsto
      (fun N : ℕ => CurrentBounded.weightSum G Λ N A β J
        * CurrentBounded.weightSum G Λ N B β J)
      Filter.atTop (nhds (∑' M, F M)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun N => ∑ M ∈ Current.boundedFinset G Λ N, F M)
      (h := fun N => ∑ M ∈ Current.boundedFinset G Λ (2 * N), F M)
      (Summable.tendsto_sum_boundedFinset G Λ hFsummable)
      ((Summable.tendsto_sum_boundedFinset G Λ hFsummable).comp h2N)
      (fun N => hLS N) (fun N => hUS N)
  exact tendsto_nhds_unique key key2

end Ambient
end IsingModel
