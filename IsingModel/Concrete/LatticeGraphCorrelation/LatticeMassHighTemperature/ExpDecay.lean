import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Inequalities.HighTemp
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointCorrelationInfinite

/-!
# Lattice mass at high temperature split — Step 110 high-temperature exponential decay

Part of the split high-temperature lattice-mass layer (Issue #1850).
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Step 110: High-temperature exponential decay (Simon 1980; Lieb 1980)

Lifts the ∞-volume Simon-Lieb inequality (Step 109) to an explicit
exponential decay rate: for `βJD < 1` (D = 2d), the two-point
correlation decays as `C · (βJD)^dist(i,j)` where `C = 1/(1-βJD)`.

References: B. Simon, *Correlation inequalities and the decay of correlations
in ferromagnets*, Comm. Math. Phys. 77 (1980), 111–126; E. H. Lieb, *A
refinement of Simon's correlation inequality*, Comm. Math. Phys. 77 (1980),
127–135. -/

/-- **Inductive bound (Step 110 core)**: at `h = 0`, `0 ≤ βJ`, `βJD < 1`
(D = 2d), for `i ≠ j` with `dist(i,j) ≥ n+1`:
`⟨σ_iσ_j⟩_∞ ≤ (βJD)^n · (βJD/(1-βJD))`.

Proof by induction on `n` (universalized over `i, j` for the IH):
- n = 0: per-stage `⟨σ_iσ_j⟩_n ≤ χ_n(i) ≤ βJD/(1-βJD)` (Step 106).
- n → n+1: `dist ≥ n+2 → ¬Adj` → Simon-Lieb (Step 109) + triangle + IH.

References: Simon 1980, Comm. Math. Phys. 77, 111–126; Lieb 1980, Comm. Math.
Phys. 77, 127–135. -/
private lemma correlationInfinite_latticeGraph_le_of_dist_ge
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J) (hlt : β * J * ↑(2 * d) < 1)
    {i j : Fin d → ℤ} (hij : i ≠ j)
    (n : ℕ) (hn : n + 1 ≤ IsingModel.latticeDistance d i j) :
    correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ (β * J * ↑(2 * d)) ^ n *
          (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) := by
  -- Universalize over (i, j) so the IH applies to neighbors (k, j)
  suffices h_univ : ∀ (n : ℕ) (i j : Fin d → ℤ), i ≠ j →
      n + 1 ≤ IsingModel.latticeDistance d i j →
      correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
        ≤ (β * J * ↑(2 * d)) ^ n *
            (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) from
    h_univ n i j hij hn
  intro n
  induction n with
  | zero =>
    intro i j hij _
    simp only [pow_zero, one_mul]
    rw [correlationInfinite_eq_ciSup]
    apply ciSup_le
    intro n'
    by_cases hA : ({i, j} : Finset _) ⊆ (Ambient.cubicExhaustion d).volume n'
    · have hi : i ∈ (Ambient.cubicExhaustion d).volume n' :=
        hA (Finset.mem_insert_self i {j})
      have hj : j ∈ (Ambient.cubicExhaustion d).volume n' :=
        hA (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self j)))
      rw [correlationAlongExhaustion_of_subset _ _ _ hA, correlationΛ_apply]
      have h_lift : liftFinset ({i, j} : Finset _) hA =
          ({⟨i, hi⟩, ⟨j, hj⟩} : Finset ↑((Ambient.cubicExhaustion d).volume n')) := by
        ext ⟨x, _⟩; simp [mem_liftFinset, Subtype.ext_iff]
      rw [h_lift]
      set G' := inducedGraph (IsingModel.latticeGraph d) ((Ambient.cubicExhaustion d).volume n')
      -- Nonnegativity of truncated2 from hβJ via random-current representation
      have hWpos : 0 < Current.weightSum (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume n') ∅ β J := by
        have hZ := IsingModel.partitionFunction_pos G' (⟨J, 0, β⟩ : IsingParams ℝ)
        rw [partitionFunction_inducedGraph_eq_pow_card_mul_weightSum_empty
            (IsingModel.latticeGraph d) _ hβJ] at hZ
        have h2 : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ↑((Ambient.cubicExhaustion d).volume n') :=
          by positivity
        exact (mul_pos_iff.mp hZ).elim (·.2) (fun h => absurd h2 (not_lt.mpr h.1.le))
      have h_trunc_nn : ∀ k : ↑((Ambient.cubicExhaustion d).volume n'),
          0 ≤ truncated2 G' (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩ k := fun k => by
        classical
        rw [truncated2_h_zero, correlation_inducedGraph_eq_weightSum_ratio _ _ hβJ]
        exact div_nonneg (Current.weightSum_nonneg _ _ _ hβJ) hWpos.le
      -- corr{⟨i,hi⟩,⟨j,hj⟩} ≤ ∑_k trunc2(⟨i,hi⟩,k) = suscept ≤ βJD/(1-βJD)
      calc IsingModel.correlation G' (⟨J, 0, β⟩ : IsingParams ℝ) {⟨i, hi⟩, ⟨j, hj⟩}
            = truncated2 G' (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩ ⟨j, hj⟩ :=
              (truncated2_h_zero G' J β ⟨i, hi⟩ ⟨j, hj⟩).symm
          _ ≤ ∑ k : ↑((Ambient.cubicExhaustion d).volume n'),
                truncated2 G' (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩ k :=
              Finset.single_le_sum (fun k _ => h_trunc_nn k) (Finset.mem_univ _)
          _ = IsingModel.susceptibility G' (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩ :=
              (susceptibility_apply G' (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩).symm
          _ = susceptibilityAlongExhaustion (IsingModel.latticeGraph d)
                (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) i n' :=
              (susceptibilityAlongExhaustion_of_mem (IsingModel.latticeGraph d)
                (Ambient.cubicExhaustion d) _ hi).symm
          _ ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
              susceptibilityAlongExhaustion_latticeGraph_le_of_high_temp hβJ hlt i n'
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ hA]
      exact div_nonneg (mul_nonneg hβJ (Nat.cast_nonneg _)) (by linarith)
  | succ n ih =>
    -- ih : ∀ i j, i ≠ j → n + 1 ≤ dist d i j → corr{i,j} ≤ (βJD)^n * bound
    intro i j hij hn
    -- dist(i,j) ≥ n+2 ≥ 2 → ¬Adj i j
    have hnadj : ¬(IsingModel.latticeGraph d).Adj i j := by
      rw [IsingModel.latticeGraph_adj_iff_latticeDistance_eq_one]; omega
    -- Apply Simon-Lieb (Step 109)
    apply (correlationInfinite_simon_lieb_latticeGraph hβJ hij hnadj).trans
    -- Bound each neighbor term via IH, then sum ≤ D · bound
    have h_each : ∀ k ∈ (IsingModel.latticeGraph d).neighborFinset i,
        correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {k, j}
          ≤ (β * J * ↑(2 * d)) ^ n *
              (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) := by
      intro k hk
      have hk_adj := (SimpleGraph.mem_neighborFinset _ _ _).mp hk
      have hik_dist : IsingModel.latticeDistance d i k = 1 :=
        (IsingModel.latticeGraph_adj_iff_latticeDistance_eq_one d i k).mp hk_adj
      have h_tri : n + 1 ≤ IsingModel.latticeDistance d k j := by
        have htri := IsingModel.latticeDistance_triangle d i k j
        rw [hik_dist] at htri; omega
      have hkj : k ≠ j := by
        intro heq; rw [heq, IsingModel.latticeDistance_self] at h_tri; omega
      exact ih k j hkj h_tri
    have hdeg : ((IsingModel.latticeGraph d).neighborFinset i).card ≤ 2 * d := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact latticeGraph_degree_le d i
    have h_pow_nn := pow_nonneg (mul_nonneg hβJ (Nat.cast_nonneg (2 * d))) n
    have h_bound_nn := div_nonneg (mul_nonneg hβJ (Nat.cast_nonneg (2 * d)))
        (by linarith : (0 : ℝ) ≤ 1 - β * J * ↑(2 * d))
    calc β * J * ∑ k ∈ (IsingModel.latticeGraph d).neighborFinset i,
              correlationInfinite _ _ _ {k, j}
        ≤ β * J * ∑ k ∈ (IsingModel.latticeGraph d).neighborFinset i,
              (β * J * ↑(2 * d)) ^ n *
                (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum h_each) hβJ
      _ = β * J * ((IsingModel.latticeGraph d).neighborFinset i).card *
              (β * J * ↑(2 * d)) ^ n *
              (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ β * J * ↑(2 * d) * (β * J * ↑(2 * d)) ^ n *
              (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (by exact_mod_cast hdeg) hβJ) h_pow_nn)
              h_bound_nn
      _ = (β * J * ↑(2 * d)) ^ (n + 1) *
              (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) := by rw [pow_succ]; ring

open IsingModel in
/-- **High-temperature exponential decay** (Simon 1980;
Lieb 1980): for the `d`-dimensional lattice graph
with cubic exhaustion, `0 ≤ βJ`, and `βJD < 1` (D = 2d),
`HasExponentialDecay d (cubicExhaustion d) ⟨J,0,β⟩ (-log(βJD))`.

Witness constant `C = 1/(1-βJD)`. The inductive lemma
`correlationInfinite_latticeGraph_le_of_dist_ge` gives
`⟨σ_iσ_j⟩_∞ ≤ C · (βJD)^dist(i,j)`,
and `(βJD)^n ≤ exp(log(βJD) · n) = exp(-(-log βJD) · n)` closes the bound.

**Edge case**: when `βJD = 0` (i.e., `J = 0` or `β = 0`), Lean's convention
`Real.log 0 = 0` gives rate `0` (trivial bound `C · 1`) rather than the
textbook's physically-infinite mass.  The statement remains valid (the bound
`|⟨σ_iσ_j⟩_∞| ≤ C` follows from the inductive lemma at `βJD = 0`),
and the physically meaningful regime is `0 < βJD < 1`.

References: Simon 1980, Comm. Math. Phys. 77, 111–126; Lieb 1980, Comm. Math.
Phys. 77, 127–135. -/
theorem hasExponentialDecay_of_high_temp
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hlt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        (-Real.log (β * J * ↑(2 * d))) := by
  set βJD := β * J * ↑(2 * d) with hβJD_def
  have hβJDnn : 0 ≤ βJD := mul_nonneg hβJ (Nat.cast_nonneg _)
  refine ⟨1 / (1 - βJD), div_nonneg zero_le_one (by linarith), fun i j hij => ?_⟩
  rw [truncated2Infinite_h_zero (latticeGraph d) (cubicExhaustion d) J β i j]
  rw [abs_of_nonneg (correlationInfinite_nonneg_of_hβJ (latticeGraph d)
      (cubicExhaustion d) hβJ {i, j})]
  set N := latticeDistance d i j
  have hN_pos : 0 < N := by
    rw [Nat.pos_iff_ne_zero]
    exact fun h => hij ((latticeDistance_eq_zero_iff d i j).mp h)
  have h_ind : correlationInfinite (latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ βJD ^ (N - 1) * (βJD / (1 - βJD)) :=
    correlationInfinite_latticeGraph_le_of_dist_ge hβJ hlt hij (N - 1) (by omega)
  have h_C_pow : βJD ^ (N - 1) * (βJD / (1 - βJD)) = 1 / (1 - βJD) * βJD ^ N := by
    rw [← mul_div_assoc, ← pow_succ, Nat.sub_add_cancel hN_pos]; ring
  -- (βJD)^N ≤ exp(log βJD * N) = exp(-(-log βJD) * N)
  have h_pow_le_exp : βJD ^ N ≤ Real.exp (Real.log βJD * ↑N) := by
    by_cases hβJD0 : βJD = 0
    · simp [hβJD0, zero_pow hN_pos.ne', Real.log_zero]
    · have hpos : 0 < βJD := lt_of_le_of_ne hβJDnn (Ne.symm hβJD0)
      rw [mul_comm, ← Real.log_pow, Real.exp_log (pow_pos hpos N)]
  calc correlationInfinite (latticeGraph d) (cubicExhaustion d) _ {i, j}
      ≤ βJD ^ (N - 1) * (βJD / (1 - βJD)) := h_ind
    _ = 1 / (1 - βJD) * βJD ^ N := h_C_pow
    _ ≤ 1 / (1 - βJD) * Real.exp (Real.log βJD * ↑N) :=
          mul_le_mul_of_nonneg_left h_pow_le_exp (div_nonneg zero_le_one (by linarith))
    _ = 1 / (1 - βJD) * Real.exp (-(-Real.log βJD) * ↑N) := by simp [neg_neg]


end Ambient
end IsingModel
