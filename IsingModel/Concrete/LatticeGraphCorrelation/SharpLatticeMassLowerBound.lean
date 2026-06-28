import IsingModel.Inequalities.SharpSimonLiebNeighbor
import IsingModel.Inequalities.HighTemp.SimonLiebInfinite
import IsingModel.Concrete.LatticeGraphCorrelation.SimonLiebDistanceDecay
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.PosAndAntitone

/-!
# Sharp `tanh`-coefficient lattice-mass lower bound (GJ §17.5 / §18 / FFS Ch 12)

The infinite-volume completion (**brick 4**) of the sharp-decay programme (#4393).  Composing the
sharp finite Simon-Lieb inequality (`correlation_inducedGraph_simon_lieb_neighbor_sharp`, brick 2)
through the exhaustion limit gives the **infinite-volume sharp Simon-Lieb** inequality, hence the
sharp exponential decay of the infinite-volume two-point function
`⟨φ_i φ_j⟩_∞ ≤ (2d·tanh βJ)^{dist(i,j)−1}`, and therefore the **sharp lattice-mass lower bound**

`latticeMass(σ) ≥ ofReal(−log(2d·tanh βJ))`,

sharper than the Simon-Lieb `−log(βJ·2d)` (since `tanh βJ < βJ`).  This tightens the GJ §17.5
Lemma 17.5.2 sandwich constant; the residual `log(2d)` gap to the upper bound `−log tanh` needs the
Ornstein–Zernike exact rate (#4386), so this does not by itself close Theorem 17.5.1.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5, §18.
* Fernández–Fröhlich–Sokal, *Random Walks…* (1992), Ch 12.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel

namespace Ambient

open Finset

variable {V : Type*} [DecidableEq V]

/-- **Infinite-volume sharp Simon-Lieb inequality** (FFS Ch 12 / GJ §18): for `0 ≤ β·J`, distinct
non-adjacent `i ≠ j`,
`⟨φ_iφ_j⟩_∞ ≤ tanh(βJ)·∑_{k ∼ i} ⟨φ_kφ_j⟩_∞`.
Sharper than `correlationInfinite_simon_lieb` (coefficient `β·J ≥ tanh βJ`).  Proof: pass the sharp
finite neighbour inequality (`correlation_inducedGraph_simon_lieb_neighbor_sharp`, brick 2) through
`correlationInfinite_eq_ciSup`; at each stage the finite neighbour kernel `K(j,u) = ⟨φ_uφ_j⟩` is
dominated by the infinite-volume `⟨φ_{u}φ_j⟩_∞`, and the induced-graph neighbours inject into the
`G`-neighbours of `i` (the missing terms are nonnegative). -/
theorem correlationInfinite_simon_lieb_sharp
    (G : SimpleGraph V) [G.LocallyFinite] (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    {i j : V} (hij : i ≠ j) (hnadj : ¬ G.Adj i j) :
    correlationInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ Real.tanh (β * J) * ∑ k ∈ G.neighborFinset i,
          correlationInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {k, j} := by
  classical
  have ht0 : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  rw [correlationInfinite_eq_ciSup]
  apply ciSup_le
  intro n
  by_cases hA : ({i, j} : Finset V) ⊆ Λ.volume n
  · have hi : i ∈ Λ.volume n := hA (Finset.mem_insert_self i {j})
    have hj : j ∈ Λ.volume n :=
      hA (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self j)))
    rw [correlationAlongExhaustion_of_subset G Λ _ hA, correlationΛ_apply]
    have h_lift : liftFinset ({i, j} : Finset V) hA
        = ({⟨i, hi⟩, ⟨j, hj⟩} : Finset ↑(Λ.volume n)) := by
      ext ⟨x, _⟩; simp [mem_liftFinset, Subtype.ext_iff]
    rw [h_lift]
    have hij' : (⟨i, hi⟩ : ↑(Λ.volume n)) ≠ ⟨j, hj⟩ :=
      fun h => hij (congr_arg Subtype.val h)
    refine le_trans (correlation_inducedGraph_simon_lieb_neighbor_sharp G (Λ.volume n) hβJ hij') ?_
    apply mul_le_mul_of_nonneg_left _ ht0
    calc ∑ u ∈ (inducedGraph G (Λ.volume n)).neighborFinset ⟨i, hi⟩,
            simonLiebKernel G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) ⟨j, hj⟩ u
        ≤ ∑ u ∈ (inducedGraph G (Λ.volume n)).neighborFinset ⟨i, hi⟩,
            correlationInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {u.val, j} := by
          apply Finset.sum_le_sum
          intro u hu
          have hadj : (inducedGraph G (Λ.volume n)).Adj ⟨i, hi⟩ u := by
            rwa [SimpleGraph.mem_neighborFinset] at hu
          have hadjG : G.Adj i u.val := hadj
          have huj : u ≠ (⟨j, hj⟩ : ↑(Λ.volume n)) := by
            intro h
            exact hnadj (by rw [h] at hadjG; exact hadjG)
          rw [simonLiebKernel_of_ne G (Λ.volume n) _ huj]
          have h_uj_sub : ({u.val, j} : Finset V) ⊆ Λ.volume n :=
            Finset.insert_subset_iff.mpr ⟨u.prop, Finset.singleton_subset_iff.mpr hj⟩
          have h_lift2 : liftFinset ({u.val, j} : Finset V) h_uj_sub
              = ({u, (⟨j, hj⟩ : ↑(Λ.volume n))} : Finset ↑(Λ.volume n)) := by
            ext ⟨x, _⟩; simp [mem_liftFinset, Subtype.ext_iff]
          have h_corr_eq :
              correlation (inducedGraph G (Λ.volume n)) (⟨J, 0, β⟩ : IsingParams ℝ)
                  ({u, (⟨j, hj⟩ : ↑(Λ.volume n))} : Finset ↑(Λ.volume n))
                = correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {u.val, j} n := by
            rw [correlationAlongExhaustion_of_subset G Λ _ h_uj_sub, correlationΛ_apply, h_lift2]
          rw [h_corr_eq]
          exact correlationAlongExhaustion_le_correlationInfinite G Λ _ {u.val, j} n
      _ = ∑ k ∈ ((inducedGraph G (Λ.volume n)).neighborFinset ⟨i, hi⟩).image (·.val),
            correlationInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {k, j} := by
          rw [Finset.sum_image]
          intro a _ b _ h
          exact Subtype.val_injective h
      _ ≤ ∑ k ∈ G.neighborFinset i,
            correlationInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {k, j} := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            rw [Finset.mem_image] at hk
            obtain ⟨u, hu, rfl⟩ := hk
            rw [SimpleGraph.mem_neighborFinset] at hu
            rw [G.mem_neighborFinset]
            exact hu
          · exact fun k _ _ => correlationInfinite_nonneg_of_hβJ G Λ hβJ {k, j}
  · rw [correlationAlongExhaustion_of_not_subset G Λ _ hA]
    exact mul_nonneg ht0
      (Finset.sum_nonneg fun k _ => correlationInfinite_nonneg_of_hβJ G Λ hβJ {k, j})

/-- **ℤ^d infinite-volume sharp Simon-Lieb**: the lattice-graph instance of
`correlationInfinite_simon_lieb_sharp`. -/
theorem correlationInfinite_simon_lieb_latticeGraph_sharp
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    {i j : Fin d → ℤ} (hij : i ≠ j) (hnadj : ¬ (latticeGraph d).Adj i j) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ Real.tanh (β * J) * ∑ k ∈ (latticeGraph d).neighborFinset i,
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {k, j} :=
  correlationInfinite_simon_lieb_sharp (latticeGraph d) (cubicExhaustion d) hβJ hij hnadj

/-- **Sharp one-step decay for non-adjacent pairs**: if every neighbour `k ∼ i` has
`⟨φ_kφ_j⟩_∞ ≤ C`, then `⟨φ_iφ_j⟩_∞ ≤ tanh(βJ)·2d·C` (`2d` the lattice degree bound).  Sharp version
of `correlationInfinite_latticeGraph_le_of_neighbors_le`. -/
theorem correlationInfinite_latticeGraph_le_of_neighbors_le_sharp
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    {i j : Fin d → ℤ} (hij : i ≠ j) (hnadj : ¬ (latticeGraph d).Adj i j)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k ∈ (latticeGraph d).neighborFinset i,
      correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {k, j} ≤ C) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ Real.tanh (β * J) * (2 * d) * C := by
  have ht0 : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  have hsum : ∑ k ∈ (latticeGraph d).neighborFinset i,
      correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {k, j}
      ≤ (((latticeGraph d).neighborFinset i).card : ℝ) * C := by
    calc ∑ k ∈ (latticeGraph d).neighborFinset i,
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {k, j}
        ≤ ∑ _k ∈ (latticeGraph d).neighborFinset i, C := Finset.sum_le_sum hC
      _ = (((latticeGraph d).neighborFinset i).card : ℝ) * C := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((latticeGraph d).neighborFinset i).card : ℝ) ≤ 2 * d := by
    have hdeg := latticeGraph_degree_le d i
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
    calc (((latticeGraph d).neighborFinset i).card : ℝ)
        ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast hdeg
      _ = 2 * d := by push_cast; ring
  calc correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ Real.tanh (β * J) * ∑ k ∈ (latticeGraph d).neighborFinset i,
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {k, j} :=
        correlationInfinite_simon_lieb_latticeGraph_sharp hβJ hij hnadj
    _ ≤ Real.tanh (β * J) * ((((latticeGraph d).neighborFinset i).card : ℝ) * C) :=
        mul_le_mul_of_nonneg_left hsum ht0
    _ ≤ Real.tanh (β * J) * ((2 * d) * C) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hC0) ht0
    _ = Real.tanh (β * J) * (2 * d) * C := by ring

/-- **Sharp `tanh` exponential decay of the infinite-volume two-point function** (FFS Ch 12 / GJ
§18): for `0 ≤ β·J`, distinct `i, j` with `n + 1 ≤ dist(i,j)`,
`⟨φ_iφ_j⟩_∞ ≤ (2d·tanh βJ)^n`.  Sharp version of
`correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_dist_gt`; induction on `n` via the sharp
one-step bound. -/
theorem correlationInfinite_latticeGraph_le_tanh_two_d_pow_of_dist_gt
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J) :
    ∀ (n : ℕ) (i j : Fin d → ℤ), n + 1 ≤ latticeDistance d i j →
      correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
        ≤ (Real.tanh (β * J) * (2 * d)) ^ n := by
  have ht0 : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  have hbase : (0 : ℝ) ≤ Real.tanh (β * J) * (2 * d) := mul_nonneg ht0 (by positivity)
  intro n
  induction n with
  | zero =>
    intro i j _
    simpa using correlationInfinite_le_one (latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
  | succ m ih =>
    intro i j hdist
    have hij : i ≠ j := by
      intro h; rw [h, latticeDistance_self] at hdist; omega
    have hnadj : ¬ (latticeGraph d).Adj i j := by
      rw [latticeGraph_adj_iff_latticeDistance_eq_one]; omega
    have hC : ∀ k ∈ (latticeGraph d).neighborFinset i,
        correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {k, j} ≤ (Real.tanh (β * J) * (2 * d)) ^ m := by
      intro k hk
      rw [SimpleGraph.mem_neighborFinset] at hk
      have hik1 : latticeDistance d i k = 1 :=
        (latticeGraph_adj_iff_latticeDistance_eq_one d i k).mp hk
      have htri : latticeDistance d i j ≤ latticeDistance d i k + latticeDistance d k j :=
        latticeDistance_triangle d i k j
      exact ih k j (by omega)
    have h := correlationInfinite_latticeGraph_le_of_neighbors_le_sharp hβJ hij hnadj
      (pow_nonneg hbase m) hC
    calc correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
        ≤ Real.tanh (β * J) * (2 * d) * (Real.tanh (β * J) * (2 * d)) ^ m := h
      _ = (Real.tanh (β * J) * (2 * d)) ^ (m + 1) := by rw [pow_succ]; ring

/-- **Sharp `tanh` exponential decay (HasExponentialDecay form)** (FFS Ch 12 / GJ §18): for `d ≥ 1`,
`0 < β·J`, the truncated two-point function satisfies the rate-`−log(tanh βJ · 2d)` decay bound (a
genuine decay rate in the high-temperature regime `tanh βJ · 2d < 1`).  Built from
`correlationInfinite_latticeGraph_le_tanh_two_d_pow_of_dist_gt` at `n = dist − 1`, with
`C = 1/(tanh βJ · 2d)`. -/
theorem hasExponentialDecay_tanh_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    HasExponentialDecay d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        (-Real.log (Real.tanh (β * J) * (2 * d))) := by
  have hβJ : 0 < β * J := mul_pos hβ hJ
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβJ) (Real.cosh_pos _)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hr_pos : 0 < Real.tanh (β * J) * (2 * d) := mul_pos htanh_pos (by positivity)
  refine ⟨1 / (Real.tanh (β * J) * (2 * d)),
    div_nonneg zero_le_one hr_pos.le, fun i j hij => ?_⟩
  rw [truncated2Infinite_h_zero (latticeGraph d) (cubicExhaustion d) J β i j]
  rw [abs_of_nonneg (correlationInfinite_nonneg_of_hβJ (latticeGraph d) (cubicExhaustion d)
    hβJ.le {i, j})]
  have hN_pos : 0 < latticeDistance d i j := by
    rw [Nat.pos_iff_ne_zero]
    exact fun h => hij ((latticeDistance_eq_zero_iff d i j).mp h)
  have h_ind : correlationInfinite (latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
        ≤ (Real.tanh (β * J) * (2 * d)) ^ (latticeDistance d i j - 1) :=
    correlationInfinite_latticeGraph_le_tanh_two_d_pow_of_dist_gt hβJ.le
      (latticeDistance d i j - 1) i j (by omega)
  generalize hN : latticeDistance d i j = N at h_ind hN_pos ⊢
  have key : (Real.tanh (β * J) * (2 * d)) * (Real.tanh (β * J) * (2 * d)) ^ (N - 1)
      = (Real.tanh (β * J) * (2 * d)) ^ N := by
    rw [← pow_succ']
    congr 1
    omega
  have h_C_pow : (Real.tanh (β * J) * (2 * d)) ^ (N - 1)
      = 1 / (Real.tanh (β * J) * (2 * d)) * (Real.tanh (β * J) * (2 * d)) ^ N := by
    rw [← key, one_div, ← mul_assoc (Real.tanh (β * J) * (2 * d))⁻¹
        (Real.tanh (β * J) * (2 * d)) ((Real.tanh (β * J) * (2 * d)) ^ (N - 1)),
      inv_mul_cancel₀ hr_pos.ne', one_mul]
  have h_pow_le_exp : (Real.tanh (β * J) * (2 * d)) ^ N
      ≤ Real.exp (Real.log (Real.tanh (β * J) * (2 * d)) * (N : ℝ)) :=
    le_of_eq (by
      rw [mul_comm (Real.log (Real.tanh (β * J) * (2 * d))) (N : ℝ), ← Real.log_pow,
        Real.exp_log (pow_pos hr_pos N)])
  calc correlationInfinite (latticeGraph d) (cubicExhaustion d) _ {i, j}
      ≤ (Real.tanh (β * J) * (2 * d)) ^ (N - 1) := h_ind
    _ = 1 / (Real.tanh (β * J) * (2 * d)) * (Real.tanh (β * J) * (2 * d)) ^ N := h_C_pow
    _ ≤ 1 / (Real.tanh (β * J) * (2 * d))
          * Real.exp (Real.log (Real.tanh (β * J) * (2 * d)) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left h_pow_le_exp (by positivity)
    _ = 1 / (Real.tanh (β * J) * (2 * d))
          * Real.exp (-(-Real.log (Real.tanh (β * J) * (2 * d))) * (N : ℝ)) := by simp [neg_neg]

/-- **Sharp `tanh` lattice-mass lower bound** (GJ §17.5 / §18, brick 4 of #4393): for `d ≥ 1`,
`0 < β·J`, and `2d·tanh βJ < 1`,
`ofReal(−log(2d·tanh βJ)) ≤ latticeMass(σ)`.
Sharper than `latticeMass_ge_neg_log_of_high_temp` (rate `−log(βJ·2d)`, since `tanh βJ < βJ`); the
rate `−log(2d·tanh βJ)` lies in the defining set of `latticeMass`.  This tightens the GJ §17.5
Lemma 17.5.2 sandwich constant toward Theorem 17.5.1 (#4386); the residual `log(2d)` gap to the
upper bound `−log tanh` needs the Ornstein–Zernike exact rate. -/
theorem latticeMass_ge_neg_log_tanh_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    (hlt : Real.tanh (β * J) * (2 * d) < 1) :
    ENNReal.ofReal (-Real.log (Real.tanh (β * J) * (2 * d))) ≤
      latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have hβJ : 0 < β * J := mul_pos hβ hJ
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβJ) (Real.cosh_pos _)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hr_pos : 0 < Real.tanh (β * J) * (2 * d) := mul_pos htanh_pos (by positivity)
  have hα_pos : 0 < -Real.log (Real.tanh (β * J) * (2 * d)) :=
    neg_pos.mpr (Real.log_neg hr_pos hlt)
  unfold latticeMass
  set α₀ : NNReal := ⟨-Real.log (Real.tanh (β * J) * (2 * d)), hα_pos.le⟩
  apply le_sSup
  exact ⟨α₀, hasExponentialDecay_tanh_of_high_temp hd hβ hJ,
    (ENNReal.ofReal_eq_coe_nnreal hα_pos.le).symm⟩

end Ambient

end IsingModel
