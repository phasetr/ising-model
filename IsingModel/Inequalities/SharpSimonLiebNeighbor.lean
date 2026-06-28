import IsingModel.Conditioning.CorrelationClosed.SharpSimonLieb
import IsingModel.Inequalities.SimonLiebKernel
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Sharp `tanh`-coefficient neighbour Simon-Lieb inequality (GJ §18 / FFS Ch 12)

The neighbour-vertex form of the sharp edge inequality `correlation_simon_lieb_sharp`: for
`0 ≤ β·J`, distinct `i ≠ j ∈ Λ`,

`⟨σ_i σ_j⟩ ≤ tanh(βJ) · ∑_{u ∈ neighborFinset i} K(j, u)`,

with `K = simonLiebKernel` the transfer kernel (`K(j,u) = ⟨σ^{ {i,j}△{i,u} }⟩`, and `= 1` at
`u = j`).
**Sharper** than the random-current `correlation_inducedGraph_simon_lieb_neighbor` (coefficient
`β·J ≥ tanh βJ`).  This is **brick 2** of the sharp-decay programme (#4393): it is the one-step
transfer form consumed by the distance iteration toward
`latticeMass ≥ ofReal(−log(2d·tanh βJ))` (#4386).

Proof: apply the sharp edge inequality at `G = inducedGraph G Λ`, then reindex its edge sum
`∑_{e ∋ i}` to the neighbour sum `∑_{u ∼ i}` via `Finset.sum_bij'` (`e ↦` other endpoint), with
the per-edge value identity `correlation_symmDiff_eq_simonLiebKernel` — identical to the
random-current neighbour proof, only the coefficient differs.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.
* Fernández–Fröhlich–Sokal, *Random Walks…* (1992), Ch 12.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*}

/-- **Sharp `tanh`-coefficient neighbour Simon-Lieb inequality** (GJ §18 / FFS Ch 12): for `0 ≤ β·J`
and distinct `i ≠ j ∈ Λ`,
`⟨σ_iσ_j⟩ ≤ tanh(βJ) · ∑_{u ∈ neighborFinset i} simonLiebKernel G Λ ⟨J,0,β⟩ j u`.
Sharper than `correlation_inducedGraph_simon_lieb_neighbor` (coefficient `β·J ≥ tanh βJ`); the edge
sum of `correlation_simon_lieb_sharp` is reindexed to the neighbour sum via `Finset.sum_bij'`. -/
theorem correlation_inducedGraph_simon_lieb_neighbor_sharp (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    {β J : ℝ} (hβJ : 0 ≤ β * J) {i j : ↑Λ} (hij : i ≠ j) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ Real.tanh (β * J) * ∑ u ∈ (inducedGraph G Λ).neighborFinset i,
          simonLiebKernel G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j u := by
  classical
  have ht0 : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  refine le_trans (correlation_simon_lieb_sharp (inducedGraph G Λ) hβJ (i := i) (j := j)) ?_
  apply mul_le_mul_of_nonneg_left _ ht0
  apply le_of_eq
  refine Finset.sum_bij'
    (fun e he => Sym2.Mem.other ((Finset.mem_filter.mp he).2))
    (fun u hu => s(i, u))
    ?_ ?_ ?_ ?_ ?_
  · -- forward maps into neighborFinset
    intro e he
    have h2 : i ∈ (e : Sym2 ↑Λ) := (Finset.mem_filter.mp he).2
    rw [SimpleGraph.mem_neighborFinset, ← SimpleGraph.mem_edgeSet, Sym2.other_spec h2,
      ← SimpleGraph.mem_edgeFinset]
    exact (Finset.mem_filter.mp he).1
  · -- backward maps into edge filter
    intro u hu
    have hadj : (inducedGraph G Λ).Adj i u := by rwa [SimpleGraph.mem_neighborFinset] at hu
    refine Finset.mem_filter.mpr ⟨?_, Sym2.mem_mk_left i u⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hadj
  · -- left inverse
    intro e he
    exact Sym2.other_spec ((Finset.mem_filter.mp he).2)
  · -- right inverse
    intro u hu
    have hadj : (inducedGraph G Λ).Adj i u := by rwa [SimpleGraph.mem_neighborFinset] at hu
    have hspec : s(i, Sym2.Mem.other (Sym2.mem_mk_left i u)) = s(i, u) :=
      Sym2.other_spec (Sym2.mem_mk_left i u)
    rw [Sym2.eq_iff] at hspec
    rcases hspec with ⟨_, h⟩ | ⟨hiu, _⟩
    · exact h
    · exact absurd hiu hadj.ne
  · -- values agree via the per-edge kernel identity
    intro e he
    have hmem : e ∈ (inducedGraph G Λ).edgeSet :=
      SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp he).1
    exact correlation_symmDiff_eq_simonLiebKernel G Λ (⟨J, 0, β⟩ : IsingParams ℝ) hij
      ⟨e, hmem⟩ ((Finset.mem_filter.mp he).2)

set_option linter.unusedDecidableInType false in
/-- **Distance-localised sharp geometric bound** (FFS Ch 12 / GJ §18): if the target `j` is more
than `n` graph-steps from `i` (`n < dist i j`), then `⟨σ_iσ_j⟩ ≤ (tanh(βJ)·D)^n` (`D` a
degree bound).  Induction on `n` via the sharp neighbour inequality
`correlation_inducedGraph_simon_lieb_neighbor_sharp`: the base (`0 < dist`) is `⟨σ_iσ_j⟩ ≤ 1`; for
`n+1`, `dist i j > n+1` forces `i ≠ j` and every neighbour `u ∼ i` still has `dist u j > n`
(`Adj.diff_dist_adj`), so each kernel term `K(j,u) = ⟨σ_uσ_j⟩` is `≤ (tanh·D)^n` by the IH, and the
`≤ D` neighbours times `tanh` give `(tanh·D)^{n+1}`. -/
theorem correlation_inducedGraph_le_tanh_pow_of_lt_dist (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    {D : ℕ} (hD : ∀ v : ↑Λ, ((inducedGraph G Λ).neighborFinset v).card ≤ D)
    (j : ↑Λ) (n : ℕ) (i : ↑Λ) (hdist : n < (inducedGraph G Λ).dist i j) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ (Real.tanh (β * J) * (D : ℝ)) ^ n := by
  have ht0 : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  have htD : 0 ≤ Real.tanh (β * J) * (D : ℝ) := mul_nonneg ht0 (Nat.cast_nonneg D)
  induction n generalizing i with
  | zero =>
    rw [pow_zero]
    exact (abs_le.mp (abs_correlation_le_one (inducedGraph G Λ) _ {i, j})).2
  | succ n ih =>
    have hij : i ≠ j := by
      rintro rfl
      rw [SimpleGraph.dist_self] at hdist
      exact absurd hdist (by omega)
    refine le_trans (correlation_inducedGraph_simon_lieb_neighbor_sharp G Λ hβJ hij) ?_
    calc Real.tanh (β * J) * ∑ u ∈ (inducedGraph G Λ).neighborFinset i,
            simonLiebKernel G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j u
        ≤ Real.tanh (β * J) * ∑ _u ∈ (inducedGraph G Λ).neighborFinset i,
            (Real.tanh (β * J) * (D : ℝ)) ^ n := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu => ?_) ht0
          have hadj : (inducedGraph G Λ).Adj i u := by
            rwa [SimpleGraph.mem_neighborFinset] at hu
          have htri := hadj.diff_dist_adj (u := j)
          have hdu : n < (inducedGraph G Λ).dist u j := by
            rw [SimpleGraph.dist_comm] at hdist ⊢
            omega
          have huj : u ≠ j := by
            rintro rfl
            rw [SimpleGraph.dist_self] at hdu
            exact absurd hdu (by omega)
          rw [simonLiebKernel_of_ne G Λ _ huj]
          exact ih u hdu
      _ = Real.tanh (β * J) * (((inducedGraph G Λ).neighborFinset i).card
            * (Real.tanh (β * J) * (D : ℝ)) ^ n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.tanh (β * J) * ((D : ℝ) * (Real.tanh (β * J) * (D : ℝ)) ^ n) := by
          refine mul_le_mul_of_nonneg_left ?_ ht0
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hD i) (pow_nonneg htD n)
      _ = (Real.tanh (β * J) * (D : ℝ)) ^ (n + 1) := by rw [pow_succ]; ring

set_option linter.unusedDecidableInType false in
/-- **Sharp `tanh`-coefficient exponential decay of the two-point function** (FFS Ch 12 / GJ §18):
for `0 ≤ β·J`, a degree bound `D`, and distinct reachable `i, j` (`0 < dist i j`),
`⟨σ_iσ_j⟩ ≤ (tanh(βJ)·D)^{dist(i,j)−1}`.  Sharper than `correlation_inducedGraph_le_pow_dist`
(coefficient `β·J·D`), giving the rate `−log(tanh(βJ)·D)` (with `D = 2d` on `ℤ^d`, the rate
`−log(2d·tanh βJ)`).  Specialises `correlation_inducedGraph_le_tanh_pow_of_lt_dist` at
`n = dist(i,j) − 1`. -/
theorem correlation_inducedGraph_le_tanh_pow_dist (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    {D : ℕ} (hD : ∀ v : ↑Λ, ((inducedGraph G Λ).neighborFinset v).card ≤ D)
    {i j : ↑Λ} (hdist : 0 < (inducedGraph G Λ).dist i j) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ (Real.tanh (β * J) * (D : ℝ)) ^ ((inducedGraph G Λ).dist i j - 1) := by
  have hlt : (inducedGraph G Λ).dist i j - 1 < (inducedGraph G Λ).dist i j := by omega
  exact correlation_inducedGraph_le_tanh_pow_of_lt_dist G Λ hβJ hD j _ i hlt

end Ambient

end IsingModel
