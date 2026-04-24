import IsingModel.AmbientLattice
import IsingModel.Inequalities.SimonLieb
import IsingModel.Concrete.LatticeGraphBED

/-!
# High-temperature susceptibility bound (GJ §5.1 / FV §3.7.3)

Lifts the finite-volume Simon-Lieb bound
`correlation_sum_le_of_high_temp` (step 105)
to the infinite-volume susceptibility `susceptibilityInfinite`.

Four main results plus a ℤ^d concrete instance:
1. `edgeFilter_card_eq_degree` (private) — filter.card of incident edges = degree.
2. `susceptibilityΛ_le_of_high_temp` — finite-volume: χ_Λ ≤ βJD/(1-βJD).
3. `susceptibilityAlongExhaustion_le_of_high_temp` — per-stage bound.
4. `susceptibilityInfinite_le_of_high_temp` — infinite-volume via ciSup_le.
5. `susceptibilityInfinite_latticeGraph_le_of_high_temp` — ℤ^d concrete.

References: Glimm–Jaffe §5.1 pp. 73–74; Friedli–Velenik §3.7.3.
-/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

/-- **Filter-card equals degree**: the number of edges of `G` incident to `v`
(counted as a filter over `G.edgeSet` subtypes) equals `G.degree v`.
Proof: bijection with `G.incidenceFinset v` via `e ↦ e.val`,
using `SimpleGraph.edge_mem_incidenceSet_iff`. -/
private lemma edgeFilter_card_eq_degree
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] [Fintype G.edgeSet] (v : V) :
    (Finset.univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V))).card = G.degree v := by
  rw [← G.card_incidenceFinset_eq_degree]
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [G.mem_incidenceFinset, G.edge_mem_incidenceSet_iff]
    exact he
  · intro e1 _ e2 _ h; exact Subtype.val_injective h
  · intro e he
    rw [G.mem_incidenceFinset] at he
    simp only [SimpleGraph.incidenceSet, Set.mem_setOf_eq] at he
    exact ⟨⟨e, he.1⟩, by simp [Finset.mem_filter, he.2], rfl⟩

set_option maxHeartbeats 400000 in
-- `suffices aux ... from aux` (susceptibilityΛ ≡ ∑ j, truncated2) requires whnf unfolding
-- of `noncomputable def` layers that exceeds the default 200000-heartbeat limit.
/-- **Finite-volume high-temperature susceptibility bound** (Simon-Lieb iteration):
for `h = 0`, `0 ≤ βJ`, and `D` bounding the incident-edge count of every vertex in `Λ`,
if `βJD < 1` then `susceptibilityΛ G Λ ⟨J,0,β⟩ i ≤ βJD/(1-βJD)`.

Proof: at `h = 0`, `truncated2 = correlation` (`truncated2_h_zero`) and the
diagonal term vanishes, so the sum reduces to `∑_{j≠i} ⟨σ_iσ_j⟩`,
bounded by `correlation_sum_le_of_high_temp`.

Reference: Glimm–Jaffe §5.1 pp. 73–74; Friedli–Velenik §3.7.3. -/
theorem susceptibilityΛ_le_of_high_temp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    {D : ℕ} (hD : ∀ v : ↑Λ,
        (Finset.univ.filter
          (fun e : (inducedGraph G Λ).edgeSet => v ∈ (e : Sym2 ↑Λ))).card ≤ D)
    (hlt : β * J * ↑D < 1) (i : ↑Λ) :
    susceptibilityΛ G Λ ⟨J, 0, β⟩ i ≤ β * J * ↑D / (1 - β * J * ↑D) := by
  classical
  -- Unfold to truncated2 sum (definitional via susceptibilityΛ_apply + IsingModel.susceptibility)
  suffices aux : ∑ j : ↑Λ, truncated2 (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) i j
      ≤ β * J * ↑D / (1 - β * J * ↑D) from aux
  -- Convert truncated2 to correlation at h=0
  have hconv : ∑ j : ↑Λ, truncated2 (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) i j
      = ∑ j : ↑Λ, correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} :=
    Finset.sum_congr rfl fun j _ => truncated2_h_zero (inducedGraph G Λ) J β i j
  rw [hconv]
  -- Diagonal: {i,i} = {i} as Finset, correlation {i,i} = magnetization i = 0 at h=0
  have hdiag : correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, i} : Finset ↑Λ) = 0 := by
    have heq : ({i, i} : Finset ↑Λ) = {i} :=
      Finset.insert_eq_of_mem (Finset.mem_singleton_self i)
    rw [heq]; exact magnetization_zero_at_h_zero (inducedGraph G Λ) J β i
  -- Split: ∑_Λ f = ∑_{j≠i} f + ∑_{j=i} f = ∑_{j≠i} f + 0 ≤ βJD/(1-βJD)
  have h_filt := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ↑Λ)
      (fun j : ↑Λ => j ≠ i)
      (fun j => correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j})
  have h_single : ∑ j ∈ (Finset.univ : Finset ↑Λ).filter (fun j => ¬j ≠ i),
        correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} = 0 := by
    have : (Finset.univ : Finset ↑Λ).filter (fun j => ¬j ≠ i) = {i} := by ext j; simp
    rw [this, Finset.sum_singleton, hdiag]
  linarith [correlation_sum_le_of_high_temp G Λ hβJ hD hlt i]

set_option maxHeartbeats 400000 in
-- Applying `susceptibilityΛ_le_of_high_temp` triggers instance synthesis whose
-- whnf exceeds the default 200000-heartbeat limit.
/-- **Along-exhaustion high-temperature susceptibility bound**:
for each stage `n`, `susceptibilityAlongExhaustion G Λ ⟨J,0,β⟩ i n ≤ βJD/(1-βJD)`.

Proof: if `i ∈ Λ.volume n`, apply `susceptibilityΛ_le_of_high_temp`;
otherwise the value is `0 ≤ βJD/(1-βJD)`.

Reference: Glimm–Jaffe §5.1; Friedli–Velenik §3.7.3. -/
theorem susceptibilityAlongExhaustion_le_of_high_temp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    {D : ℕ} (hD : ∀ n, ∀ v : ↑(Λ.volume n),
        (Finset.univ.filter
          (fun e : (inducedGraph G (Λ.volume n)).edgeSet =>
            v ∈ (e : Sym2 ↑(Λ.volume n)))).card ≤ D)
    (hlt : β * J * ↑D < 1) (i : V) (n : ℕ) :
    susceptibilityAlongExhaustion G Λ ⟨J, 0, β⟩ i n ≤ β * J * ↑D / (1 - β * J * ↑D) := by
  simp only [susceptibilityAlongExhaustion]
  split_ifs with h
  · exact susceptibilityΛ_le_of_high_temp G (Λ.volume n) hβJ (hD n) hlt ⟨i, h⟩
  · exact div_nonneg (mul_nonneg hβJ (Nat.cast_nonneg D)) (by linarith)

set_option maxHeartbeats 400000 in
-- Applying `susceptibilityAlongExhaustion_le_of_high_temp` + `ciSup_le` synthesizes
-- instances whose whnf exceeds the default 200000-heartbeat limit.
/-- **Infinite-volume high-temperature susceptibility bound**:
`susceptibilityInfinite G Λ ⟨J,0,β⟩ i ≤ βJD/(1-βJD)` when `βJD < 1`.

Proof: `susceptibilityInfinite = ⨆_n susceptibilityAlongExhaustion_n`;
each stage is bounded by `susceptibilityAlongExhaustion_le_of_high_temp`,
so `ciSup_le` closes the goal.

Reference: Glimm–Jaffe §5.1 pp. 73–74; Friedli–Velenik §3.7.3. -/
theorem susceptibilityInfinite_le_of_high_temp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    {D : ℕ} (hD : ∀ n, ∀ v : ↑(Λ.volume n),
        (Finset.univ.filter
          (fun e : (inducedGraph G (Λ.volume n)).edgeSet =>
            v ∈ (e : Sym2 ↑(Λ.volume n)))).card ≤ D)
    (hlt : β * J * ↑D < 1) (i : V) :
    susceptibilityInfinite G Λ ⟨J, 0, β⟩ i ≤ β * J * ↑D / (1 - β * J * ↑D) := by
  simp only [susceptibilityInfinite_eq_ciSup]
  apply ciSup_le
  intro n
  exact susceptibilityAlongExhaustion_le_of_high_temp G Λ hβJ hD hlt i n

open IsingModel in
/-- **ℤ^d concrete instance**: for the `d`-dimensional lattice graph with cubic exhaustion,
`0 ≤ βJ`, and `βJ · ↑(2*d) < 1`:
`susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J,0,β⟩ i ≤ βJ·↑(2*d)/(1-βJ·↑(2*d))`.

Proof: apply `susceptibilityInfinite_le_of_high_temp` with `D = 2*d : ℕ`;
the degree bound follows from `edgeFilter_card_eq_degree` + `inducedLatticeGraph_degree_le`.

Reference: Glimm–Jaffe §5.1; Friedli–Velenik §3.7.3. -/
theorem susceptibilityInfinite_latticeGraph_le_of_high_temp
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) := by
  apply susceptibilityInfinite_le_of_high_temp (latticeGraph d) (cubicExhaustion d)
    hβJ (D := 2 * d) _ hlt
  intro n v
  classical
  rw [edgeFilter_card_eq_degree v]
  exact inducedLatticeGraph_degree_le d _ v

end IsingModel.Ambient
