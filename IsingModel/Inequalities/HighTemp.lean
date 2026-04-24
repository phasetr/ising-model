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

-- liftFinset pair rewrite + sum_attach + Finset.sum_image injectivity proof
/-- **Private helper**: for any finite `s ⊆ Λ.volume n` and `i ∈ Λ.volume n`,
the sum of along-exhaustion correlations `∑ j ∈ s, correlationAlongExhaustion G Λ ⟨J,0,β⟩ {i,j} n`
is bounded by `susceptibilityAlongExhaustion G Λ ⟨J,0,β⟩ i n`.

Proof: at h=0, each `correlationAlongExhaustion {i,j} n = truncated2(Λ_n) ⟨i,hi⟩ ⟨j,hj⟩`
(via `correlationAlongExhaustion_of_subset`, `correlationΛ_apply`, liftFinset pair form,
`truncated2_h_zero`). Rewrite via `Finset.sum_attach` + `Finset.sum_congr`, then bound
the attached sum ≤ full `∑ j : ↑Λ_n` via `Finset.sum_image` injectivity +
`Finset.sum_le_sum_of_subset_of_nonneg`. -/
private lemma sum_correlationAlongExhaustion_le_susceptibilityAlongExhaustion
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J β : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    {s : Finset V} {i : V} {n : ℕ}
    (hi : i ∈ Λ.volume n) (hs : ∀ j ∈ s, j ∈ Λ.volume n) :
    ∑ j ∈ s, correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} n
      ≤ susceptibilityAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i n := by
  classical
  rw [susceptibilityAlongExhaustion_of_mem G Λ _ hi, susceptibilityΛ_apply,
      IsingModel.susceptibility_apply]
  -- Pointwise: corr {i,j} n = trunc2(Λ_n) ⟨i,hi⟩ ⟨j,hj⟩ at h=0
  have h_eq : ∀ j, ∀ hj : j ∈ s,
      correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} n
        = truncated2 (inducedGraph G (Λ.volume n)) (⟨J, 0, β⟩ : IsingParams ℝ)
            ⟨i, hi⟩ ⟨j, hs j hj⟩ := by
    intro j hj
    have h_ij : ({i, j} : Finset V) ⊆ Λ.volume n :=
      Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr (hs j hj)⟩
    rw [correlationAlongExhaustion_of_subset G Λ _ h_ij, correlationΛ_apply]
    have h_lift : liftFinset ({i, j} : Finset V) h_ij
        = ({⟨i, hi⟩, ⟨j, hs j hj⟩} : Finset ↑(Λ.volume n)) := by
      ext ⟨x, _⟩
      simp [mem_liftFinset, Subtype.ext_iff]
    rw [h_lift]
    exact (truncated2_h_zero (inducedGraph G (Λ.volume n)) J β ⟨i, hi⟩ ⟨j, hs j hj⟩).symm
  -- Convert ∑ j ∈ s, corr to ∑ j ∈ s.attach, trunc2
  rw [← Finset.sum_attach]
  rw [Finset.sum_congr rfl (fun j _ => h_eq j.val j.prop)]
  -- Bound via image + Finset.univ
  calc ∑ j ∈ s.attach, truncated2 (inducedGraph G (Λ.volume n))
          (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩ ⟨j.val, hs j.val j.prop⟩
      = ∑ j' ∈ s.attach.image (fun j => (⟨j.val, hs j.val j.prop⟩ : ↑(Λ.volume n))),
            truncated2 (inducedGraph G (Λ.volume n)) (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩ j' := by
          rw [Finset.sum_image]
          rintro ⟨a, ha⟩ _ ⟨b, hb⟩ _ h
          have h' := congr_arg Subtype.val h
          simp only at h'
          exact Subtype.ext h'
    _ ≤ ∑ j' : ↑(Λ.volume n), truncated2 (inducedGraph G (Λ.volume n))
            (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩ j' := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro j' _ _
          exact truncated2_nonneg (inducedGraph G (Λ.volume n)) _ hf ⟨i, hi⟩ j'

set_option maxHeartbeats 800000 in
-- `tendsto_finset_sum` + `le_of_tendsto` for finite partial-sum bound;
-- `sum_correlationAlongExhaustion_le_susceptibilityAlongExhaustion` helper;
-- `summable_of_sum_le` all need extended heartbeats.
/-- **High-temperature summability of the truncated 2-point function**:
at `h = 0`, `0 ≤ βJ`, max degree `≤ D`, and `βJD < 1`, the function
`j ↦ U_2(i, j; ⟨J,0,β⟩)` is summable over all `j : V`.

Proof: use `summable_of_sum_le` with bound `βJD/(1-βJD)`.
For any finite `s`, write `∑_{j∈s} U_2(i,j) = ∑_{j∈s} correlationInfinite {i,j}` (h=0).
Bound via `le_of_tendsto` applied to the convergent sequence
`∑_{j∈s} correlationAlongExhaustion {i,j} n →_n ∑_{j∈s} correlationInfinite {i,j}`,
which is eventually ≤ `susceptibilityAlongExhaustion n ≤ βJD/(1-βJD)`
by `sum_correlationAlongExhaustion_le_susceptibilityAlongExhaustion`.

Reference: Glimm–Jaffe §5.1 pp. 73–74; Friedli–Velenik §3.7.3. -/
theorem truncated2Infinite_summable_of_high_temp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    {D : ℕ} (hD : ∀ n, ∀ v : ↑(Λ.volume n),
        (Finset.univ.filter
          (fun e : (inducedGraph G (Λ.volume n)).edgeSet =>
            v ∈ (e : Sym2 ↑(Λ.volume n)))).card ≤ D)
    (hlt : β * J * ↑D < 1) (i : V) :
    Summable (fun j : V => truncated2Infinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j) := by
  classical
  have hβJ : 0 ≤ β * J := mul_nonneg (le_of_lt hf.hβ) hf.hJ
  apply summable_of_sum_le
      (c := β * J * ↑D / (1 - β * J * ↑D))
      (fun j => truncated2Infinite_nonneg G Λ _ hf i j)
  intro s
  -- At h=0: truncated2Infinite = correlationInfinite {i,j}
  conv_lhs => arg 2; ext j; rw [truncated2Infinite_h_zero G Λ J β i j]
  -- The sequence ∑ j ∈ s, correlationAlongExhaustion {i,j} n converges to LHS
  have hten : Filter.Tendsto
      (fun n => ∑ j ∈ s, correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} n)
      Filter.atTop (nhds (∑ j ∈ s, correlationInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, j})) :=
    tendsto_finset_sum s fun j _ =>
      tendsto_correlationAlongExhaustion_correlationInfinite G Λ _ hf {i, j}
  apply le_of_tendsto hten
  -- Eventually: ∑ j ∈ s, correlationAlongExhaustion {i,j} n ≤ βJD/(1-βJD)
  obtain ⟨N, hN⟩ := Λ.exhaust (s ∪ {i})
  apply Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  have hi_n : i ∈ Λ.volume n :=
    hN n hn (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
  have hs_n : ∀ j ∈ s, j ∈ Λ.volume n :=
    fun j hj => hN n hn (Finset.mem_union.mpr (Or.inl hj))
  calc ∑ j ∈ s, correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} n
      ≤ susceptibilityAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i n :=
          sum_correlationAlongExhaustion_le_susceptibilityAlongExhaustion G Λ hf hi_n hs_n
    _ ≤ β * J * ↑D / (1 - β * J * ↑D) :=
          susceptibilityAlongExhaustion_le_of_high_temp G Λ hβJ hD hlt i n

/-- **High-temperature cluster property**:
at `h = 0`, `0 ≤ βJ`, max degree `≤ D`, and `βJD < 1`,
the Gibbs state satisfies the cluster property:
`∀ i, Tendsto (j ↦ U_2(i,j)) Filter.cofinite (nhds 0)`.

Proof: per-site summability (`truncated2Infinite_summable_of_high_temp`)
+ `clusterProperty_of_summable`.

Reference: Glimm–Jaffe §5.1 pp. 72–74; Friedli–Velenik §3.7.3. -/
theorem clusterProperty_of_high_temp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    {D : ℕ} (hD : ∀ n, ∀ v : ↑(Λ.volume n),
        (Finset.univ.filter
          (fun e : (inducedGraph G (Λ.volume n)).edgeSet =>
            v ∈ (e : Sym2 ↑(Λ.volume n)))).card ≤ D)
    (hlt : β * J * ↑D < 1) :
    clusterProperty G Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  clusterProperty_of_summable G Λ _ fun i =>
    truncated2Infinite_summable_of_high_temp G Λ hf hD hlt i

open IsingModel in
/-- **ℤ^d high-temperature cluster property**:
for the `d`-dimensional lattice graph with cubic exhaustion,
`Ferromagnetic ⟨J,0,β⟩` (i.e. `0 ≤ J`, `0 < β`), and `βJ·2d < 1`:
`clusterProperty (latticeGraph d) (cubicExhaustion d) ⟨J,0,β⟩`.

Proof: apply `clusterProperty_of_high_temp` with `D = 2*d`,
using `edgeFilter_card_eq_degree` + `inducedLatticeGraph_degree_le`.

Reference: Glimm–Jaffe §5.1; Friedli–Velenik §3.7.3. -/
theorem clusterProperty_latticeGraph_of_high_temp
    {d : ℕ} {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hlt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  apply clusterProperty_of_high_temp (latticeGraph d) (cubicExhaustion d) hf (D := 2 * d) _ hlt
  intro n v
  classical
  rw [edgeFilter_card_eq_degree v]
  exact inducedLatticeGraph_degree_le d _ v

end IsingModel.Ambient
