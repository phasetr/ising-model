import IsingModel.Inequalities.HighTemp.Susceptibility

/-!
# High-temperature summability and cluster property

Summability of the infinite-volume truncated two-point function at high
temperature and the resulting cluster-property wrappers.
-/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

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

/-- **Per-pair high-temperature correlation bound from finite susceptibility**:
at `h = 0`, `0 ≤ βJ`, max degree `≤ D`, and `βJD < 1`, every infinite-volume pair
correlation is bounded by the susceptibility ceiling,
`correlationInfinite G Λ ⟨J,0,β⟩ {i,w} ≤ βJD/(1−βJD)`.

Proof: a single nonnegative pair term is bounded by the whole susceptibility sum.
Concretely, `correlationAlongExhaustion {i,w} n = ∑_{j ∈ {w}} correlationAlongExhaustion {i,j} n
≤ susceptibilityAlongExhaustion i n ≤ βJD/(1−βJD)` (private
`sum_correlationAlongExhaustion_le_susceptibilityAlongExhaustion` at the singleton `{w}`
plus `susceptibilityAlongExhaustion_le_of_high_temp`), and `le_of_tendsto` on
`tendsto_correlationAlongExhaustion_correlationInfinite` passes the bound to the limit.

This is the missing **distance-1 (adjacent)** correlation bound: the Simon–Lieb peeling
alone yields only `≤ 1` at distance 1, whereas the susceptibility ceiling is `< 1` in the
strict window `βJD < 1/2`.

Reference: Glimm–Jaffe §5.1 pp. 73–74; §17.5 pp. 311–312; Friedli–Velenik §3.7.3. -/
theorem correlationInfinite_le_susceptibility_bound_of_high_temp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    {D : ℕ} (hD : ∀ n, ∀ v : ↑(Λ.volume n),
        (Finset.univ.filter
          (fun e : (inducedGraph G (Λ.volume n)).edgeSet =>
            v ∈ (e : Sym2 ↑(Λ.volume n)))).card ≤ D)
    (hlt : β * J * ↑D < 1) (i w : V) :
    correlationInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, w}
      ≤ β * J * ↑D / (1 - β * J * ↑D) := by
  classical
  have hβJ : 0 ≤ β * J := mul_nonneg (le_of_lt hf.hβ) hf.hJ
  have hten := tendsto_correlationAlongExhaustion_correlationInfinite G Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) hf {i, w}
  apply le_of_tendsto hten
  obtain ⟨N, hN⟩ := Λ.exhaust ({i, w} : Finset V)
  apply Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  have hi_n : i ∈ Λ.volume n := hN n hn (Finset.mem_insert_self i {w})
  have hw_n : w ∈ Λ.volume n :=
    hN n hn (Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
  have hsingle : correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, w} n
      = ∑ j ∈ ({w} : Finset V),
          correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} n := by
    rw [Finset.sum_singleton]
  rw [hsingle]
  calc ∑ j ∈ ({w} : Finset V),
          correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} n
      ≤ susceptibilityAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i n :=
        sum_correlationAlongExhaustion_le_susceptibilityAlongExhaustion G Λ hf hi_n
          (fun j hj => by rw [Finset.mem_singleton] at hj; subst hj; exact hw_n)
    _ ≤ β * J * ↑D / (1 - β * J * ↑D) :=
        susceptibilityAlongExhaustion_le_of_high_temp G Λ hβJ hD hlt i n

open IsingModel in
/-- **ℤ^d per-pair high-temperature correlation bound**:
for the `d`-dimensional lattice graph with cubic exhaustion, `Ferromagnetic ⟨J,0,β⟩`,
and `βJ·2d < 1`, `correlationInfinite (latticeGraph d) (cubicExhaustion d) ⟨J,0,β⟩ {i,w}
≤ βJ·2d/(1−βJ·2d)` for every pair `i, w`.

Proof: `correlationInfinite_le_susceptibility_bound_of_high_temp` with `D = 2d`, using the
same degree discharge (`edgeFilter_card_eq_degree` + `inducedLatticeGraph_degree_le`) as
`clusterProperty_latticeGraph_of_high_temp`.

Reference: Glimm–Jaffe §5.1; §17.5 pp. 311–312; Friedli–Velenik §3.7.3. -/
theorem correlationInfinite_latticeGraph_le_susceptibility_bound_of_high_temp
    {d : ℕ} {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hlt : β * J * (2 * (d : ℝ)) < 1) (i w : Fin d → ℤ) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, w}
      ≤ β * J * (2 * (d : ℝ)) / (1 - β * J * (2 * (d : ℝ))) := by
  have hcast : (↑(2 * d) : ℝ) = 2 * (d : ℝ) := by push_cast; ring
  have hlt' : β * J * (↑(2 * d) : ℝ) < 1 := by rw [hcast]; exact hlt
  have hbound :
      correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, w}
        ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) := by
    apply correlationInfinite_le_susceptibility_bound_of_high_temp
      (latticeGraph d) (cubicExhaustion d) hf (D := 2 * d) _ hlt'
    intro n v
    classical
    rw [edgeFilter_card_eq_degree v]
    exact inducedLatticeGraph_degree_le d _ v
  rwa [hcast] at hbound

end IsingModel.Ambient
