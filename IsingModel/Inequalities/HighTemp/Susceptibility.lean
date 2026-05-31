import IsingModel.AmbientLattice.TruncatedFunctions
import IsingModel.Inequalities.SimonLieb
import IsingModel.Concrete.LatticeGraphBED

/-!
# High-temperature susceptibility bounds

Finite-volume, along-exhaustion, and infinite-volume susceptibility bounds in the
high-temperature regime, plus concrete lattice-graph instances.
-/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

/-- **Filter-card equals degree**: the number of edges of `G` incident to `v`
(counted as a filter over `G.edgeSet` subtypes) equals `G.degree v`.
Proof: bijection with `G.incidenceFinset v` via `e ↦ e.val`,
using `SimpleGraph.edge_mem_incidenceSet_iff`. -/
lemma edgeFilter_card_eq_degree
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

open IsingModel in
/-- **ℤ^d infinite-volume high-temperature susceptibility bound (general exhaustion)**:
for the `d`-dimensional lattice graph with **any** exhaustion `Λ`, `0 ≤ βJ`,
and `βJ · ↑(2*d) < 1`:
`susceptibilityInfinite (latticeGraph d) Λ ⟨J,0,β⟩ i ≤ βJ·↑(2*d)/(1-βJ·↑(2*d))`.

Proof: apply `susceptibilityInfinite_le_of_high_temp` with `D = 2*d : ℕ`;
the degree bound follows from `edgeFilter_card_eq_degree` + `inducedLatticeGraph_degree_le`.

Reference: Glimm–Jaffe §5.1; Friedli–Velenik §3.7.3. -/
theorem susceptibilityInfinite_latticeGraph_le_of_high_temp_gen
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) Λ ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) := by
  apply susceptibilityInfinite_le_of_high_temp (latticeGraph d) Λ
    hβJ (D := 2 * d) _ hlt
  intro n v
  classical
  rw [edgeFilter_card_eq_degree v]
  exact inducedLatticeGraph_degree_le d _ v

open IsingModel in
/-- **ℤ^d per-stage high-temperature susceptibility bound**: for the `d`-dimensional
lattice graph with cubic exhaustion, `0 ≤ βJ`, and `βJ · ↑(2*d) < 1`:
`susceptibilityAlongExhaustion (latticeGraph d) (cubicExhaustion d) ⟨J,0,β⟩ i n`
is bounded above by `βJ·↑(2*d)/(1-βJ·↑(2*d))`.

Proof: apply `susceptibilityAlongExhaustion_le_of_high_temp` with `D = 2*d : ℕ`;
the degree bound follows from `edgeFilter_card_eq_degree` + `inducedLatticeGraph_degree_le`.

Reference: Glimm–Jaffe §5.1; Friedli–Velenik §3.7.3. -/
theorem susceptibilityAlongExhaustion_latticeGraph_le_of_high_temp
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) (n : ℕ) :
    susceptibilityAlongExhaustion (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i n
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) := by
  apply susceptibilityAlongExhaustion_le_of_high_temp (latticeGraph d) (cubicExhaustion d)
    hβJ (D := 2 * d) _ hlt
  intro n' v
  classical
  rw [edgeFilter_card_eq_degree v]
  exact inducedLatticeGraph_degree_le d _ v

open IsingModel in
/-- **ℤ^d per-stage high-temperature susceptibility bound (general exhaustion)**:
for the `d`-dimensional lattice graph with **any** exhaustion `Λ`, `0 ≤ βJ`,
and `βJ · ↑(2*d) < 1`:
`susceptibilityAlongExhaustion (latticeGraph d) Λ ⟨J,0,β⟩ i n`
is bounded above by `βJ·↑(2*d)/(1-βJ·↑(2*d))`.

The proof is identical to `susceptibilityAlongExhaustion_latticeGraph_le_of_high_temp`
but works for an arbitrary `Λ : Ambient.Exhaustion (Fin d → ℤ)`.

Reference: Glimm–Jaffe §5.1; Friedli–Velenik §3.7.3. -/
theorem susceptibilityAlongExhaustion_latticeGraph_le_of_high_temp_gen
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) (n : ℕ) :
    susceptibilityAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ i n
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) := by
  apply susceptibilityAlongExhaustion_le_of_high_temp (latticeGraph d) Λ
    hβJ (D := 2 * d) _ hlt
  intro n' v
  classical
  rw [edgeFilter_card_eq_degree v]
  exact inducedLatticeGraph_degree_le d _ v

open IsingModel in
/-- **BddAbove of susceptibilityAlongExhaustion under high temperature** (Step 164, GJ §17.5):
For the `d`-dimensional lattice graph with any exhaustion `Λ`, vertex `i ∈ ℤ^d`,
`0 ≤ βJ`, and `βJ · ↑(2*d) < 1`, the sequence
`(susceptibilityAlongExhaustion (latticeGraph d) Λ ⟨J,0,β⟩ i n)_n`
is bounded above.

Proof: `susceptibilityAlongExhaustion_latticeGraph_le_of_high_temp_gen` gives a
uniform upper bound `βJ·2d/(1-βJ·2d)` for every `n`; this witnesses `BddAbove`.

Reference: Glimm–Jaffe §5.1 pp.~73--74 and §17.5 pp.~311--312. -/
theorem susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    BddAbove (Set.range fun n =>
        susceptibilityAlongExhaustion (latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) i n) := by
  refine ⟨β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)), ?_⟩
  rintro x ⟨n, rfl⟩
  exact susceptibilityAlongExhaustion_latticeGraph_le_of_high_temp_gen Λ hβJ hlt i n

/-! ## Ferromagnetic-form high-temperature helpers -/

open IsingModel in
/-- **Infinite-volume susceptibility bound from `Ferromagnetic ⟨J, 0, β⟩`**.

This is the ferromagnetic-input form of
`susceptibilityInfinite_latticeGraph_le_of_high_temp`. -/
theorem susceptibilityInfinite_latticeGraph_le_of_ferromagnetic_high_temp
    {d : ℕ} {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  susceptibilityInfinite_latticeGraph_le_of_high_temp
    (mul_nonneg hf.hβ.le hf.hJ) hlt i

open IsingModel in
/-- **Infinite-volume susceptibility bound (general exhaustion)
from `Ferromagnetic ⟨J, 0, β⟩`**. -/
theorem susceptibilityInfinite_latticeGraph_le_of_ferromagnetic_high_temp_gen
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) Λ ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  susceptibilityInfinite_latticeGraph_le_of_high_temp_gen Λ
    (mul_nonneg hf.hβ.le hf.hJ) hlt i

/-- **`0 ≤ susceptibility bound` from `0 ≤ β·J·(2d) < 1`**. -/
theorem susceptibility_bound_nonneg
    {β J : ℝ} {d : ℕ}
    (hβJ_nn : 0 ≤ β * J) (hlt : β * J * ↑(2 * d) < 1) :
    0 ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) := by
  have h2d_nn : (0 : ℝ) ≤ 2 * d := by positivity
  have hβJ2d_nn : 0 ≤ β * J * (2 * d) := mul_nonneg hβJ_nn h2d_nn
  have hβJ2d_nn' : 0 ≤ β * J * ↑(2 * d) := by exact_mod_cast hβJ2d_nn
  have h_denom_pos : 0 < 1 - β * J * ↑(2 * d) := by linarith
  exact div_nonneg hβJ2d_nn' h_denom_pos.le

/-- **`susceptibility bound < 1/(1 - β·J·2d)` (general upper)**. -/
theorem susceptibility_bound_lt_one_div
    {β J : ℝ} {d : ℕ}
    (hβJ_nn : 0 ≤ β * J) (hlt : β * J * ↑(2 * d) < 1) :
    β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) <
      1 / (1 - β * J * ↑(2 * d)) := by
  have h2d_nn : (0 : ℝ) ≤ 2 * d := by positivity
  have hβJ2d_nn : 0 ≤ β * J * (2 * d) := mul_nonneg hβJ_nn h2d_nn
  have hβJ2d_lt : β * J * ↑(2 * d) < 1 := hlt
  have h_denom_pos : 0 < 1 - β * J * ↑(2 * d) := by linarith
  rw [div_lt_div_iff_of_pos_right h_denom_pos]
  linarith

open IsingModel in
/-- **Squared susceptibility bound under ferromagnetic high temperature**.

For nonnegative `χ_∞ ≤ M` and `0 ≤ M`, we have `χ_∞² ≤ M²`. -/
theorem susceptibilityInfinite_squared_le_of_ferromagnetic_high_temp_bound
    {d : ℕ} {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ)
    (hχ_nn : 0 ≤
      susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i) :
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i ^ 2
      ≤ (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ^ 2 := by
  have h_le := susceptibilityInfinite_latticeGraph_le_of_ferromagnetic_high_temp hf hlt i
  have h_bd_nn := susceptibility_bound_nonneg (mul_nonneg hf.hβ.le hf.hJ) hlt
  exact sq_le_sq' (by linarith) h_le

open IsingModel in
/-- **`Ferromagnetic ⟨J, 0, β⟩` implies `0 ≤ β·J`**. -/
theorem ferromagnetic_implies_betaJ_nonneg {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 ≤ β * J :=
  mul_nonneg hf.hβ.le hf.hJ

open IsingModel in
/-- **`Ferromagnetic ⟨J, 0, β⟩` plus `β·J·(2d) < 1`
implies `0 < 1 - β·J·(2d)`**. -/
theorem one_sub_betaJ_two_d_pos_of_ferromagnetic_high_temp
    {J β : ℝ} {d : ℕ}
    (_hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hlt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) < 1 - β * J * ↑(2 * d) := by
  linarith

end IsingModel.Ambient
