import IsingModel.Dobrushin.BoundaryWeight
import IsingModel.Dobrushin.SingleSiteGeneralComparison

/-!
# The interior-mass contraction of the heat-bath sweep (GJ §17.1, Issue #4214 §A)

Toward the Dobrushin comparison capstone: under the Dobrushin condition `tanh(βJ)·Δ(G) < 1`, a full
heat-bath sweep over the volume `Λ` contracts the **interior mass** `MΛ(v) = ∑_{x∈Λ} v_x` of a
nonnegative oscillation vector by the Dobrushin coefficient `α = Δ(G)·tanh(βJ) < 1`. Iterating, the
interior mass after `n` full sweeps is `≤ αⁿ·MΛ(v) → 0`, killing the comparison's interior term.

The contraction is a Lyapunov/potential argument: one heat-bath step at `x ∈ Λ` drops the interior
mass by `(1−α)·v_x` (it zeroes `v_x` and re-distributes at most `α·v_x` of it), and summing over a
single sweep (each site swept once, its value when swept being at least its initial value) gives the
factor `α`.

* `heatBathOscStep_interiorMass_drop` — the per-step mass drop.
* `heatBathListOscBound_interiorMass_le` — the telescoped sweep bound `MΛ(sweep xs v) ≤ MΛ(v) −
  (1−α)·∑_{x∈xs} v_x`.
* `repeatedFullSweep` / `interiorMass_repeatedFullSweep_le_pow` — `MΛ(repeated n) ≤ αⁿ·MΛ(v)`.
* `interiorMass_repeatedFullSweep_tendsto_zero` — the interior mass vanishes in the sweep limit.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

omit [Fintype G.edgeSet] in
/-- **The influence row sum is at most the Dobrushin coefficient**: `∑_y C_{xy} = deg(x)·tanh(βJ) ≤
Δ(G)·tanh(βJ) = α`. -/
theorem isingInfluence_rowSum_le_dobrushinCoeff {β J : ℝ} (hβJ : 0 ≤ β * J) (x : ι) :
    ∑ y, isingInfluence G β J x y ≤ isingDobrushinCoeff G β J := by
  have htanh : 0 ≤ Real.tanh (β * J) := real_tanh_nonneg hβJ
  have hrow : ∑ y, isingInfluence G β J x y
      = ((Finset.univ ∩ G.neighborFinset x).card : ℝ) * Real.tanh (β * J) :=
    sum_isingInfluence_eq G β J x Finset.univ
  rw [hrow, isingDobrushinCoeff, Finset.univ_inter]
  refine mul_le_mul_of_nonneg_right ?_ htanh
  have hdeg : (G.neighborFinset x).card = G.degree x := rfl
  rw [hdeg]
  exact_mod_cast G.degree_le_maxDegree x

omit [Fintype G.edgeSet] in
/-- A heat-bath oscillation step does not decrease the value at any site other than the swept site
(the propagation `C_{xy}·v_x` is nonnegative). -/
theorem heatBathOscStep_ge_of_ne {β J : ℝ} (hβJ : 0 ≤ β * J) (x : ι) {v : ι → ℝ}
    (hvx : 0 ≤ v x) {y : ι} (hy : y ≠ x) : v y ≤ heatBathOscStep G β J x v y := by
  rw [heatBathOscStep, if_neg hy]
  have : 0 ≤ isingInfluence G β J x y * v x := mul_nonneg (isingInfluence_nonneg G hβJ x y) hvx
  linarith

omit [Fintype G.edgeSet] in
/-- **The per-step interior-mass drop** (GJ §17.1): one heat-bath step at `x ∈ Λ` drops the interior
mass by at least `(1 − α)·v_x`, where `α` is the Dobrushin coefficient. -/
theorem heatBathOscStep_interiorMass_drop {β J : ℝ} (hβJ : 0 ≤ β * J) {Λ : Finset ι} {x : ι}
    (hx : x ∈ Λ) {v : ι → ℝ} (hvx : 0 ≤ v x) :
    ∑ y ∈ Λ, heatBathOscStep G β J x v y
      ≤ (∑ y ∈ Λ, v y) - (1 - isingDobrushinCoeff G β J) * v x := by
  classical
  have hsplit : ∑ y ∈ Λ, heatBathOscStep G β J x v y
      = ∑ y ∈ Λ.erase x, (v y + isingInfluence G β J x y * v x) := by
    rw [← Finset.add_sum_erase Λ (fun y => heatBathOscStep G β J x v y) hx,
      heatBathOscStep, if_pos rfl, zero_add]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [heatBathOscStep, if_neg (Finset.ne_of_mem_erase hy)]
  rw [hsplit, Finset.sum_add_distrib]
  have hv : ∑ y ∈ Λ.erase x, v y = (∑ y ∈ Λ, v y) - v x := Finset.sum_erase_eq_sub hx
  have hrowle : ∑ y ∈ Λ.erase x, isingInfluence G β J x y ≤ isingDobrushinCoeff G β J := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => isingInfluence_nonneg G hβJ x y)) ?_
    exact isingInfluence_rowSum_le_dobrushinCoeff G hβJ x
  have hC : ∑ y ∈ Λ.erase x, isingInfluence G β J x y * v x
      ≤ isingDobrushinCoeff G β J * v x := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hrowle hvx
  rw [hv]
  nlinarith [hC]

omit [Fintype G.edgeSet] in
/-- **The telescoped sweep interior-mass bound** (GJ §17.1): sweeping a no-duplicate list `xs ⊆ Λ`
drops the interior mass by at least `(1 − α)·∑_{x∈xs} v_x` (each site, swept once, has value
time at least its initial value). -/
theorem heatBathListOscBound_interiorMass_le {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hα1 : isingDobrushinCoeff G β J < 1) (Λ : Finset ι) :
    ∀ (xs : List ι), xs.Nodup → (∀ x ∈ xs, x ∈ Λ) → ∀ (v : ι → ℝ), (∀ z, 0 ≤ v z) →
      (∑ y ∈ Λ, heatBathListOscBound G β J xs v y)
        ≤ (∑ y ∈ Λ, v y) - (1 - isingDobrushinCoeff G β J) * ∑ x ∈ xs.toFinset, v x := by
  intro xs
  induction xs with
  | nil => intro _ _ v _; simp [heatBathListOscBound]
  | cons x xs ih =>
    intro hnd hsub v hv
    have hx : x ∈ Λ := hsub x (List.mem_cons.mpr (Or.inl rfl))
    have hndxs : xs.Nodup := (List.nodup_cons.mp hnd).2
    have hxnotin : x ∉ xs := (List.nodup_cons.mp hnd).1
    have hxnotinf : x ∉ xs.toFinset := fun hc => hxnotin (List.mem_toFinset.mp hc)
    have hsubxs : ∀ y ∈ xs, y ∈ Λ := fun y hy => hsub y (List.mem_cons.mpr (Or.inr hy))
    have hstepnn : ∀ z, 0 ≤ heatBathOscStep G β J x v z :=
      fun z => heatBathOscStep_nonneg G hβJ x hv z
    have hih := ih hndxs hsubxs (heatBathOscStep G β J x v) hstepnn
    have hfold : heatBathListOscBound G β J (x :: xs) v
        = heatBathListOscBound G β J xs (heatBathOscStep G β J x v) := rfl
    rw [hfold]
    refine hih.trans ?_
    have hdrop := heatBathOscStep_interiorMass_drop G hβJ hx (v := v) (hvx := hv x)
    have hα0 : (0 : ℝ) ≤ 1 - isingDobrushinCoeff G β J := by linarith
    have hgrow : ∑ y ∈ xs.toFinset, v y
        ≤ ∑ y ∈ xs.toFinset, heatBathOscStep G β J x v y := by
      refine Finset.sum_le_sum fun y hy => ?_
      exact heatBathOscStep_ge_of_ne G hβJ x (hv x) (fun hyx => hxnotinf (hyx ▸ hy))
    rw [List.toFinset_cons, Finset.sum_insert hxnotinf, mul_add]
    linarith [hdrop, mul_le_mul_of_nonneg_left hgrow hα0]

omit [Fintype G.edgeSet] in
/-- **A full sweep contracts the interior mass** (GJ §17.1): under the Dobrushin condition,
`MΛ(sweep Λ.toList v) ≤ α·MΛ(v)` for nonnegative `v`. -/
theorem heatBathListOscBound_toList_interiorMass_le {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hα1 : isingDobrushinCoeff G β J < 1) (Λ : Finset ι) {v : ι → ℝ} (hv : ∀ z, 0 ≤ v z) :
    (∑ y ∈ Λ, heatBathListOscBound G β J Λ.toList v y)
      ≤ isingDobrushinCoeff G β J * ∑ y ∈ Λ, v y := by
  have h := heatBathListOscBound_interiorMass_le G hβJ hα1 Λ Λ.toList Λ.nodup_toList
    (fun x hx => Finset.mem_toList.mp hx) v hv
  rw [Finset.toList_toFinset] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **`n` repetitions of the full sweep over `Λ`**, as a flattened list. -/
noncomputable def repeatedFullSweep (Λ : Finset ι) (n : ℕ) : List ι :=
  (List.replicate n Λ.toList).flatten

omit [DecidableEq ι] [Fintype ι] [Fintype G.edgeSet] [DecidableRel G.Adj] in
/-- Every site of a repeated full sweep lies in `Λ`. -/
theorem repeatedFullSweep_subset (Λ : Finset ι) (n : ℕ) :
    ∀ x ∈ repeatedFullSweep Λ n, x ∈ Λ := by
  intro x hx
  rw [repeatedFullSweep, List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  rw [List.eq_of_mem_replicate hl] at hxl
  exact Finset.mem_toList.mp hxl

omit [DecidableEq ι] [Fintype ι] [Fintype G.edgeSet] [DecidableRel G.Adj] in
/-- The successor repeated sweep is the `n`-fold sweep followed by one more full sweep. -/
theorem repeatedFullSweep_succ (Λ : Finset ι) (n : ℕ) :
    repeatedFullSweep Λ (n + 1) = repeatedFullSweep Λ n ++ Λ.toList := by
  rw [repeatedFullSweep, repeatedFullSweep, List.replicate_succ', List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil]

omit [Fintype G.edgeSet] in
/-- **The repeated-sweep interior-mass geometric bound** (GJ §17.1): `MΛ(repeatedFullSweep Λ n v) ≤
αⁿ·MΛ(v)`. -/
theorem interiorMass_repeatedFullSweep_le_pow {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hα1 : isingDobrushinCoeff G β J < 1) (Λ : Finset ι) {v : ι → ℝ} (hv : ∀ z, 0 ≤ v z) :
    ∀ n : ℕ, (∑ y ∈ Λ, heatBathListOscBound G β J (repeatedFullSweep Λ n) v y)
      ≤ isingDobrushinCoeff G β J ^ n * ∑ y ∈ Λ, v y := by
  intro n
  induction n with
  | zero => simp [repeatedFullSweep, heatBathListOscBound]
  | succ n ih =>
    rw [repeatedFullSweep_succ]
    have hfold : heatBathListOscBound G β J (repeatedFullSweep Λ n ++ Λ.toList) v
        = heatBathListOscBound G β J Λ.toList
            (heatBathListOscBound G β J (repeatedFullSweep Λ n) v) := by
      simp only [heatBathListOscBound, List.foldl_append]
    rw [hfold]
    have hwnn : ∀ z, 0 ≤ heatBathListOscBound G β J (repeatedFullSweep Λ n) v z :=
      fun z => heatBathListOscBound_nonneg G hβJ (repeatedFullSweep Λ n) v hv z
    have hstep := heatBathListOscBound_toList_interiorMass_le G hβJ hα1 Λ hwnn
    have hα0 : (0 : ℝ) ≤ isingDobrushinCoeff G β J := isingDobrushinCoeff_nonneg G hβJ
    calc ∑ y ∈ Λ, heatBathListOscBound G β J Λ.toList
            (heatBathListOscBound G β J (repeatedFullSweep Λ n) v) y
        ≤ isingDobrushinCoeff G β J
            * ∑ y ∈ Λ, heatBathListOscBound G β J (repeatedFullSweep Λ n) v y := hstep
      _ ≤ isingDobrushinCoeff G β J * (isingDobrushinCoeff G β J ^ n * ∑ y ∈ Λ, v y) :=
          mul_le_mul_of_nonneg_left ih hα0
      _ = isingDobrushinCoeff G β J ^ (n + 1) * ∑ y ∈ Λ, v y := by ring

omit [Fintype G.edgeSet] in
/-- **The interior mass vanishes in the sweep limit** (GJ §17.1): under the Dobrushin condition, the
interior mass after `n` full sweeps tends to `0`. -/
theorem interiorMass_repeatedFullSweep_tendsto_zero {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hα1 : isingDobrushinCoeff G β J < 1) (Λ : Finset ι) {v : ι → ℝ} (hv : ∀ z, 0 ≤ v z) :
    Tendsto (fun n => ∑ y ∈ Λ, heatBathListOscBound G β J (repeatedFullSweep Λ n) v y)
      atTop (nhds 0) := by
  refine squeeze_zero (fun n => Finset.sum_nonneg fun y _ =>
    heatBathListOscBound_nonneg G hβJ (repeatedFullSweep Λ n) v hv y)
    (fun n => interiorMass_repeatedFullSweep_le_pow G hβJ hα1 Λ hv n) ?_
  have : Tendsto (fun n => isingDobrushinCoeff G β J ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (isingDobrushinCoeff_nonneg G hβJ) hα1
  simpa using this.mul_const (∑ y ∈ Λ, v y)

end Dobrushin

end IsingModel
