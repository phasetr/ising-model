import IsingModel.Dobrushin.HeatBathSweep
import IsingModel.Dobrushin.DobrushinResolvent

/-!
# The Dobrushin boundary weight and the oscillation Lyapunov bound (GJ §17.1, Issue #4214 §A)

The Dobrushin comparison capstone bounds a boundary-condition difference by the resolvent-weighted
oscillations, `∑_{x,y} R_{xy}·osc_x(f)·1_{y∈S}`. This file isolates the **boundary fixed-point**
structure underlying that bound, independent of the Gibbs measure.

* `dobrushinBoundaryWeight G β J S x := ∑_{y∈S} R_{xy}` — the resolvent harmonic weight of the
  differing boundary set `S`.
* `dobrushinBoundaryWeight_fixed_point` — `w_x = 1_{x∈S} + ∑_z C_{xz} w_z`, inherited from the
  resolvent fixed point `R = I + C·R`.
* `dobrushinBoundaryWeight_superharmonic` (`∑_z C_{xz} w_z ≤ w_x`) and
  `indicator_le_dobrushinBoundaryWeight` (`1_{x∈S} ≤ w_x`) are immediate corollaries.
* `heatBathListOscBound_boundary_sum_le_boundaryWeight` — the **Lyapunov bound**: for any sweep,
  `∑_{y∈S} heatBathListOscBound xs v y ≤ ∑_x v_x·w_x`. The weighted total `∑_x v_x·w_x` is a
  Lyapunov function of the oscillation-vector dynamics (non-increasing under each heat-bath step,
  by superharmonicity), and `1_{·∈S} ≤ w` recovers the boundary sum.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

omit [Fintype G.edgeSet] in
/-- **The Dobrushin boundary weight** of a differing boundary set `S`: the resolvent harmonic weight
`w_x = ∑_{y∈S} R_{xy}`, where `R = (I − C)⁻¹` is the Dobrushin resolvent. -/
noncomputable def dobrushinBoundaryWeight (β J : ℝ) (S : Finset ι) (x : ι) : ℝ :=
  ∑ y ∈ S, dobrushinResolvent G β J x y

omit [Fintype G.edgeSet] in
/-- The boundary weight is nonnegative. -/
theorem dobrushinBoundaryWeight_nonneg {β J : ℝ} (hβJ : 0 ≤ β * J) (S : Finset ι) (x : ι) :
    0 ≤ dobrushinBoundaryWeight G β J S x :=
  Finset.sum_nonneg fun y _ => dobrushinResolvent_nonneg G hβJ x y

omit [Fintype G.edgeSet] in
/-- **The boundary-weight fixed point** (GJ §17.1): `w_x = 1_{x∈S} + ∑_z C_{xz} w_z`, inherited from
the resolvent fixed point `R = I + C·R` summed over the differing boundary set `S`. -/
theorem dobrushinBoundaryWeight_fixed_point {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (S : Finset ι) (x : ι) :
    dobrushinBoundaryWeight G β J S x
      = (if x ∈ S then (1 : ℝ) else 0)
        + ∑ z, isingInfluenceMatrix G β J x z * dobrushinBoundaryWeight G β J S z := by
  rw [dobrushinBoundaryWeight]
  have hterm : ∀ y, dobrushinResolvent G β J x y
      = (if x = y then (1 : ℝ) else 0)
        + ∑ z, isingInfluenceMatrix G β J x z * dobrushinResolvent G β J z y :=
    fun y => dobrushinResolvent_fixed_point G hβJ hΔ x y
  rw [Finset.sum_congr rfl fun y _ => hterm y, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_ite_eq S x (fun _ => (1 : ℝ))
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [dobrushinBoundaryWeight, Finset.mul_sum]

omit [Fintype G.edgeSet] in
/-- **Superharmonicity of the boundary weight** (GJ §17.1): `∑_z C_{xz} w_z ≤ w_x`. The harmonic
weight loses exactly `1_{x∈S}` per `C`-step. -/
theorem dobrushinBoundaryWeight_superharmonic {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (S : Finset ι) (x : ι) :
    ∑ z, isingInfluenceMatrix G β J x z * dobrushinBoundaryWeight G β J S z
      ≤ dobrushinBoundaryWeight G β J S x := by
  rw [dobrushinBoundaryWeight_fixed_point G hβJ hΔ S x]
  have h : 0 ≤ (if x ∈ S then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  linarith

omit [Fintype G.edgeSet] in
/-- **The boundary indicator is dominated by the boundary weight** (GJ §17.1): `1_{x∈S} ≤ w_x`. -/
theorem indicator_le_dobrushinBoundaryWeight {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (S : Finset ι) (x : ι) :
    (if x ∈ S then (1 : ℝ) else 0) ≤ dobrushinBoundaryWeight G β J S x := by
  rw [dobrushinBoundaryWeight_fixed_point G hβJ hΔ S x]
  have h : 0 ≤ ∑ z, isingInfluenceMatrix G β J x z * dobrushinBoundaryWeight G β J S z :=
    Finset.sum_nonneg fun z _ =>
      mul_nonneg (isingInfluence_nonneg G hβJ x z) (dobrushinBoundaryWeight_nonneg G hβJ S z)
  linarith

omit [Fintype G.edgeSet] in
/-- The heat-bath oscillation step preserves nonnegativity. -/
theorem heatBathOscStep_nonneg {β J : ℝ} (hβJ : 0 ≤ β * J) (x : ι) {v : ι → ℝ}
    (hv : ∀ z, 0 ≤ v z) (y : ι) : 0 ≤ heatBathOscStep G β J x v y := by
  rw [heatBathOscStep]
  split_ifs
  · exact le_refl 0
  · exact add_nonneg (hv y) (mul_nonneg (isingInfluence_nonneg G hβJ x y) (hv x))

omit [Fintype G.edgeSet] in
/-- The oscillation-vector dynamics preserves nonnegativity over any sweep. -/
theorem heatBathListOscBound_nonneg {β J : ℝ} (hβJ : 0 ≤ β * J) (xs : List ι) :
    ∀ (v : ι → ℝ), (∀ z, 0 ≤ v z) → ∀ y, 0 ≤ heatBathListOscBound G β J xs v y := by
  induction xs with
  | nil => intro v hv y; exact hv y
  | cons x xs ih =>
    intro v hv y
    exact ih (heatBathOscStep G β J x v) (fun z => heatBathOscStep_nonneg G hβJ x hv z) y

omit [Fintype G.edgeSet] in
/-- **One Lyapunov step** (GJ §17.1): the boundary-weighted total `∑_y v_y·w_y` does not increase
under one heat-bath oscillation step, `∑_y (heatBathOscStep x v)_y·w_y ≤ ∑_y v_y·w_y`, by
superharmonicity of `w` and `v_x ≥ 0`. -/
theorem heatBathOscStep_boundaryWeight_sum_le {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (S : Finset ι) (x : ι) {v : ι → ℝ} (hv : ∀ z, 0 ≤ v z) :
    ∑ y, heatBathOscStep G β J x v y * dobrushinBoundaryWeight G β J S y
      ≤ ∑ y, v y * dobrushinBoundaryWeight G β J S y := by
  set w := fun y => dobrushinBoundaryWeight G β J S y with hw
  have hxx : isingInfluence G β J x x = 0 := by rw [isingInfluence, if_neg (by simp)]
  have hsuper : ∑ z, isingInfluence G β J x z * w z ≤ w x := by
    have := dobrushinBoundaryWeight_superharmonic G hβJ hΔ S x
    simpa [hw, isingInfluenceMatrix] using this
  have e1 : ∑ y, v y * w y = v x * w x + ∑ y ∈ Finset.univ.erase x, v y * w y :=
    (Finset.add_sum_erase Finset.univ (fun y => v y * w y) (Finset.mem_univ x)).symm
  have e2 : ∑ y, heatBathOscStep G β J x v y * w y
      = ∑ y ∈ Finset.univ.erase x, (v y + isingInfluence G β J x y * v x) * w y := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun y => heatBathOscStep G β J x v y * w y) (Finset.mem_univ x),
      heatBathOscStep, if_pos rfl, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [heatBathOscStep, if_neg (Finset.ne_of_mem_erase hy)]
  have e3 : ∑ z, isingInfluence G β J x z * w z
      = ∑ z ∈ Finset.univ.erase x, isingInfluence G β J x z * w z := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun z => isingInfluence G β J x z * w z) (Finset.mem_univ x), hxx, zero_mul, zero_add]
  rw [e1, e2]
  have key : ∑ y ∈ Finset.univ.erase x, (v y + isingInfluence G β J x y * v x) * w y
      = ∑ y ∈ Finset.univ.erase x, v y * w y
        + v x * ∑ y ∈ Finset.univ.erase x, isingInfluence G β J x y * w y := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [key, ← e3]
  have hle : v x * ∑ z, isingInfluence G β J x z * w z ≤ v x * w x :=
    mul_le_mul_of_nonneg_left hsuper (hv x)
  linarith

omit [Fintype G.edgeSet] in
/-- **The Lyapunov bound over a sweep** (GJ §17.1): the boundary-weighted total is non-increasing
under any sweep, `∑_y (heatBathListOscBound xs v)_y·w_y ≤ ∑_y v_y·w_y`. -/
theorem heatBathListOscBound_boundaryWeight_sum_le {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (S : Finset ι) (xs : List ι) :
    ∀ (v : ι → ℝ), (∀ z, 0 ≤ v z) →
      ∑ y, heatBathListOscBound G β J xs v y * dobrushinBoundaryWeight G β J S y
        ≤ ∑ y, v y * dobrushinBoundaryWeight G β J S y := by
  induction xs with
  | nil => intro v _; exact le_refl _
  | cons x xs ih =>
    intro v hv
    refine le_trans (ih (heatBathOscStep G β J x v)
      (fun z => heatBathOscStep_nonneg G hβJ x hv z)) ?_
    exact heatBathOscStep_boundaryWeight_sum_le G hβJ hΔ S x hv

omit [Fintype G.edgeSet] in
/-- **The boundary-sum Lyapunov bound** (GJ §17.1): the swept oscillation summed over the differing
boundary set `S` is bounded by the initial boundary-weighted total,
`∑_{y∈S} heatBathListOscBound xs v y ≤ ∑_x v_x·w_x`. Combines the Lyapunov bound with the
boundary-indicator domination `1_{·∈S} ≤ w`. -/
theorem heatBathListOscBound_boundary_sum_le_boundaryWeight {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (S : Finset ι) (xs : List ι) {v : ι → ℝ}
    (hv : ∀ z, 0 ≤ v z) :
    ∑ y ∈ S, heatBathListOscBound G β J xs v y
      ≤ ∑ x, v x * dobrushinBoundaryWeight G β J S x := by
  refine le_trans ?_ (heatBathListOscBound_boundaryWeight_sum_le G hβJ hΔ S xs v hv)
  have hub : ∑ y ∈ S, heatBathListOscBound G β J xs v y
      ≤ ∑ y, heatBathListOscBound G β J xs v y
          * dobrushinBoundaryWeight G β J S y := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
    have h1 : ∑ y ∈ S, heatBathListOscBound G β J xs v y
        ≤ ∑ y ∈ Finset.univ.filter (· ∈ S),
            heatBathListOscBound G β J xs v y * dobrushinBoundaryWeight G β J S y := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      refine Finset.sum_le_sum fun y hy => ?_
      have hyS : (if y ∈ S then (1 : ℝ) else 0) = 1 := if_pos hy
      have hind := indicator_le_dobrushinBoundaryWeight G hβJ hΔ S y
      rw [hyS] at hind
      calc heatBathListOscBound G β J xs v y
          = heatBathListOscBound G β J xs v y * 1 := (mul_one _).symm
        _ ≤ heatBathListOscBound G β J xs v y * dobrushinBoundaryWeight G β J S y :=
            mul_le_mul_of_nonneg_left hind
              (heatBathListOscBound_nonneg G hβJ xs v hv y)
    have h2 : (0 : ℝ) ≤ ∑ y ∈ Finset.univ.filter (¬ · ∈ S),
        heatBathListOscBound G β J xs v y * dobrushinBoundaryWeight G β J S y :=
      Finset.sum_nonneg fun y _ =>
        mul_nonneg (heatBathListOscBound_nonneg G hβJ xs v hv y)
          (dobrushinBoundaryWeight_nonneg G hβJ S y)
    linarith
  exact hub

end Dobrushin

end IsingModel
