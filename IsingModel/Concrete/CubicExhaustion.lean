import IsingModel.AmbientLattice.Exhaustion
import IsingModel.Lattice
import IsingModel.TranslationInvariance.Shift

/-!
# Cubic exhaustion of the integer lattice `Fin d → ℤ`

We equip the vertex type `Fin d → ℤ` (the `d`-dimensional integer
lattice used by `IsingModel.latticeGraph`) with a concrete
`Ambient.Exhaustion` built from two-sided cubic boxes
`[-n, n]^d`. This is the first concrete `Ambient.Exhaustion`
instance on `ℤ^d`, and makes `correlationInfinite (latticeGraph d)
(cubicExhaustion d) p A` an explicit object on the physical
`d`-dimensional Ising lattice.

## Main definitions

* `cubicBox d n : Finset (Fin d → ℤ)` — the finite set
  `{x : Fin d → ℤ | ∀ i, -n ≤ x i ≤ n}`, realised as
  `Fintype.piFinset` of coordinatewise `Finset.Icc (-↑n) ↑n`.
* `cubicExhaustion d : Ambient.Exhaustion (Fin d → ℤ)` — the
  exhaustion whose stage-`n` volume is `cubicBox d n`.

## Main theorems

* `mem_cubicBox` — membership characterisation
  `x ∈ cubicBox d n ↔ ∀ i, -n ≤ x i ∧ x i ≤ n`.
* `cubicBox_mono` — `m ≤ n → cubicBox d m ⊆ cubicBox d n`.
* `cubicBox_exhaust` — any finite `A ⊆ Fin d → ℤ` is contained in
  some `cubicBox d N`. The witness `N` is the `Finset.max'` of the
  set of `natAbs` of every coordinate of every point of `A`, in the
  non-degenerate case; the degenerate case (`A = ∅` or `d = 0`) picks
  `N = 0` and discharges the goal by contradiction / vacuity.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6, p. 67.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **Cubic box in `Fin d → ℤ`**: the finite set
`{x : Fin d → ℤ | ∀ i, -n ≤ x i ≤ n}` as a `Finset`. Built as the
dependent product of coordinate intervals
`Finset.Icc (-↑n : ℤ) n` via `Fintype.piFinset`. -/
noncomputable def cubicBox (d : ℕ) (n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n)

/-- **Membership in `cubicBox`**: `x ∈ cubicBox d n` iff every
coordinate lies in `Icc (-n) n`. -/
theorem mem_cubicBox {d n : ℕ} {x : Fin d → ℤ} :
    x ∈ cubicBox d n ↔ ∀ i, -(n : ℤ) ≤ x i ∧ x i ≤ n := by
  unfold cubicBox
  rw [Fintype.mem_piFinset]
  simp [Finset.mem_Icc]

/-- **Monotonicity of `cubicBox`**: if `m ≤ n`, the cube at level
`m` is contained in the cube at level `n`. -/
theorem cubicBox_mono (d : ℕ) : Monotone (cubicBox d) := by
  intro m n hmn x hx
  rw [mem_cubicBox] at hx ⊢
  intro i
  obtain ⟨hle, hge⟩ := hx i
  have hmn' : (m : ℤ) ≤ n := by exact_mod_cast hmn
  refine ⟨?_, ?_⟩
  · linarith [hle, hmn']
  · linarith [hge, hmn']

/-- **Boundary coordinate of a fresh cubic-box vertex**: a vertex that lies in
the stage-`n+1` cube but not in the stage-`n` cube has at least one coordinate of
absolute value exactly `n + 1`.

This pins fresh vertices of the cubic exhaustion to the sup-norm sphere of radius
`n + 1`, the geometric input for boundary-distance decay arguments (Issue
#2931). -/
theorem exists_coord_natAbs_eq_of_mem_cubicBox_succ_not_mem
    {d n : ℕ} {x : Fin d → ℤ}
    (hmem : x ∈ cubicBox d (n + 1)) (hnot : x ∉ cubicBox d n) :
    ∃ i, (x i).natAbs = n + 1 := by
  rw [mem_cubicBox] at hmem
  -- From `x ∉ cubicBox d n` extract a coordinate exceeding `n` in absolute value.
  have hex : ∃ i, ¬ (-(n : ℤ) ≤ x i ∧ x i ≤ n) := by
    by_contra h
    exact hnot (mem_cubicBox.mpr (fun i => not_not.mp (not_exists.mp h i)))
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_⟩
  -- Bound the same coordinate by `n + 1` from membership in the larger cube.
  obtain ⟨hle1, hge1⟩ := hmem i
  have hle1' : -((n : ℤ) + 1) ≤ x i := by push_cast at hle1; linarith
  have hge1' : x i ≤ (n : ℤ) + 1 := by push_cast at hge1; linarith
  -- The fresh coordinate sits at sup-norm exactly `n + 1`.
  rcases not_and_or.mp hi with h | h
  · have hlt := not_le.mp h
    omega
  · have hlt := not_le.mp h
    omega

/-- **ℓ¹-distance lower bound to a fresh cubic-box vertex**: if a reference point
`p` lies in the radius-`R` cube and `w` is a fresh vertex of the stage-`n+1` cube
(in the stage-`n+1` cube but not the stage-`n` cube) with `R ≤ n`, then the
lattice ℓ¹-distance from `p` to `w` is at least `n + 1 - R`.

A fresh vertex has a coordinate of absolute value `n + 1`, while every coordinate
of `p` has absolute value at most `R`; that single coordinate already contributes
at least `n + 1 - R` to the coordinatewise-sum distance.  This is the
boundary-distance growth used by the finite-volume convergence-rate program
(Issue #2931): fresh vertices recede from any fixed pair at unit speed in the
exhaustion stage. -/
theorem latticeDistance_ge_of_mem_cubicBox_succ_not_mem
    {d n R : ℕ} {p w : Fin d → ℤ}
    (hp : p ∈ cubicBox d R) (hRn : R ≤ n)
    (hmem : w ∈ cubicBox d (n + 1)) (hnot : w ∉ cubicBox d n) :
    n + 1 - R ≤ latticeDistance d p w := by
  obtain ⟨i, hi⟩ := exists_coord_natAbs_eq_of_mem_cubicBox_succ_not_mem hmem hnot
  rw [mem_cubicBox] at hp
  -- The `i`-th coordinate of `p` has absolute value at most `R`.
  have hpi : (p i).natAbs ≤ R := by
    have habs : |p i| ≤ (R : ℤ) := abs_le.mpr (hp i)
    have hcast : ((p i).natAbs : ℤ) ≤ (R : ℤ) := by rwa [← Int.abs_eq_natAbs]
    exact_mod_cast hcast
  -- A single coordinate's contribution lower-bounds the ℓ¹ distance.
  have hterm : (n + 1) - R ≤ (p i - w i).natAbs := by
    have htri : (w i).natAbs ≤ (p i).natAbs + (p i - w i).natAbs := by
      have : w i = p i - (p i - w i) := by ring
      calc (w i).natAbs = (p i - (p i - w i)).natAbs := by rw [← this]
        _ ≤ (p i).natAbs + (p i - w i).natAbs := by
            have := Int.natAbs_sub_le (p i) (p i - w i)
            simpa using this
    omega
  -- That coordinate term is one summand of `latticeDistance`.
  have hmem_term : (p i - w i).natAbs ≤ latticeDistance d p w := by
    unfold latticeDistance
    have hsum := Finset.single_le_sum
      (f := fun j : Fin d => (p j - w j).natAbs)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    -- `latticeDistance` is the sum of `|p j - w j|` over `j`; compare with one term.
    calc (p i - w i).natAbs ≤ ∑ j : Fin d, (p j - w j).natAbs := by
            simpa using hsum
      _ = latticeDistance d p w := by rw [latticeDistance]
  exact le_trans hterm hmem_term

/-- **ℓ¹-distance lower bound to a neighbour of a fresh cubic-box vertex**: a
vertex `v` adjacent (in `latticeGraph d`) to a fresh stage-`n+1` vertex `w`
still lies at lattice ℓ¹-distance at least `n - R` from a reference point `p` in
the radius-`R` cube (with `R ≤ n`).

Adjacency in `latticeGraph d` is exactly unit ℓ¹-distance, so a neighbour of a
fresh vertex can be no more than one step closer to `p`; the boundary-distance
lower bound therefore only loses one unit.  This extends the fresh-vertex
distance bound to the edges touching the boundary, the form needed when the
finite-volume β-derivative increment is expanded over the fresh boundary edges
(Issue #2931, Phase 3). -/
theorem latticeDistance_ge_of_adj_mem_cubicBox_succ_not_mem
    {d n R : ℕ} {p w v : Fin d → ℤ}
    (hp : p ∈ cubicBox d R) (hRn : R ≤ n)
    (hmem : w ∈ cubicBox d (n + 1)) (hnot : w ∉ cubicBox d n)
    (hadj : (latticeGraph d).Adj w v) :
    n - R ≤ latticeDistance d p v := by
  have hpw : n + 1 - R ≤ latticeDistance d p w :=
    latticeDistance_ge_of_mem_cubicBox_succ_not_mem hp hRn hmem hnot
  have hwv : latticeDistance d w v = 1 :=
    (latticeGraph_adj_iff_latticeDistance_eq_one d w v).mp hadj
  have hvw : latticeDistance d v w = 1 := by
    rw [latticeDistance_comm]; exact hwv
  have htri : latticeDistance d p w ≤ latticeDistance d p v + latticeDistance d v w :=
    latticeDistance_triangle d p v w
  omega

/-- **Cardinality of `cubicBox`**: the stage-`n` cube `[-n, n]^d` has exactly
`(2n + 1)^d` lattice points, since each of the `d` coordinate intervals
`Icc (-n) n` contains `2n + 1` integers. -/
theorem card_cubicBox (d n : ℕ) :
    (cubicBox d n).card = (2 * n + 1) ^ d := by
  unfold cubicBox
  rw [Fintype.card_piFinset]
  have hIcc : ∀ _ : Fin d, (Finset.Icc (-(n : ℤ)) n).card = 2 * n + 1 := by
    intro _
    rw [Int.card_Icc]
    have : ((n : ℤ) + 1 - -(n : ℤ)) = ((2 * n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [Finset.prod_congr rfl (fun i _ => hIcc i)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Polynomial growth of the fresh cubic-box boundary set**: the set of
vertices freshly added at stage `n + 1` has cardinality at most `(2n + 3)^d`,
the cardinality of the stage-`n+1` cube.  Combined with exponential decay of the
boundary contributions, this polynomial growth is what keeps the boundary sums
summable (Issue #2931, Phase 3). -/
theorem card_cubicBox_sdiff_succ_le (d n : ℕ) :
    (cubicBox d (n + 1) \ cubicBox d n).card ≤ (2 * n + 3) ^ d := by
  calc (cubicBox d (n + 1) \ cubicBox d n).card
      ≤ (cubicBox d (n + 1)).card := Finset.card_le_card Finset.sdiff_subset
    _ = (2 * (n + 1) + 1) ^ d := card_cubicBox d (n + 1)
    _ = (2 * n + 3) ^ d := by ring_nf

/-- **Geometric summability of the polynomially-growing boundary cardinalities**:
for `0 ≤ ratio < 1`, the sequence `n ↦ (2n + 3)^d · ratio^n` is summable.  This
is the summability skeleton for the boundary-distance decay argument: the fresh
boundary set grows polynomially in the stage while each contribution decays
geometrically (Issue #2931, Phase 3). -/
theorem summable_cubicBox_boundary_card_mul_geometric
    (d : ℕ) {ratio : ℝ} (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1) :
    Summable (fun n : ℕ => ((2 * n + 3 : ℕ) : ℝ) ^ d * ratio ^ n) := by
  have hr_norm : ‖ratio‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hratio0]; exact hratio1
  have hsum_pow : Summable (fun n : ℕ => (n : ℝ) ^ d * ratio ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one d hr_norm
  have hsum_geom : Summable (fun n : ℕ => ratio ^ n) :=
    summable_geometric_of_lt_one hratio0 hratio1
  -- Majorant `6^d·(n^d·ratio^n) + 6^d·ratio^n`, summable as a sum of summables.
  have hg : Summable
      (fun n : ℕ => (6 : ℝ) ^ d * ((n : ℝ) ^ d * ratio ^ n) + (6 : ℝ) ^ d * ratio ^ n) :=
    (hsum_pow.mul_left _).add (hsum_geom.mul_left _)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hg
  have hrn : 0 ≤ ratio ^ n := pow_nonneg hratio0 n
  have hbase0 : (0 : ℝ) ≤ ((2 * n + 3 : ℕ) : ℝ) := by positivity
  have hbase : ((2 * n + 3 : ℕ) : ℝ) ≤ 3 * ((n : ℝ) + 1) := by push_cast; linarith
  have hpow : ((2 * n + 3 : ℕ) : ℝ) ^ d ≤ (3 * ((n : ℝ) + 1)) ^ d :=
    pow_le_pow_left₀ hbase0 hbase d
  have hn1 : ((n : ℝ) + 1) ^ d ≤ (2 : ℝ) ^ d * ((n : ℝ) ^ d + 1) := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      simp only [Nat.cast_zero, zero_add, one_pow]
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
      have h3 : (1 : ℝ) ≤ (0 : ℝ) ^ d + 1 := by
        have h0 : (0 : ℝ) ≤ (0 : ℝ) ^ d := pow_nonneg le_rfl d
        linarith
      exact le_trans h2 (le_mul_of_one_le_right (by positivity) h3)
    · have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
      calc ((n : ℝ) + 1) ^ d
          ≤ (2 * (n : ℝ)) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
        _ = (2 : ℝ) ^ d * (n : ℝ) ^ d := by rw [mul_pow]
        _ ≤ (2 : ℝ) ^ d * ((n : ℝ) ^ d + 1) := by
            have hle : (n : ℝ) ^ d ≤ (n : ℝ) ^ d + 1 := by linarith
            exact mul_le_mul_of_nonneg_left hle (by positivity)
  have hstep : ((2 * n + 3 : ℕ) : ℝ) ^ d ≤ (6 : ℝ) ^ d * ((n : ℝ) ^ d + 1) := by
    calc ((2 * n + 3 : ℕ) : ℝ) ^ d
        ≤ (3 * ((n : ℝ) + 1)) ^ d := hpow
      _ = (3 : ℝ) ^ d * ((n : ℝ) + 1) ^ d := by rw [mul_pow]
      _ ≤ (3 : ℝ) ^ d * ((2 : ℝ) ^ d * ((n : ℝ) ^ d + 1)) :=
          mul_le_mul_of_nonneg_left hn1 (by positivity)
      _ = (6 : ℝ) ^ d * ((n : ℝ) ^ d + 1) := by rw [← mul_assoc, ← mul_pow]; norm_num
  calc ((2 * n + 3 : ℕ) : ℝ) ^ d * ratio ^ n
      ≤ ((6 : ℝ) ^ d * ((n : ℝ) ^ d + 1)) * ratio ^ n :=
        mul_le_mul_of_nonneg_right hstep hrn
    _ = (6 : ℝ) ^ d * ((n : ℝ) ^ d * ratio ^ n) + (6 : ℝ) ^ d * ratio ^ n := by ring

/-- **Exhaustion property for `cubicBox`**: any finite set
`A ⊆ Fin d → ℤ` is contained in some sufficiently large cube.

In the non-degenerate case (`A.Nonempty` and `d ≠ 0`), the witness `N`
is the `Finset.max'` of `natAbs` of every coordinate of every point
of `A`. In the degenerate case (`A = ∅` or `d = 0`), the helper
`Finset` of absolute coordinates is empty and we take `N = 0`; the
membership goal is then discharged by `exfalso` (for `A = ∅` the
membership hypothesis `a ∈ A` is false; for `d = 0` there is no
`i : Fin 0` to contradict, but the assumed membership still provides
such an `i`-derived element to contradict emptiness of the helper
set). -/
theorem cubicBox_exhaust (d : ℕ) (A : Finset (Fin d → ℤ)) :
    ∃ N, ∀ n ≥ N, A ⊆ cubicBox d n := by
  classical
  -- The set of absolute coordinates `|a i|` for `a ∈ A`, `i : Fin d`.
  set absSet : Finset ℕ :=
    A.biUnion (fun a => (Finset.univ : Finset (Fin d)).image
      (fun i => (a i).natAbs))
    with habsSet_def
  by_cases hne : absSet.Nonempty
  · refine ⟨absSet.max' hne, ?_⟩
    intro n hn a ha
    rw [mem_cubicBox]
    intro i
    have hmem : (a i).natAbs ∈ absSet := by
      rw [habsSet_def]
      exact Finset.mem_biUnion.mpr ⟨a, ha,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    have hle : (a i).natAbs ≤ absSet.max' hne := Finset.le_max' _ _ hmem
    have hleN : (a i).natAbs ≤ n := hle.trans hn
    have habs : |a i| ≤ (n : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hleN
    have := abs_le.mp habs
    refine ⟨this.1, this.2⟩
  · -- `absSet` empty; refine ⟨0, _⟩ and conclude by exfalso via `a, i`.
    refine ⟨0, ?_⟩
    intro n _ a ha
    rw [mem_cubicBox]
    intro i
    exfalso
    apply hne
    refine ⟨(a i).natAbs, ?_⟩
    rw [habsSet_def]
    exact Finset.mem_biUnion.mpr ⟨a, ha,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

/-- **Concrete cubic exhaustion of `Fin d → ℤ`**: stage-`n` volume is
the cube `[-n, n]^d`. Satisfies monotonicity and covers every finite
subset of `Fin d → ℤ`, so furnishes an `Ambient.Exhaustion` instance.
This is the first concrete exhaustion on the physical integer lattice,
enabling `correlationInfinite (latticeGraph d) (cubicExhaustion d)`
etc. as explicit objects. -/
noncomputable def cubicExhaustion (d : ℕ) : Ambient.Exhaustion (Fin d → ℤ) where
  volume := cubicBox d
  mono := cubicBox_mono d
  exhaust := cubicBox_exhaust d

/-! ## `Exhaustion.shift` specialisations on cubicExhaustion -/

/-- **Zero-shift identity** on cubicExhaustion:
`(cubicExhaustion d).shift 0 = cubicExhaustion d`. Direct from
`Exhaustion.shift_zero`. -/
@[simp]
theorem cubicExhaustion_shift_zero (d : ℕ) :
    (cubicExhaustion d).shift (0 : Fin d → ℤ) = cubicExhaustion d :=
  Exhaustion.shift_zero (cubicExhaustion d)

/-! ## Convenience specialisations -/

/-- **`cubicExhaustion d`'s volume is eventually nonempty** under
`[Nonempty (Fin d → ℤ)]`. Specialisation of
`Exhaustion.eventually_volume_nonempty`. -/
theorem cubicExhaustion_eventually_volume_nonempty
    (d : ℕ) [Nonempty (Fin d → ℤ)] :
    ∀ᶠ n in Filter.atTop, ((cubicExhaustion d).volume n).Nonempty :=
  Exhaustion.eventually_volume_nonempty (cubicExhaustion d)

/-- **`cubicExhaustion d`'s volume cardinality tends to ∞** under
`[Infinite (Fin d → ℤ)]`. Specialisation of
`Exhaustion.tendsto_card_atTop`. -/
theorem cubicExhaustion_tendsto_card_atTop
    (d : ℕ) [Infinite (Fin d → ℤ)] :
    Filter.Tendsto
      (fun n => ((cubicExhaustion d).volume n).card) Filter.atTop Filter.atTop :=
  Exhaustion.tendsto_card_atTop (cubicExhaustion d)

end Ambient

end IsingModel
