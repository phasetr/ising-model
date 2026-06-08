import IsingModel.Peierls.RayExitAnchorVerticalStrictBridgeStrip

/-!
# Frontier entry darts for non-strip strict ray-exit gaps (FV §3.7.2)

`RayExitAnchorVerticalStrictBridgeStrip.lean` discharges straight strip gaps.  This file
prepares the remaining non-strip case: a non-strip finite gap has a first ray point which
re-enters `F`, and the predecessor of that first re-entry lies outside `F`.  The horizontal cut
between those two points gives a concrete boundary dart.  This is the local entry point for the
later `nextDart` frontier-chain argument.

No monotonicity after first exit is assumed; all indices are confined to the finite gap interval.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-! ## Re-entry witnesses from non-strip gaps -/

/-- A non-strip lower-exits-first genuine gap contains a lower ray point of `F` inside the finite
gap interval. -/
theorem exists_ltGap_nonStrip_mem
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    ∃ t : ℕ,
      rayExitIndex F a.1 a.2 + 1 ≤ t ∧
        t ≤ rayExitIndex F b.1 b.2 ∧ ray0 a.1 t ∈ F := by
  by_contra hnone
  apply hnon
  refine ⟨rayExitIndex F b.1 b.2 - (rayExitIndex F a.1 a.2 + 1), ?_, ?_⟩
  · omega
  · intro t ht0 ht1
    by_contra htmem
    exact hnone ⟨t, ht0, ht1, htmem⟩

/-- A non-strip upper-exits-first genuine gap contains an upper ray point of `F` inside the finite
gap interval. -/
theorem exists_gtGap_nonStrip_mem
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) :
    ∃ t : ℕ,
      rayExitIndex F b.1 b.2 + 1 ≤ t ∧
        t ≤ rayExitIndex F a.1 a.2 ∧ ray0 b.1 t ∈ F := by
  by_contra hnone
  apply hnon
  refine ⟨rayExitIndex F a.1 a.2 - (rayExitIndex F b.1 b.2 + 1), ?_, ?_⟩
  · omega
  · intro t ht0 ht1
    by_contra htmem
    exact hnone ⟨t, ht0, ht1, htmem⟩

/-- The first lower-ray re-entry index in a non-strip lower-exits-first genuine gap. -/
noncomputable def rayExitVerticalStrictLtFirstFrontierIndex
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) : ℕ :=
  Nat.find (exists_ltGap_nonStrip_mem a b hgap hnon)

/-- The first upper-ray re-entry index in a non-strip upper-exits-first genuine gap. -/
noncomputable def rayExitVerticalStrictGtFirstFrontierIndex
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) : ℕ :=
  Nat.find (exists_gtGap_nonStrip_mem a b hgap hnon)

/-- The first lower-ray frontier index lies after the lower first-exit successor. -/
theorem rayExitVerticalStrictLtFirstFrontierIndex_lower_bound
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    rayExitIndex F a.1 a.2 + 1 ≤
      rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon :=
  (Nat.find_spec (exists_ltGap_nonStrip_mem a b hgap hnon)).1

/-- The first lower-ray frontier index stays before the upper first-exit index. -/
theorem rayExitVerticalStrictLtFirstFrontierIndex_upper_bound
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon ≤
      rayExitIndex F b.1 b.2 :=
  (Nat.find_spec (exists_ltGap_nonStrip_mem a b hgap hnon)).2.1

/-- The first lower-ray frontier index is a point of `F`. -/
theorem rayExitVerticalStrictLtFirstFrontierIndex_mem
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    ray0 a.1 (rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) ∈ F :=
  (Nat.find_spec (exists_ltGap_nonStrip_mem a b hgap hnon)).2.2

/-- The first lower-ray frontier index is strictly after the first outside successor. -/
theorem rayExitVerticalStrictLtFirstFrontierIndex_strict_lower_bound
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    rayExitIndex F a.1 a.2 + 1 <
      rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon := by
  have hle := rayExitVerticalStrictLtFirstFrontierIndex_lower_bound a b hgap hnon
  have hne : rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon ≠
      rayExitIndex F a.1 a.2 + 1 := by
    intro hidx
    have hmem := rayExitVerticalStrictLtFirstFrontierIndex_mem a b hgap hnon
    rw [hidx] at hmem
    exact rayExitIndex_succ_not_mem a.1 a.2 hmem
  omega

/-- Minimality of the first lower-ray frontier index: earlier points in the finite gap interval
are outside `F`. -/
theorem rayExitVerticalStrictLtFirstFrontierIndex_min
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b)
    {t : ℕ}
    (ht0 : rayExitIndex F a.1 a.2 + 1 ≤ t)
    (htt : t < rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) :
    ray0 a.1 t ∉ F := by
  intro htmem
  have hnot := Nat.find_min (exists_ltGap_nonStrip_mem a b hgap hnon) htt
  exact hnot ⟨ht0, by
    have hub := rayExitVerticalStrictLtFirstFrontierIndex_upper_bound a b hgap hnon
    omega, htmem⟩

/-- The predecessor of the first lower-ray frontier point lies outside `F`. -/
theorem rayExitVerticalStrictLtFirstFrontierIndex_pred_not_mem
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    ray0 a.1 (rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon - 1) ∉ F := by
  have hstrict := rayExitVerticalStrictLtFirstFrontierIndex_strict_lower_bound a b hgap hnon
  exact rayExitVerticalStrictLtFirstFrontierIndex_min a b hgap hnon (by omega) (by omega)

/-- The first upper-ray frontier index lies after the upper first-exit successor. -/
theorem rayExitVerticalStrictGtFirstFrontierIndex_lower_bound
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) :
    rayExitIndex F b.1 b.2 + 1 ≤
      rayExitVerticalStrictGtFirstFrontierIndex a b hgap hnon :=
  (Nat.find_spec (exists_gtGap_nonStrip_mem a b hgap hnon)).1

/-- The first upper-ray frontier index stays before the lower first-exit index. -/
theorem rayExitVerticalStrictGtFirstFrontierIndex_upper_bound
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) :
    rayExitVerticalStrictGtFirstFrontierIndex a b hgap hnon ≤
      rayExitIndex F a.1 a.2 :=
  (Nat.find_spec (exists_gtGap_nonStrip_mem a b hgap hnon)).2.1

/-- The first upper-ray frontier index is a point of `F`. -/
theorem rayExitVerticalStrictGtFirstFrontierIndex_mem
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) :
    ray0 b.1 (rayExitVerticalStrictGtFirstFrontierIndex a b hgap hnon) ∈ F :=
  (Nat.find_spec (exists_gtGap_nonStrip_mem a b hgap hnon)).2.2

/-- The first upper-ray frontier index is strictly after the first outside successor. -/
theorem rayExitVerticalStrictGtFirstFrontierIndex_strict_lower_bound
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) :
    rayExitIndex F b.1 b.2 + 1 <
      rayExitVerticalStrictGtFirstFrontierIndex a b hgap hnon := by
  have hle := rayExitVerticalStrictGtFirstFrontierIndex_lower_bound a b hgap hnon
  have hne : rayExitVerticalStrictGtFirstFrontierIndex a b hgap hnon ≠
      rayExitIndex F b.1 b.2 + 1 := by
    intro hidx
    have hmem := rayExitVerticalStrictGtFirstFrontierIndex_mem a b hgap hnon
    rw [hidx] at hmem
    exact rayExitIndex_succ_not_mem b.1 b.2 hmem
  omega

/-- Minimality of the first upper-ray frontier index: earlier points in the finite gap interval
are outside `F`. -/
theorem rayExitVerticalStrictGtFirstFrontierIndex_min
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b)
    {t : ℕ}
    (ht0 : rayExitIndex F b.1 b.2 + 1 ≤ t)
    (htt : t < rayExitVerticalStrictGtFirstFrontierIndex a b hgap hnon) :
    ray0 b.1 t ∉ F := by
  intro htmem
  have hnot := Nat.find_min (exists_gtGap_nonStrip_mem a b hgap hnon) htt
  exact hnot ⟨ht0, by
    have hub := rayExitVerticalStrictGtFirstFrontierIndex_upper_bound a b hgap hnon
    omega, htmem⟩

/-- The predecessor of the first upper-ray frontier point lies outside `F`. -/
theorem rayExitVerticalStrictGtFirstFrontierIndex_pred_not_mem
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) :
    ray0 b.1 (rayExitVerticalStrictGtFirstFrontierIndex a b hgap hnon - 1) ∉ F := by
  have hstrict := rayExitVerticalStrictGtFirstFrontierIndex_strict_lower_bound a b hgap hnon
  exact rayExitVerticalStrictGtFirstFrontierIndex_min a b hgap hnon (by omega) (by omega)

/-! ## Concrete re-entry darts -/

/-- Removing one `e₀` step from a positive ray index gives the predecessor ray point. -/
theorem ray0_sub_unitVec2_zero_of_pos (i : Fin 2 → ℤ) {n : ℕ} (hn : 0 < n) :
    ray0 i n - unitVec2 0 = ray0 i (n - 1) := by
  funext j
  fin_cases j
  · simp [ray0, unitVec2, Pi.sub_apply, Pi.add_apply]
    omega
  · simp [ray0, unitVec2, Pi.sub_apply, Pi.add_apply]

/-- The boundary dart crossing a horizontal re-entry cut from `ray0 i (n - 1) ∉ F` to
`ray0 i n ∈ F`. -/
noncomputable def ray0ReentryDart (i : Fin 2 → ℤ) (n : ℕ) (hnpos : 0 < n)
    (hmem : ray0 i n ∈ F) (hprev : ray0 i (n - 1) ∉ F) : BoundaryDart F := by
  have hL : leftSite (ray0 i n - unitVec2 0) 3 = ray0 i n := by
    funext j
    fin_cases j <;> simp [leftSite, unitVec2, Pi.sub_apply]
  have hR : rightSite (ray0 i n - unitVec2 0) 3 = ray0 i (n - 1) := by
    calc
      rightSite (ray0 i n - unitVec2 0) 3 = ray0 i n - unitVec2 0 := by
        funext j
        fin_cases j <;>
          simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec, unitVec2, Pi.sub_apply]
      _ = ray0 i (n - 1) := ray0_sub_unitVec2_zero_of_pos i hnpos
  exact ⟨ray0 i n - unitVec2 0, 3, by rw [hL]; exact hmem, by rw [hR]; exact hprev⟩

/-- A re-entry dart starts at the predecessor dual vertex. -/
@[simp] theorem ray0ReentryDart_tail (i : Fin 2 → ℤ) (n : ℕ) (hnpos : 0 < n)
    (hmem : ray0 i n ∈ F) (hprev : ray0 i (n - 1) ∉ F) :
    (ray0ReentryDart i n hnpos hmem hprev).tail = ray0 i n - unitVec2 0 :=
  rfl

/-- A re-entry dart points in direction `-e₁`. -/
@[simp] theorem ray0ReentryDart_dir (i : Fin 2 → ℤ) (n : ℕ) (hnpos : 0 < n)
    (hmem : ray0 i n ∈ F) (hprev : ray0 i (n - 1) ∉ F) :
    (ray0ReentryDart i n hnpos hmem hprev).dir = 3 :=
  rfl

/-- A re-entry dart ends at the predecessor dual vertex below the ray. -/
@[simp] theorem ray0ReentryDart_head (i : Fin 2 → ℤ) (n : ℕ) (hnpos : 0 < n)
    (hmem : ray0 i n ∈ F) (hprev : ray0 i (n - 1) ∉ F) :
    (ray0ReentryDart i n hnpos hmem hprev).head =
      ray0 i n - unitVec2 0 - unitVec2 1 := by
  rw [BoundaryDart.head, ray0ReentryDart_tail, ray0ReentryDart_dir]
  funext j
  fin_cases j
  · simp [Dir2.vec, unitVec2, Pi.add_apply, Pi.sub_apply]
  · simp [Dir2.vec, unitVec2, Pi.add_apply, Pi.sub_apply]
    omega

/-- A re-entry dart has the re-entering ray point on its left. -/
theorem ray0ReentryDart_left
    (i : Fin 2 → ℤ) (n : ℕ) (hnpos : 0 < n)
    (hmem : ray0 i n ∈ F) (hprev : ray0 i (n - 1) ∉ F) :
    (ray0ReentryDart i n hnpos hmem hprev).left = ray0 i n := by
  change leftSite (ray0 i n - unitVec2 0) 3 = ray0 i n
  funext j
  fin_cases j <;> simp [leftSite, unitVec2, Pi.sub_apply]

/-- A re-entry dart has the predecessor ray point on its right. -/
theorem ray0ReentryDart_right
    (i : Fin 2 → ℤ) (n : ℕ) (hnpos : 0 < n)
    (hmem : ray0 i n ∈ F) (hprev : ray0 i (n - 1) ∉ F) :
    (ray0ReentryDart i n hnpos hmem hprev).right = ray0 i (n - 1) := by
  change rightSite (ray0 i n - unitVec2 0) 3 = ray0 i (n - 1)
  calc
    rightSite (ray0 i n - unitVec2 0) 3 = ray0 i n - unitVec2 0 := by
      funext j
      fin_cases j <;>
        simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec, unitVec2, Pi.sub_apply]
    _ = ray0 i (n - 1) := ray0_sub_unitVec2_zero_of_pos i hnpos

/-- The canonical lower re-entry dart for a non-strip lower-exits-first genuine gap. -/
noncomputable def rayExitVerticalStrictLtFrontierDart
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) : BoundaryDart F :=
  ray0ReentryDart a.1 (rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon)
    (by
      have hstrict := rayExitVerticalStrictLtFirstFrontierIndex_strict_lower_bound a b hgap hnon
      omega)
    (rayExitVerticalStrictLtFirstFrontierIndex_mem a b hgap hnon)
    (rayExitVerticalStrictLtFirstFrontierIndex_pred_not_mem a b hgap hnon)

/-- The canonical upper re-entry dart for a non-strip upper-exits-first genuine gap. -/
noncomputable def rayExitVerticalStrictGtFrontierDart
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) : BoundaryDart F :=
  ray0ReentryDart b.1 (rayExitVerticalStrictGtFirstFrontierIndex a b hgap hnon)
    (by
      have hstrict := rayExitVerticalStrictGtFirstFrontierIndex_strict_lower_bound a b hgap hnon
      omega)
    (rayExitVerticalStrictGtFirstFrontierIndex_mem a b hgap hnon)
    (rayExitVerticalStrictGtFirstFrontierIndex_pred_not_mem a b hgap hnon)

/-- The lower frontier dart starts at the predecessor lower-ray dual vertex. -/
@[simp] theorem rayExitVerticalStrictLtFrontierDart_tail
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    (rayExitVerticalStrictLtFrontierDart a b hgap hnon).tail =
      ray0 a.1 (rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) - unitVec2 0 := by
  unfold rayExitVerticalStrictLtFrontierDart
  rw [ray0ReentryDart_tail]

/-- The lower frontier dart points in direction `-e₁`. -/
@[simp] theorem rayExitVerticalStrictLtFrontierDart_dir
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    (rayExitVerticalStrictLtFrontierDart a b hgap hnon).dir = 3 := by
  unfold rayExitVerticalStrictLtFrontierDart
  rw [ray0ReentryDart_dir]

/-- The lower frontier dart ends below the predecessor lower-ray dual vertex. -/
@[simp] theorem rayExitVerticalStrictLtFrontierDart_head
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    (rayExitVerticalStrictLtFrontierDart a b hgap hnon).head =
      ray0 a.1 (rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) -
        unitVec2 0 - unitVec2 1 := by
  unfold rayExitVerticalStrictLtFrontierDart
  rw [ray0ReentryDart_head]

/-- The upper frontier dart starts at the predecessor upper-ray dual vertex. -/
@[simp] theorem rayExitVerticalStrictGtFrontierDart_tail
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) :
    (rayExitVerticalStrictGtFrontierDart a b hgap hnon).tail =
      ray0 b.1 (rayExitVerticalStrictGtFirstFrontierIndex a b hgap hnon) - unitVec2 0 := by
  unfold rayExitVerticalStrictGtFrontierDart
  rw [ray0ReentryDart_tail]

/-- The upper frontier dart points in direction `-e₁`. -/
@[simp] theorem rayExitVerticalStrictGtFrontierDart_dir
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) :
    (rayExitVerticalStrictGtFrontierDart a b hgap hnon).dir = 3 := by
  unfold rayExitVerticalStrictGtFrontierDart
  rw [ray0ReentryDart_dir]

/-- The upper frontier dart ends below the predecessor upper-ray dual vertex. -/
@[simp] theorem rayExitVerticalStrictGtFrontierDart_head
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) :
    (rayExitVerticalStrictGtFrontierDart a b hgap hnon).head =
      ray0 b.1 (rayExitVerticalStrictGtFirstFrontierIndex a b hgap hnon) -
        unitVec2 0 - unitVec2 1 := by
  unfold rayExitVerticalStrictGtFrontierDart
  rw [ray0ReentryDart_head]

/-- The lower frontier dart has the first lower-ray re-entry point on its left. -/
theorem rayExitVerticalStrictLtFrontierDart_left
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    (rayExitVerticalStrictLtFrontierDart a b hgap hnon).left =
      ray0 a.1 (rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon) := by
  unfold rayExitVerticalStrictLtFrontierDart
  rw [ray0ReentryDart_left]

/-- The lower frontier dart has the predecessor lower-ray point on its right. -/
theorem rayExitVerticalStrictLtFrontierDart_right
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F a.1 a.2 + 1 < rayExitIndex F b.1 b.2)
    (hnon : ¬ RayExitVerticalStrictLtGapStrip F a b) :
    (rayExitVerticalStrictLtFrontierDart a b hgap hnon).right =
      ray0 a.1 (rayExitVerticalStrictLtFirstFrontierIndex a b hgap hnon - 1) := by
  unfold rayExitVerticalStrictLtFrontierDart
  rw [ray0ReentryDart_right]

/-- The upper frontier dart has the first upper-ray re-entry point on its left. -/
theorem rayExitVerticalStrictGtFrontierDart_left
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) :
    (rayExitVerticalStrictGtFrontierDart a b hgap hnon).left =
      ray0 b.1 (rayExitVerticalStrictGtFirstFrontierIndex a b hgap hnon) := by
  unfold rayExitVerticalStrictGtFrontierDart
  rw [ray0ReentryDart_left]

/-- The upper frontier dart has the predecessor upper-ray point on its right. -/
theorem rayExitVerticalStrictGtFrontierDart_right
    (a b : {x : Fin 2 → ℤ // x ∈ F})
    (hgap : rayExitIndex F b.1 b.2 + 1 < rayExitIndex F a.1 a.2)
    (hnon : ¬ RayExitVerticalStrictGtGapStrip F a b) :
    (rayExitVerticalStrictGtFrontierDart a b hgap hnon).right =
      ray0 b.1 (rayExitVerticalStrictGtFirstFrontierIndex a b hgap hnon - 1) := by
  unfold rayExitVerticalStrictGtFrontierDart
  rw [ray0ReentryDart_right]

end IsingModel
