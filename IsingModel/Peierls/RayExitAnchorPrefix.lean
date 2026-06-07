import IsingModel.Peierls.RayExitAnchorDart

/-!
# Ray-exit anchor stability along ray prefixes (FV §3.7.2)

The `rayExitAnchorDartMap` chooses, for each site of `F`, the first `+e₀` exit seen from
that site.  Along a fixed `+e₀` ray before its first exit, later starting points see the same
exit edge.  This file records that prefix stability as a small API for later `hshadow` work.

* `ray0_add` — shifting the ray origin along the same ray adds the indices.
* `rayExitIndex_shift` — the chosen first-exit index decreases by the prefix offset.
* `rayExitAnchorDart_shift` — prefix sites on the same ray have the same anchor dart.
* `rayExitAnchorDartMap_prefix_shared` — the same fact in shared-dual-vertex form.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- Shifting the origin along a `+e₀` ray adds the ray parameters. -/
theorem ray0_add (i : Fin 2 → ℤ) (t u : ℕ) : ray0 (ray0 i t) u = ray0 i (t + u) := by
  simp only [ray0, Nat.cast_add, add_smul]
  abel

/-- The strengthened first-exit specification determines the exit index uniquely. -/
theorem first_exit_below_unique {i : Fin 2 → ℤ} {k l : ℕ}
    (hkF : ∀ t, t ≤ k → ray0 i t ∈ F) (hkout : ray0 i (k + 1) ∉ F)
    (hlF : ∀ t, t ≤ l → ray0 i t ∈ F) (hlout : ray0 i (l + 1) ∉ F) : k = l := by
  by_cases hkl : k < l
  · have hmem : ray0 i (k + 1) ∈ F := hlF (k + 1) (by omega)
    exact (hkout hmem).elim
  · by_cases hlk : l < k
    · have hmem : ray0 i (l + 1) ∈ F := hkF (l + 1) (by omega)
      exact (hlout hmem).elim
    · omega

/-- If an index satisfies the strengthened first-exit specification, it is `rayExitIndex`. -/
theorem rayExitIndex_eq_of_first_exit (i : Fin 2 → ℤ) (hi : i ∈ F) {k : ℕ}
    (hkF : ∀ t, t ≤ k → ray0 i t ∈ F) (hkout : ray0 i (k + 1) ∉ F) :
    rayExitIndex F i hi = k :=
  first_exit_below_unique (rayExitIndex_below i hi) (rayExitIndex_succ_not_mem i hi) hkF hkout

/-- Starting from a prefix point on the same `+e₀` ray subtracts the prefix offset from the
chosen first-exit index. -/
theorem rayExitIndex_shift (i : Fin 2 → ℤ) (hi : i ∈ F) {t : ℕ}
    (ht : t ≤ rayExitIndex F i hi) :
    rayExitIndex F (ray0 i t) (rayExitIndex_below i hi t ht) =
      rayExitIndex F i hi - t := by
  refine rayExitIndex_eq_of_first_exit (ray0 i t) (rayExitIndex_below i hi t ht) ?_ ?_
  · intro u hu
    rw [ray0_add]
    exact rayExitIndex_below i hi (t + u) (by omega)
  · rw [ray0_add]
    have hidx : t + (rayExitIndex F i hi - t + 1) = rayExitIndex F i hi + 1 := by
      omega
    rw [hidx]
    exact rayExitIndex_succ_not_mem i hi

/-- The shifted prefix point has the same first-exit site as the original ray. -/
theorem ray0_rayExitIndex_shift (i : Fin 2 → ℤ) (hi : i ∈ F) {t : ℕ}
    (ht : t ≤ rayExitIndex F i hi) :
    ray0 (ray0 i t)
        (rayExitIndex F (ray0 i t) (rayExitIndex_below i hi t ht)) =
      ray0 i (rayExitIndex F i hi) := by
  rw [rayExitIndex_shift i hi ht, ray0_add]
  have hidx : t + (rayExitIndex F i hi - t) = rayExitIndex F i hi := by
    omega
  rw [hidx]

/-- Prefix sites on the same `+e₀` ray choose exactly the same ray-exit anchor dart. -/
theorem rayExitAnchorDart_shift (i : Fin 2 → ℤ) (hi : i ∈ F) {t : ℕ}
    (ht : t ≤ rayExitIndex F i hi) :
    rayExitAnchorDart F (ray0 i t) (rayExitIndex_below i hi t ht) =
      rayExitAnchorDart F i hi := by
  apply BoundaryDart.ext'
  · rw [rayExitAnchorDart_tail, rayExitAnchorDart_tail, ray0_rayExitIndex_shift i hi ht]
  · rw [rayExitAnchorDart_dir, rayExitAnchorDart_dir]

/-- Prefix sites on the same `+e₀` ray have ray-exit anchor edges sharing a dual vertex. -/
theorem rayExitAnchorDart_prefix_shared (i : Fin 2 → ℤ) (hi : i ∈ F) {t : ℕ}
    (ht : t ≤ rayExitIndex F i hi) :
    ∃ v : Fin 2 → ℤ,
      v ∈ s((rayExitAnchorDart F i hi).tail, (rayExitAnchorDart F i hi).head) ∧
        v ∈ s((rayExitAnchorDart F (ray0 i t) (rayExitIndex_below i hi t ht)).tail,
          (rayExitAnchorDart F (ray0 i t) (rayExitIndex_below i hi t ht)).head) := by
  refine ⟨ray0 i (rayExitIndex F i hi), rayExitAnchorDart_anchor_mem i hi, ?_⟩
  rw [rayExitAnchorDart_shift i hi ht]
  exact rayExitAnchorDart_anchor_mem i hi

/-- Prefix sites on the same `+e₀` ray have equal entries in `rayExitAnchorDartMap`. -/
theorem rayExitAnchorDartMap_prefix_eq (x : {x : Fin 2 → ℤ // x ∈ F}) {t : ℕ}
    (ht : t ≤ rayExitIndex F x.1 x.2) :
    rayExitAnchorDartMap F ⟨ray0 x.1 t, rayExitIndex_below x.1 x.2 t ht⟩ =
      rayExitAnchorDartMap F x :=
  rayExitAnchorDart_shift x.1 x.2 ht

/-- The map-level shared-vertex form of ray-prefix stability. -/
theorem rayExitAnchorDartMap_prefix_shared (x : {x : Fin 2 → ℤ // x ∈ F}) {t : ℕ}
    (ht : t ≤ rayExitIndex F x.1 x.2) :
    ∃ v : Fin 2 → ℤ,
      v ∈ s((rayExitAnchorDartMap F x).tail, (rayExitAnchorDartMap F x).head) ∧
        v ∈ s((rayExitAnchorDartMap F
          ⟨ray0 x.1 t, rayExitIndex_below x.1 x.2 t ht⟩).tail,
          (rayExitAnchorDartMap F
            ⟨ray0 x.1 t, rayExitIndex_below x.1 x.2 t ht⟩).head) :=
  rayExitAnchorDart_prefix_shared x.1 x.2 ht

end IsingModel
