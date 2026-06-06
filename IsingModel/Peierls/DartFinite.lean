import IsingModel.Peierls.NextDart

/-!
# Finiteness of boundary darts (FV §3.7.2)

For a fixed finite region `F`, there are only finitely many boundary darts: a dart's left site
lies in `F`, and the left site together with the direction determines the dart (the left site is
`tail` plus a direction-dependent offset, so `tail` is recoverable). Hence `BoundaryDart F` injects
into `↥F × Dir2` and is a `Fintype`.

Finiteness is what forces the `nextDart` traversal to be eventually periodic — the orbit of a dart
closes into a cycle, the basis for the contour's connectedness.

* `leftSite_eq`, `leftSite_tail_injective` — the left site determines the tail.
* `BoundaryDart` is a `Fintype`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **The left site is the tail plus a direction-dependent offset**. -/
theorem leftSite_eq (t : Fin 2 → ℤ) (δ : Dir2) : leftSite t δ = t + leftSite 0 δ := by
  funext i
  fin_cases δ <;> fin_cases i <;>
    simp [leftSite, unitVec2, Pi.add_apply]

/-- **The left site determines the tail** (for a fixed direction): `leftSite · δ` is injective. -/
theorem leftSite_tail_injective {δ : Dir2} {t₁ t₂ : Fin 2 → ℤ}
    (h : leftSite t₁ δ = leftSite t₂ δ) : t₁ = t₂ := by
  rw [leftSite_eq t₁ δ, leftSite_eq t₂ δ] at h
  exact add_right_cancel h

/-- **Boundary darts are finite**: `BoundaryDart F` injects into `↥F × Dir2` via the left site and
direction (which determine the dart), so it is a `Fintype`. -/
noncomputable instance instFintypeBoundaryDart (F : Finset (Fin 2 → ℤ)) :
    Fintype (BoundaryDart F) := by
  apply Fintype.ofInjective
    (β := {x : Fin 2 → ℤ // x ∈ F} × Dir2)
    (fun d => (⟨leftSite d.tail d.dir, d.left_mem⟩, d.dir))
  intro a b heq
  simp only [Prod.ext_iff, Subtype.ext_iff] at heq
  obtain ⟨hL, hδ⟩ := heq
  obtain ⟨ta, da, ha, ha'⟩ := a
  obtain ⟨tb, db, hb, hb'⟩ := b
  simp only at hL hδ
  subst hδ
  obtain rfl := leftSite_tail_injective hL
  rfl

end IsingModel
