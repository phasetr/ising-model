import IsingModel.Peierls.DualCutConnected
import IsingModel.Peierls.SingleOrbitEulerian
import IsingModel.Peierls.SingleOrbitDegTwoPairing
import IsingModel.Peierls.DartDualComponentEulerian

/-!
# The dual cut has even incidence degree at every dual vertex (FV §3.7.2)

The discrete-Jordan core needs the dual cut (and, via `DartDualComponentEulerian.lean`, each dart's
dual component) to be a mod-2 cycle. This file proves the even-degree property of the full dual cut
at every dual vertex `c`, by identifying the dual-cut edges incident to `c` with the cut directions
`cutDirs F c` (already known to be even, `card_cut_dirs_even`).

Each dual-cut edge through `c` has the form `s(c, c + dir.vec)` for a unique direction `dir`, and is
present exactly when `dir ∈ cutDirs F c` (one of the two darts of that edge is valid,
`mem_cutDirs_iff`). The map `dir ↦ s(c, c + dir.vec)` is therefore a bijection from `cutDirs F c`
onto the incident edges, so the incidence degree equals `(cutDirs F c).card`, which is even.

* `cutDirDualEdge_injective` — `dir ↦ s(c, c + dir.vec)` is injective.
* `mem_dartDualCut_incident_iff_exists_cutDir` — incidence membership via cut directions.
* `dartDualCut_incident_eq_cutDirs_image` — the incidence set is the image of `cutDirs F c`.
* `dartDualCut_incident_card_eq_cutDirs_card` — the incidence degree equals `(cutDirs F c).card`.
* `dartDualCut_incident_even` — the dual cut is even at every dual vertex.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **The direction-to-incident-edge map is injective**: distinct directions `dir` give distinct
edges `s(c, c + dir.vec)` (the second endpoints `c + dir.vec` are distinct, and none equals `c`). -/
theorem cutDirDualEdge_injective (c : Fin 2 → ℤ) :
    Function.Injective (fun dir : Dir2 => s(c, c + dir.vec)) := by
  intro d₁ d₂ h
  simp only [Sym2.eq_iff] at h
  apply Dir2.vec_injective
  apply add_left_cancel (a := c)
  rcases h with ⟨_, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · rw [h2]; exact h1

/-- **Incidence membership via cut directions**: a dual-cut edge through `c` is exactly an edge
`s(c, c + dir.vec)` for some cut direction `dir ∈ cutDirs F c`. -/
theorem mem_dartDualCut_incident_iff_exists_cutDir {c : Fin 2 → ℤ} {e : Sym2 (Fin 2 → ℤ)} :
    e ∈ (dartDualCut F).filter (fun e => c ∈ e) ↔
      ∃ dir ∈ cutDirs F c, e = s(c, c + dir.vec) := by
  classical
  rw [Finset.mem_filter, dartDualCut, Finset.mem_image]
  constructor
  · rintro ⟨⟨d, _, rfl⟩, hc⟩
    rw [Sym2.mem_iff] at hc
    rcases hc with rfl | rfl
    · exact ⟨d.dir, dir_mem_cutDirs_tail d, by rw [BoundaryDart.head]⟩
    · refine ⟨d.dir + 2, dir_add_two_mem_cutDirs_head d, ?_⟩
      have ht : d.head + (d.dir + 2).vec = d.tail := by
        rw [BoundaryDart.head, Dir2.vec_add_two]; abel
      rw [Sym2.eq_swap, ht]
  · rintro ⟨dir, hdir, rfl⟩
    refine ⟨?_, Sym2.mem_iff.mpr (Or.inl rfl)⟩
    rw [mem_cutDirs_iff] at hdir
    rcases hdir with hv | hv
    · exact ⟨⟨c, dir, hv.1, hv.2⟩, Finset.mem_univ _, by rw [BoundaryDart.head]⟩
    · refine ⟨⟨c + dir.vec, dir + 2, hv.1, hv.2⟩, Finset.mem_univ _, ?_⟩
      have ht : (c + dir.vec) + (dir + 2).vec = c := by
        rw [Dir2.vec_add_two]; abel
      rw [BoundaryDart.head, ht, Sym2.eq_swap]

/-- **The incidence set is the image of `cutDirs F c`** under `dir ↦ s(c, c + dir.vec)`. -/
theorem dartDualCut_incident_eq_cutDirs_image (c : Fin 2 → ℤ) :
    (dartDualCut F).filter (fun e => c ∈ e) =
      (cutDirs F c).image (fun dir => s(c, c + dir.vec)) := by
  ext e
  rw [Finset.mem_image, mem_dartDualCut_incident_iff_exists_cutDir]
  constructor
  · rintro ⟨dir, h, rfl⟩; exact ⟨dir, h, rfl⟩
  · rintro ⟨dir, h, rfl⟩; exact ⟨dir, h, rfl⟩

/-- **The incidence degree equals the cut-direction count**. -/
theorem dartDualCut_incident_card_eq_cutDirs_card (c : Fin 2 → ℤ) :
    ((dartDualCut F).filter (fun e => c ∈ e)).card = (cutDirs F c).card := by
  rw [dartDualCut_incident_eq_cutDirs_image,
    Finset.card_image_of_injective _ (cutDirDualEdge_injective c)]

/-- **The dual cut is even at every dual vertex**: the incidence degree of `dartDualCut F` at any
dual vertex `c` is even (it equals `(cutDirs F c).card`, which is even by `card_cut_dirs_even`). -/
theorem dartDualCut_incident_even (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ) :
    Even (((dartDualCut F).filter (fun e => c ∈ e)).card) := by
  rw [dartDualCut_incident_card_eq_cutDirs_card]
  exact card_cut_dirs_even F c

/-- **A dart's dual component is Eulerian** (unconditional): combining the incidence reduction
`dartDualComponentEdges_incident_even_of_dartDualCut_incident_even` with the dual cut's even degree
`dartDualCut_incident_even`, the dual component of any boundary dart `d` has even incidence degree
at every dual vertex `c`. This is the mod-2 cycle property the crossing-parity separation needs. -/
theorem dartDualComponentEdges_incident_even (F : Finset (Fin 2 → ℤ)) (d : BoundaryDart F)
    (c : Fin 2 → ℤ) :
    Even (((dartDualComponentEdges F d).filter (fun e => c ∈ e)).card) :=
  dartDualComponentEdges_incident_even_of_dartDualCut_incident_even d c
    (dartDualCut_incident_even F c)

end IsingModel
