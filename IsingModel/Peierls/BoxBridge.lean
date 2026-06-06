import IsingModel.Peierls.DartCutChar
import IsingModel.Peierls.LiftBoxCutChar

/-!
# The dart primal cut equals the lifted box cut (FV §3.7.2)

For a box droplet `F : Finset ↑Λ` whose ambient image stays inside the box (every lattice neighbour
of an `F`-vertex lies in `Λ` — automatic when `F` is separated from the box boundary), the ambient
primal cut of `F.image Subtype.val` coincides with the lifted box cut `liftBoxCut Λ F`. The
inclusion `liftBoxCut ⊆ dartPrimalCut` needs no hypothesis; the reverse needs neighbour-closure so
the non-`F` endpoint is itself a box vertex.

This is the bridge linking the dual-cut/dart machinery (ambient) to the parity injectivity
`isFilled_eq_of_cutEdges_eq` (box), completing the contour injectivity chain.

* `dartPrimalCut_image_val_eq_liftBoxCut` — the ambient primal cut is the lifted box cut.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {Λ : Finset (Fin 2 → ℤ)} {F : Finset ↑Λ}

/-- **The ambient primal cut equals the lifted box cut** for a neighbour-closed box droplet. -/
theorem dartPrimalCut_image_val_eq_liftBoxCut
    (hclosed : ∀ a : ↑Λ, a ∈ F → ∀ b : Fin 2 → ℤ, (latticeGraph 2).Adj (↑a) b → b ∈ Λ) :
    dartPrimalCut (F.image Subtype.val) = liftBoxCut Λ F := by
  classical
  ext e
  rw [mem_dartPrimalCut_iff, mem_liftBoxCut_iff]
  constructor
  · rintro ⟨a, b, rfl, hadj, ha, hb⟩
    rw [Finset.mem_image] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    have hbΛ : b ∈ Λ := hclosed a' ha' b hadj
    refine ⟨a', ⟨b, hbΛ⟩, rfl, hadj, ha', ?_⟩
    intro hb'
    exact hb (Finset.mem_image.mpr ⟨⟨b, hbΛ⟩, hb', rfl⟩)
  · rintro ⟨a, b, rfl, hadj, ha, hb⟩
    refine ⟨↑a, ↑b, rfl, hadj, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    intro hb'
    rw [Finset.mem_image] at hb'
    obtain ⟨b', hb'F, hb'eq⟩ := hb'
    exact hb (Subtype.val_injective hb'eq ▸ hb'F)

end IsingModel
