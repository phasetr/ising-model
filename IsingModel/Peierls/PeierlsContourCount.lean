import IsingModel.Peierls.ContourCountAssembly
import IsingModel.Peierls.RayAnchorSet
import IsingModel.Peierls.DualCutCardBridge
import IsingModel.Peierls.PlanarBondReduction

/-!
# The Peierls contour count for box droplets (FV §3.7.2)

Assembling all the supply lemmas, the number of box droplets `S` (neighbour-closed, ground-avoiding,
single-orbit) with `|cutEdges (box) S| = r` is at most `r · (2·2)^{2r} ≤ 32^r`,
volume-independently. The dual cut `dualCutInBox` is injective on droplets
(`box_droplet_eq_of_dualCutInBox_eq`), edge-connected (single orbit, or anchored
`DartReachable` data), of size `r` (`dualCutInBox_card_eq_cutEdges`), and anchored in the
`r`-element ray anchor set (`rayAnchorSet_cover`); feeding the contour count assembly
`contour_count_le` then bounds the count.

* `peierls_contour_count` — `|D| ≤ r · (2·2)^{2r}`.
* `peierls_contour_count_anchored` — the same bound from anchored `DartReachable` data instead of
  the single-orbit hypothesis.

The single-orbit (discrete Jordan) input enters only through the connectivity supply; the anchored
variant is the count-consumer form for the direct edge-connectedness route.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, (3.49), pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **The Peierls contour count**: the number of neighbour-closed, ground-avoiding, single-orbit
box droplets `S ∋ i` with box edge cut of size `r` is at most `r · (2·2)^{2r}`. -/
theorem peierls_contour_count {Λ Λd : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ}
    {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hone : ∀ S ∈ D, ∀ d e : BoundaryDart (S.image Subtype.val), d.SameOrbit e)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) := by
  classical
  set cut : Finset ↑Λ → Finset (Sym2 ↑Λd) :=
    fun S => if h : dualSupport (S.image Subtype.val) ⊆ Λd then dualCutInBox h else ∅ with hcut
  have hcutD : ∀ S (hS : S ∈ D), cut S = dualCutInBox (hdual S hS) := by
    intro S hS; exact dif_pos (hdual S hS)
  have hcardD : ∀ S ∈ D, (cut S).card = r := by
    intro S hS
    rw [hcutD S hS, dualCutInBox_card_eq_cutEdges (hne S hS), hr S hS]
  calc D.card
      ≤ (rayAnchorSet Λd i r).card * (2 * 2) ^ (2 * r) := by
        refine contour_count_le r D cut (rayAnchorSet Λd i r) ?_ ?_ ?_ hcardD ?_
        · -- injectivity
          intro S₁ hS₁ S₂ hS₂ heq
          rw [Finset.mem_coe] at hS₁ hS₂
          rw [hcutD S₁ hS₁, hcutD S₂ hS₂] at heq
          exact box_droplet_eq_of_dualCutInBox_eq hpre (hne S₁ hS₁) (hne S₂ hS₂)
            (hg S₁ hS₁) (hg S₂ hS₂) heq
        · -- subset of the edge finset
          intro S hS
          rw [hcutD S hS]; exact dualCutInBox_subset_edgeFinset _
        · -- connectivity (single orbit)
          intro S hS
          rw [hcutD S hS]
          exact dualCutInBox_isEdgeConnected_of_single_orbit (hdual S hS) (hone S hS)
        · -- anchored in the ray anchor set
          intro S hS
          rw [hcutD S hS]
          exact rayAnchorSet_cover (hi S hS) (hdual S hS) (by
            rw [← hcutD S hS]; exact hcardD S hS)
    _ ≤ r * (2 * 2) ^ (2 * r) :=
        Nat.mul_le_mul_right _ rayAnchorSet_card_le

/-- **The Peierls contour count from anchored dart reachability data**: the number of
neighbour-closed, ground-avoiding box droplets `S ∋ i` with box edge cut of size `r` is at most
`r · (2·2)^{2r}` when each ambient image `S.image Subtype.val` has anchored `DartReachable`
data supplying the common-box dual cut's edge-connectivity. This is the count-consumer form of the
direct route replacing the single-orbit `hone` hypothesis. -/
theorem peierls_contour_count_anchored {Λ Λd : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ}
    {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hdata : ∀ S (_ : S ∈ D),
      ∃ φ : {x : Fin 2 → ℤ // x ∈ S.image Subtype.val} →
          BoundaryDart (S.image Subtype.val),
        (∀ d : BoundaryDart (S.image Subtype.val),
          DartReachable (S.image Subtype.val) d (φ ⟨d.left, d.left_mem⟩)) ∧
        (∀ a b : {x : Fin 2 → ℤ // x ∈ S.image Subtype.val},
          (latticeGraph 2).Adj a.1 b.1 →
            DartReachable (S.image Subtype.val) (φ a) (φ b)) ∧
        (∀ a ∈ S.image Subtype.val, ∀ b ∈ S.image Subtype.val,
          ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b))
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) := by
  classical
  set cut : Finset ↑Λ → Finset (Sym2 ↑Λd) :=
    fun S => if h : dualSupport (S.image Subtype.val) ⊆ Λd then dualCutInBox h else ∅ with hcut
  have hcutD : ∀ S (hS : S ∈ D), cut S = dualCutInBox (hdual S hS) := by
    intro S hS; exact dif_pos (hdual S hS)
  have hcardD : ∀ S ∈ D, (cut S).card = r := by
    intro S hS
    rw [hcutD S hS, dualCutInBox_card_eq_cutEdges (hne S hS), hr S hS]
  calc D.card
      ≤ (rayAnchorSet Λd i r).card * (2 * 2) ^ (2 * r) := by
        refine contour_count_le r D cut (rayAnchorSet Λd i r) ?_ ?_ ?_ hcardD ?_
        · -- injectivity
          intro S₁ hS₁ S₂ hS₂ heq
          rw [Finset.mem_coe] at hS₁ hS₂
          rw [hcutD S₁ hS₁, hcutD S₂ hS₂] at heq
          exact box_droplet_eq_of_dualCutInBox_eq hpre (hne S₁ hS₁) (hne S₂ hS₂)
            (hg S₁ hS₁) (hg S₂ hS₂) heq
        · -- subset of the edge finset
          intro S hS
          rw [hcutD S hS]; exact dualCutInBox_subset_edgeFinset _
        · -- connectivity (anchored dart reachability)
          intro S hS
          rw [hcutD S hS]
          obtain ⟨φ, hanchor, hstep, hconn⟩ := hdata S hS
          exact dualCutInBox_isEdgeConnected_of_anchored (hdual S hS) φ hanchor hstep hconn
        · -- anchored in the ray anchor set
          intro S hS
          rw [hcutD S hS]
          exact rayAnchorSet_cover (hi S hS) (hdual S hS) (by
            rw [← hcutD S hS]; exact hcardD S hS)
    _ ≤ r * (2 * 2) ^ (2 * r) :=
        Nat.mul_le_mul_right _ rayAnchorSet_card_le

/-- **The Peierls contour count from the planar bond lemma**: the contour bound holds when each box
droplet supplies the planar bond hypothesis together with the two connectivity inputs — the inside
sites are connected inside the droplet (`hF`) and the outside sites are connected in the complement
(`hC`). This is the convergent route replacing the single-orbit `hone` hypothesis and the
`peierls_contour_count_anchored` first-exit anchor data: the connectivity supply is discharged via
`dualCutInBox_isEdgeConnected_of_bond` from the planar bond lemma instead of a single dart orbit. -/
theorem peierls_contour_count_of_bond {Λ Λd : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ}
    {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hbond : ∀ S ∈ D, PlanarBondHypothesis (S.image Subtype.val))
    (hF : ∀ S ∈ D, ∀ a ∈ S.image Subtype.val, ∀ b ∈ S.image Subtype.val,
      ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b)
    (hC : ∀ S ∈ D, ∀ a, a ∉ S.image Subtype.val → ∀ b, b ∉ S.image Subtype.val →
      ReachableOutside (S.image Subtype.val) a b)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) := by
  classical
  set cut : Finset ↑Λ → Finset (Sym2 ↑Λd) :=
    fun S => if h : dualSupport (S.image Subtype.val) ⊆ Λd then dualCutInBox h else ∅ with hcut
  have hcutD : ∀ S (hS : S ∈ D), cut S = dualCutInBox (hdual S hS) := by
    intro S hS; exact dif_pos (hdual S hS)
  have hcardD : ∀ S ∈ D, (cut S).card = r := by
    intro S hS
    rw [hcutD S hS, dualCutInBox_card_eq_cutEdges (hne S hS), hr S hS]
  calc D.card
      ≤ (rayAnchorSet Λd i r).card * (2 * 2) ^ (2 * r) := by
        refine contour_count_le r D cut (rayAnchorSet Λd i r) ?_ ?_ ?_ hcardD ?_
        · -- injectivity
          intro S₁ hS₁ S₂ hS₂ heq
          rw [Finset.mem_coe] at hS₁ hS₂
          rw [hcutD S₁ hS₁, hcutD S₂ hS₂] at heq
          exact box_droplet_eq_of_dualCutInBox_eq hpre (hne S₁ hS₁) (hne S₂ hS₂)
            (hg S₁ hS₁) (hg S₂ hS₂) heq
        · -- subset of the edge finset
          intro S hS
          rw [hcutD S hS]; exact dualCutInBox_subset_edgeFinset _
        · -- connectivity (planar bond lemma)
          intro S hS
          rw [hcutD S hS]
          exact dualCutInBox_isEdgeConnected_of_bond (hdual S hS) (hbond S hS) (hF S hS) (hC S hS)
        · -- anchored in the ray anchor set
          intro S hS
          rw [hcutD S hS]
          exact rayAnchorSet_cover (hi S hS) (hdual S hS) (by
            rw [← hcutD S hS]; exact hcardD S hS)
    _ ≤ r * (2 * 2) ^ (2 * r) :=
        Nat.mul_le_mul_right _ rayAnchorSet_card_le

end IsingModel
