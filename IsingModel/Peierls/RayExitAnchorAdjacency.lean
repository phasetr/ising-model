import IsingModel.Peierls.DartOfCut
import IsingModel.Peierls.RayExitAnchorStep

/-!
# Ray-exit anchor adjacency shadow reduction (FV §3.7.2)

`RayExitAnchorStep.lean` closes the horizontal `±e₀` same-ray cases of the later
`hshadow` input.  This file packages that result behind the 2D lattice adjacency case split:
an arbitrary adjacent pair of sites either has a shared ray-exit anchor edge, or it is one of the
two vertical `±e₁` cases that remain for separate local geometry.

It is only a case-reduction lemma.  It does not prove the vertical/frontier shadow cases and does
not address the same-left-site reachability input `hanchor`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- Adjacent sites have a ray-exit anchor shadow in the horizontal cases; the remaining cases are
the two vertical coordinate shifts. -/
theorem rayExitAnchorDartMap_adj_shared_or_vertical (x y : {x : Fin 2 → ℤ // x ∈ F})
    (hxy : (latticeGraph 2).Adj x.1 y.1) :
    (∃ v : Fin 2 → ℤ,
      v ∈ s((rayExitAnchorDartMap F x).tail, (rayExitAnchorDartMap F x).head) ∧
        v ∈ s((rayExitAnchorDartMap F y).tail, (rayExitAnchorDartMap F y).head)) ∨
      y.1 = x.1 + unitVec2 1 ∨ y.1 = x.1 - unitVec2 1 := by
  rcases latticeGraph2_adj_cases hxy with hy | hy | hy | hy
  · have hx1 : x.1 + unitVec2 0 ∈ F := by
      simp [← hy, y.2]
    obtain ⟨v, hvx, hvy⟩ := rayExitAnchorDartMap_add_e0_shared (F := F) x hx1
    left
    refine ⟨v, hvx, ?_⟩
    have hsub : (⟨x.1 + unitVec2 0, hx1⟩ : {x : Fin 2 → ℤ // x ∈ F}) = y :=
      Subtype.ext hy.symm
    simpa [hsub] using hvy
  · have hx0 : x.1 - unitVec2 0 ∈ F := by
      simp [← hy, y.2]
    obtain ⟨v, hvx, hvy⟩ := rayExitAnchorDartMap_sub_e0_shared (F := F) x hx0
    left
    refine ⟨v, hvx, ?_⟩
    have hsub : (⟨x.1 - unitVec2 0, hx0⟩ : {x : Fin 2 → ℤ // x ∈ F}) = y :=
      Subtype.ext hy.symm
    simpa [hsub] using hvy
  · exact Or.inr (Or.inl hy)
  · exact Or.inr (Or.inr hy)

end IsingModel
