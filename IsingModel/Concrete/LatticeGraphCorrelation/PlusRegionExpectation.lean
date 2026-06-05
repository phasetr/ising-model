import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateAmbientIndep
import IsingModel.Concrete.LatticeGraphBED.NeighborDegree

/-!
# The region `+` expectation and its nearest-neighbour closure (Issue #3581)

Towards exhaustion independence of the `+`-state functional (FV §3.4 Theorem 3.17):
for a finite region `A ⊆ ℤ^d` we model the FV finite-volume `+` measure `μ⁺_A` —
the Ising measure in `A` with the configuration *outside* `A` frozen to `+1` — as a
`gibbsExpectationBC` on the **nearest-neighbour closure** `nnClosure d A = A ∪ ∂A`,
with the free region `A` and the boundary layer `∂A` frozen `+`.

* `nnClosure d A` — the region `A` together with all its lattice neighbours.
* `subset_nnClosure`, `nnClosure_neighbors_subset`, `nnClosure_mono` — its geometry.
* `regionLift d A` — the free region `A` viewed inside `↑(nnClosure d A)`.
* `plusRegionExpectation` — the region `+` expectation `μ⁺_A(O)`.
* `plusRegionExpectation_eq_on_ambient` — ambient independence: realised on any
  `Ω ⊇ nnClosure d A`.
* `plusRegionExpectation_antitone` — antitone in the region (growing `A` pushes the
  `+` boundary away, decreasing the monotone expectation; FV Lemma 3.22).
* `plusRegionExpectation_cubicBox_eq` — agrees with the cubic
  `plusBoxLocalExpectation n (n+1)` on `A = cubicBox d n`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17 (statement p. 95, proof pp. 102–103).
-/

namespace IsingModel

namespace Ambient

open Finset

variable {d : ℕ}

/-- **Nearest-neighbour closure** of a finite region: the region `A` together with
all lattice neighbours of its sites, `nnClosure d A = A ∪ ⋃_{a ∈ A} N(a)`.  This is
the smallest ambient on which the `+` boundary expectation with free region `A` is
well defined: the boundary layer `nnClosure d A ∖ A` carries the frozen `+`. -/
noncomputable def nnClosure (d : ℕ) (A : Finset (Fin d → ℤ)) : Finset (Fin d → ℤ) :=
  A ∪ A.biUnion (fun a => (IsingModel.latticeGraph d).neighborFinset a)

/-- The region is contained in its nearest-neighbour closure. -/
theorem subset_nnClosure (A : Finset (Fin d → ℤ)) : A ⊆ nnClosure d A :=
  Finset.subset_union_left

/-- **Neighbours of region sites lie in the closure**: every lattice neighbour `y` of
a site `k ∈ A` belongs to `nnClosure d A` — the shell-separation input for the
ambient screening. -/
theorem nnClosure_neighbors_subset {A : Finset (Fin d → ℤ)} {k : Fin d → ℤ} (hk : k ∈ A)
    {y : Fin d → ℤ} (hadj : (IsingModel.latticeGraph d).Adj k y) : y ∈ nnClosure d A := by
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_biUnion.mpr ⟨k, hk, (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj⟩

/-- **Monotonicity of the nearest-neighbour closure**: `A ⊆ A' ⟹ nnClosure d A ⊆
nnClosure d A'`. -/
theorem nnClosure_mono {A A' : Finset (Fin d → ℤ)} (h : A ⊆ A') :
    nnClosure d A ⊆ nnClosure d A' := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxA | hxN
  · exact subset_nnClosure A' (h hxA)
  · rcases Finset.mem_biUnion.mp hxN with ⟨a, haA, hxa⟩
    exact nnClosure_neighbors_subset (h haA)
      ((SimpleGraph.mem_neighborFinset _ _ _).mp hxa)

/-- **The closure of a cubic box sits inside the next box**: `nnClosure d (cubicBox d n)
⊆ cubicBox d (n+1)`, since a `cubicBox d n` site's neighbours lie in `cubicBox d
(n+1)` (`cubicBox_adj_mem_succ`). -/
theorem nnClosure_cubicBox_subset_succ (d n : ℕ) :
    nnClosure d (cubicBox d n) ⊆ cubicBox d (n + 1) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxA | hxN
  · exact cubicBox_mono d (Nat.le_succ n) hxA
  · rcases Finset.mem_biUnion.mp hxN with ⟨a, haA, hxa⟩
    exact cubicBox_adj_mem_succ haA ((SimpleGraph.mem_neighborFinset _ _ _).mp hxa)

/-- **The free region `A` viewed inside its closure** `↑(nnClosure d A)`: the inner
free region of the region `+` expectation, the closure sites whose value lies in
`A`. -/
noncomputable def regionLift (d : ℕ) (A : Finset (Fin d → ℤ)) :
    Finset (↑(nnClosure d A) : Type _) :=
  Finset.univ.filter (fun x => (x : Fin d → ℤ) ∈ A)

/-- Membership in `regionLift`: a closure site lies in `regionLift d A` iff its value
lies in `A`. -/
@[simp] theorem mem_regionLift {A : Finset (Fin d → ℤ)} {x : (↑(nnClosure d A) : Type _)} :
    x ∈ regionLift d A ↔ (x : Fin d → ℤ) ∈ A := by
  simp only [regionLift, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The region `+` expectation** `μ⁺_A(O)`: the Ising expectation of `O` on the
nearest-neighbour closure `nnClosure d A` with the free region `A` and the boundary
layer `nnClosure d A ∖ A` frozen to `+` — the FV finite-volume `+` measure `μ⁺_A`
with `+` boundary condition outside `A`. -/
noncomputable def plusRegionExpectation (A : Finset (Fin d → ℤ)) (J h β : ℝ)
    (O : LocalMonotoneObservable d) (hSA : O.S ⊆ A) : ℝ :=
  haveI : Fintype (inducedGraph (IsingModel.latticeGraph d) (nnClosure d A)).edgeSet :=
    Fintype.ofFinite _
  gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (nnClosure d A)) β
    (fun _ => J) h (regionLift d A) (plusConfig _) (O.lift (hSA.trans (subset_nnClosure A)))

/-- **Ambient independence of the region `+` expectation**: for any ambient
`Ω ⊇ nnClosure d A`, the `+` boundary expectation of `O` with free region `A` on `Ω`
equals the canonical `plusRegionExpectation A O` — the boundary layer outside `A` is
frozen `+` and the choice of ambient does not matter (FV Theorem 3.17). -/
theorem plusRegionExpectation_eq_on_ambient {A Ω : Finset (Fin d → ℤ)}
    (hΩ : nnClosure d A ⊆ Ω)
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Ω).edgeSet]
    {J h β : ℝ} (O : LocalMonotoneObservable d) (hSA : O.S ⊆ A) :
    gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) Ω) β (fun _ => J) h
        ((regionLift d A).map (subtypeInclEmb hΩ)) (plusConfig _)
        (O.lift ((hSA.trans (subset_nnClosure A)).trans hΩ))
      = plusRegionExpectation A J h β O hSA := by
  letI : Fintype (inducedGraph (IsingModel.latticeGraph d) (nnClosure d A)).edgeSet :=
    Fintype.ofFinite _
  unfold plusRegionExpectation
  refine gibbsExpectationBC_screening_of_neighbors hΩ (regionLift d A)
    (fun k hk y hadj => nnClosure_neighbors_subset (mem_regionLift.mp hk) hadj)
    (O.lift ((hSA.trans (subset_nnClosure A)).trans hΩ))
    (O.lift (hSA.trans (subset_nnClosure A))) (fun σ₁ σ₂ => ?_)
  change O.φ (restrictConfig ((hSA.trans (subset_nnClosure A)).trans hΩ)
      ((configEquivSubtypeProd hΩ).symm (σ₁, σ₂)))
    = O.φ (restrictConfig (hSA.trans (subset_nnClosure A)) σ₁)
  rw [restrictConfig_trans (hSA.trans (subset_nnClosure A)) hΩ,
    restrictConfig_configEquivSubtypeProd_symm]

/-- **Region antitonicity of the `+` expectation** (FV Lemma 3.22 / monotonicity in
the volume): for a monotone observable `O` supported in `A ⊆ A'`, growing the free
region pushes the `+` boundary further away, decreasing the expectation,

`plusRegionExpectation A' O ≤ plusRegionExpectation A O`.

Both regions are compared on the common ambient `nnClosure d A'` (via
`plusRegionExpectation_eq_on_ambient`), where the free regions nest and
`gibbsExpectationBC_plus_volume_antitone` applies. -/
theorem plusRegionExpectation_antitone {A A' : Finset (Fin d → ℤ)} (hAA' : A ⊆ A')
    {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (O : LocalMonotoneObservable d) (hSA : O.S ⊆ A) :
    plusRegionExpectation A' J h β O (hSA.trans hAA') ≤ plusRegionExpectation A J h β O hSA := by
  letI : Fintype (inducedGraph (IsingModel.latticeGraph d) (nnClosure d A')).edgeSet :=
    Fintype.ofFinite _
  rw [← plusRegionExpectation_eq_on_ambient (A := A) (nnClosure_mono hAA') O hSA]
  unfold plusRegionExpectation
  refine gibbsExpectationBC_plus_volume_antitone _ hβ (fun _ => hJ) ?_ _ (O.lift_monotone _)
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨k, hk, rfl⟩
  exact mem_regionLift.mpr (hAA' (mem_regionLift.mp hk))

/-- **Agreement with the cubic `+` local expectation**: on a cubic box `A = cubicBox d
n`, the region `+` expectation coincides with the cubic
`plusBoxLocalExpectation n (n+1)` (free inner box `cubicBox d n`, one boundary layer).
This connects the region functional to the cubic-exhaustion `+`-state. -/
theorem plusRegionExpectation_cubicBox_eq {n : ℕ} {J h β : ℝ}
    (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d n) :
    plusRegionExpectation (cubicBox d n) J h β O hS
      = plusBoxLocalExpectation n (n + 1) J h β O
          (hS.trans (cubicBox_mono d (Nat.le_succ n))) := by
  rw [← plusRegionExpectation_eq_on_ambient (nnClosure_cubicBox_subset_succ d n) O hS]
  unfold plusBoxLocalExpectation plusBoxExpectation
  have hreg : (regionLift d (cubicBox d n)).map
        (subtypeInclEmb (nnClosure_cubicBox_subset_succ d n))
      = plusBoxInterior d n (n + 1) := by
    ext x
    simp only [Finset.mem_map, mem_regionLift, subtypeInclEmb, subtypeIncl,
      Function.Embedding.coeFn_mk, mem_plusBoxInterior]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact hk
    · intro hx
      exact ⟨⟨x.val, subset_nnClosure _ hx⟩, hx, Subtype.ext rfl⟩
  rw [hreg]

end Ambient

end IsingModel
