import IsingModel.Inequalities.VolumeMonotonicity
import IsingModel.Concrete.CubicExhaustion
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.Lattice

/-!
# `+` boundary expectation on a cubic box of ℤ^d (Issue #3565, PR 1)

The first step toward the infinite-volume `+` Gibbs state on ℤ^d: the **`+`
boundary expectation on a finite cubic box**, built from the conditioning
boundary-condition machinery (`gibbsExpectationBC`) on the finite ambient
`↑(cubicBox d m)`.

For an inner box index `n ≤ m`, `plusBoxExpectation d n m J h β φ` is the
expectation of `φ` under the Ising measure on the box `cubicBox d m` with the
**annulus `cubicBox d m ∖ cubicBox d n` frozen to `+`** (the `+` boundary
condition on the inner region `cubicBox d n`).  Concretely it is
`gibbsExpectationBC` over the induced cubic-lattice graph on `cubicBox d m`, with
inner region `plusBoxInterior d n m` and boundary configuration `plusConfig`.

Within a fixed ambient box `m`, growing the inner region `n` makes the `+`
expectation of a monotone observable decrease
(`plusBoxExpectation_antitone_interior`), the cubic-box instance of FV Lemma 3.22
(`gibbsExpectationBC_plus_volume_antitone`).  Lifting this to a genuine
thermodynamic limit (growing the ambient box `m` as well) is the subject of the
later PRs of Issue #3565.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
§3.6.2, Lemma 3.22, §6.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **Inner region of the `+` box state**: the sites of the ambient box
`cubicBox d m` that lie in the inner box `cubicBox d n`.  The annulus (the
complement) carries the frozen `+` boundary condition. -/
noncomputable def plusBoxInterior (d n m : ℕ) : Finset ↑(cubicBox d m) :=
  Finset.univ.filter (fun x => (x : Fin d → ℤ) ∈ cubicBox d n)

/-- **Monotonicity of the inner region**: `n₁ ≤ n₂ ⟹ plusBoxInterior d n₁ m ⊆
plusBoxInterior d n₂ m` (the inner cubic boxes nest). -/
theorem plusBoxInterior_subset (d : ℕ) {n₁ n₂ m : ℕ} (hn : n₁ ≤ n₂) :
    plusBoxInterior d n₁ m ⊆ plusBoxInterior d n₂ m := by
  intro x hx
  simp only [plusBoxInterior, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact cubicBox_mono d hn hx

/-- **`+` boundary expectation on a cubic box**: the expectation of `φ` under the
Ising measure on `cubicBox d m` with the annulus `cubicBox d m ∖ cubicBox d n`
frozen to `+` (the `+` boundary condition on the inner box `cubicBox d n`).  Built
from `gibbsExpectationBC` on the induced cubic-lattice graph, with uniform
coupling `J`. -/
noncomputable def plusBoxExpectation (d n m : ℕ) (J h β : ℝ)
    (φ : Config ↑(cubicBox d m) → ℝ) : ℝ :=
  gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d m))
    β (fun _ => J) h (plusBoxInterior d n m) (plusConfig ↑(cubicBox d m)) φ

/-- **Inner-region antitonicity of the cubic-box `+` state** (cubic-box instance of
FV Lemma 3.22): within a fixed ambient box `m`, the `+` boundary expectation of a
monotone observable decreases as the inner region grows,

`n₁ ≤ n₂ ⟹ plusBoxExpectation d n₂ m J h β φ ≤ plusBoxExpectation d n₁ m J h β φ`.

Direct application of `gibbsExpectationBC_plus_volume_antitone` to the nested inner
regions `plusBoxInterior d n₁ m ⊆ plusBoxInterior d n₂ m`. -/
theorem plusBoxExpectation_antitone_interior (d : ℕ) {n₁ n₂ m : ℕ} (hn : n₁ ≤ n₂)
    {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (φ : Config ↑(cubicBox d m) → ℝ) (hφ : Monotone φ) :
    plusBoxExpectation d n₂ m J h β φ ≤ plusBoxExpectation d n₁ m J h β φ := by
  unfold plusBoxExpectation
  exact gibbsExpectationBC_plus_volume_antitone
    (inducedGraph (IsingModel.latticeGraph d) (cubicBox d m)) hβ (fun _ => hJ)
    (plusBoxInterior_subset d hn) φ hφ

end Ambient

end IsingModel
