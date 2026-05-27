import IsingModel.AmbientLatticeSum.PerStageIncrement
import IsingModel.Concrete.CubicExhaustion
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Cubic-exhaustion per-stage correlation increment (Issue #2965, Phase A)

Instantiates the abstract two-box per-stage increment
`correlation_pair_two_box_le_derivBound` (`PerStageIncrement.lean`) on the cubic
exhaustion stages `box_k ⊆ box_{k+1}` of `latticeGraph d`, expressed through
`correlationAlongExhaustion`. For a pair `r, s` interior to `box_k` (neither on a
cut edge of the `box_k`-slice), the successive correlation difference is bounded:

`correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r,s} (k+1)
  − correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r,s} k
  ≤ derivBound (inducedGraph (latticeGraph d) (box_{k+1})) (filter straddle) p ⟨r,_⟩ ⟨s,_⟩`.

This is the correlation-side `c_{k+1} − c_k` bound, one input toward the
volume-convergence rate program of GJ Lemma 17.5.2 (distinct from the
β-derivative provider that program also requires).

## Main declaration

* `IsingModel.Ambient.correlationAlongExhaustion_cubic_succ_sub_le_derivBound`.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- Edge sets of induced/derived subgraphs over a cubic box subtype are finite
(the vertex type is a `Fintype`, hence `Sym2` of it is finite). Local instance
supplying the `Fintype edgeSet` hypotheses of the abstract two-box increment in
the concrete cubic setting, where they are not synthesised automatically. Given a
lower priority than the canonical `inducedGraph (latticeGraph d) Λ` edge-set
instance (`LatticeBoundaryBED`), so the canonical instance is used for the outer
induced lattice graphs (keeping the per-stage increment's shell coherent with the
shell-bound lemmas) while this broad fallback still covers the inner
`deleteEdges`/`sum`/`map` graphs of the abstract increment. -/
noncomputable local instance (priority := 100) fintype_edgeSet_of_finite {W : Type*} [Finite W]
    (G : SimpleGraph W) : Fintype G.edgeSet :=
  Fintype.ofFinite _

/-- **Cubic-exhaustion per-stage correlation increment** (Issue #2965, Phase A):
for the cubic exhaustion of `latticeGraph d` and a pair `r, s` interior to the
stage `box_k` (neither endpoint on a cut edge of the `box_k`-slice), enlarging the
volume from `box_k` to `box_{k+1}` increases the pair correlation by at most the
ball-boundary `derivBound` over the cut edges of the slice. Instantiates the
abstract two-box increment `correlation_pair_two_box_le_derivBound` with
`G = latticeGraph d`, `T₁ = box_k`, `T₂ = box_{k+1}` (nested by `cubicBox_mono`),
unfolding `correlationAlongExhaustion` on both stages (both observable subsets hold
by `cubicBox_mono`) and matching the lifted observables via `liftFinset_pair`. -/
theorem correlationAlongExhaustion_cubic_succ_sub_le_derivBound (d : ℕ)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (k : ℕ)
    (hr : r ∈ cubicBox d k) (hs : s ∈ cubicBox d k)
    (hsep : ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem (⟨r, cubicBox_mono d (Nat.le_succ k) hr⟩ : (↑(cubicBox d (k + 1)) : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, cubicBox_mono d (Nat.le_succ k) hs⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e) :
    correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} (k + 1)
        - correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} k
      ≤ derivBound (inducedGraph (latticeGraph d) (cubicBox d (k + 1)))
          ((inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
            (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1))))) p
          ⟨r, cubicBox_mono d (Nat.le_succ k) hr⟩ ⟨s, cubicBox_mono d (Nat.le_succ k) hs⟩ := by
  have hsubk : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume k := by
    change ({r, s} : Finset (Fin d → ℤ)) ⊆ cubicBox d k
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hr, hs⟩
  have hsubk1 : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume (k + 1) :=
    hsubk.trans (cubicBox_mono d (Nat.le_succ k))
  rw [correlationAlongExhaustion, correlationAlongExhaustion,
    dif_pos hsubk1, dif_pos hsubk, correlationΛ, correlationΛ,
    liftFinset_pair hsubk1 (cubicBox_mono d (Nat.le_succ k) hr)
      (cubicBox_mono d (Nat.le_succ k) hs),
    liftFinset_pair hsubk hr hs]
  exact correlation_pair_two_box_le_derivBound (latticeGraph d)
    (cubicBox_mono d (Nat.le_succ k)) p hf hh hr hs hrs hsep

/-- **Tight cubic-exhaustion per-stage correlation increment** (Issue #2965,
Phase A→B): tight analogue of `correlationAlongExhaustion_cubic_succ_sub_le_derivBound`
bounding the successive correlation difference by the *tight* `derivBoundTight`
(cross products only) over the cut edges of the `box_k`-slice. Instantiates the
tight two-box increment `correlation_pair_two_box_le_derivBoundTight` on
`box_k ⊆ box_{k+1}`. The cross-product-only form is what makes `c_{k+1} − c_k`
summable under the infinite-volume spatial decay. -/
theorem correlationAlongExhaustion_cubic_succ_sub_le_derivBoundTight (d : ℕ)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (k : ℕ)
    (hr : r ∈ cubicBox d k) (hs : s ∈ cubicBox d k)
    (hsep : ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem (⟨r, cubicBox_mono d (Nat.le_succ k) hr⟩ : (↑(cubicBox d (k + 1)) : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, cubicBox_mono d (Nat.le_succ k) hs⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e) :
    correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} (k + 1)
        - correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} k
      ≤ derivBoundTight (inducedGraph (latticeGraph d) (cubicBox d (k + 1)))
          ((inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
            (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1))))) p
          ⟨r, cubicBox_mono d (Nat.le_succ k) hr⟩ ⟨s, cubicBox_mono d (Nat.le_succ k) hs⟩ := by
  have hsubk : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume k := by
    change ({r, s} : Finset (Fin d → ℤ)) ⊆ cubicBox d k
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hr, hs⟩
  have hsubk1 : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume (k + 1) :=
    hsubk.trans (cubicBox_mono d (Nat.le_succ k))
  rw [correlationAlongExhaustion, correlationAlongExhaustion,
    dif_pos hsubk1, dif_pos hsubk, correlationΛ, correlationΛ,
    liftFinset_pair hsubk1 (cubicBox_mono d (Nat.le_succ k) hr)
      (cubicBox_mono d (Nat.le_succ k) hs),
    liftFinset_pair hsubk hr hs]
  exact correlation_pair_two_box_le_derivBoundTight (latticeGraph d)
    (cubicBox_mono d (Nat.le_succ k)) p hf hh hr hs hrs hsep

end Ambient
end IsingModel
