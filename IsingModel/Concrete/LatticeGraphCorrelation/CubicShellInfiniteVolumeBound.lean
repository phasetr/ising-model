import IsingModel.Concrete.LatticeGraphCorrelation.CubicPerStageIncrement
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMagAlongExConvergenceCiSup

/-!
# Cubic-shell `derivBound` bounded by an infinite-volume two-point sum (Issue #2965, Phase A→B)

Bounds the ball-boundary `derivBound` over a cubic-box edge set, evaluated on
finite-volume correlations of `inducedGraph (latticeGraph d) box_n`, by the same
edge sum with each finite-volume correlation replaced by its **infinite-volume**
pair-set correlation `correlationInfinite (latticeGraph d) (cubicExhaustion d)`
(a two-point function when the two sites are distinct; the `Finset` pair `{x,y}`
collapses to the one-site correlation when `x = y`).

Composes the abstract monotonicity `derivBound_le_of_correlation_le`
(`WeakBound.lean`) with the finite-volume ≤ infinite-volume bridge
`correlationAlongExhaustion_le_correlationInfinite_latticeGraph`. This moves the
per-stage increment bound (#2992/#2993) onto infinite-volume correlations, where
the Phase B spatial-decay/summability results (`#2966`) apply — separating the
`derivBound` algebra from the divergent-prefactor-sensitive decay analysis.

## Main declaration

* `IsingModel.Ambient.derivBound_inducedGraph_cubic_le_infiniteVolume_sum`.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- Edge sets of subgraphs over a cubic box subtype are finite (`Sym2` of a
`Fintype` is finite). Local instance supplying the `Fintype edgeSet` /
`∀ n, Fintype …` hypotheses of the abstract increment and of `correlationInfinite`
in the concrete cubic setting. -/
noncomputable local instance fintype_edgeSet_of_finite_ib {W : Type*} [Finite W]
    (G : SimpleGraph W) : Fintype G.edgeSet :=
  Fintype.ofFinite _

/-- **Finite-volume ≤ infinite-volume bridge on a cubic box**: for any pair of
sites of `box_n`, the finite-volume correlation in `inducedGraph (latticeGraph d)
box_n` is at most the infinite-volume two-point function. Specialises
`correlationAlongExhaustion_le_correlationInfinite_latticeGraph` by unfolding
`correlationAlongExhaustion` (the observable subset holds since both endpoints lie
in `box_n`) and matching the lifted pair via `liftFinset_pair`. -/
theorem correlation_inducedGraph_cubic_le_correlationInfinite (d : ℕ)
    (p : IsingParams ℝ) (n : ℕ) (α β : (↑(cubicBox d n) : Type _)) :
    correlation (inducedGraph (latticeGraph d) (cubicBox d n)) p {α, β}
      ≤ correlationInfinite (latticeGraph d) (cubicExhaustion d) p {α.val, β.val} := by
  have hsub : ({α.val, β.val} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
    change ({α.val, β.val} : Finset (Fin d → ℤ)) ⊆ cubicBox d n
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨α.property, β.property⟩
  have hle := correlationAlongExhaustion_le_correlationInfinite_latticeGraph d
    (cubicExhaustion d) p {α.val, β.val} n
  rwa [correlationAlongExhaustion, dif_pos hsub, correlationΛ,
    liftFinset_pair hsub α.property β.property] at hle

/-- **Cubic-shell `derivBound` bounded by an infinite-volume two-point sum**
(Issue #2965, Phase A→B link): for sites `r, s ∈ box_n` and any edge set `E₀` of
`inducedGraph (latticeGraph d) box_n`,
`derivBound … E₀ … ⟨r,_⟩ ⟨s,_⟩` is bounded by `β·J` times the edge sum of the
infinite-volume Lebowitz products
`g{r,a}·g{s,b} + g{r,b}·g{s,a} + g{r,s}·g{a,b}`, where
`g{x,y} = correlationInfinite (latticeGraph d) (cubicExhaustion d) p {x,y}`
(the infinite-volume pair-set correlation; a two-point function for distinct sites).
Instantiates `derivBound_le_of_correlation_le` with the infinite-volume bound
`c α β = g{α.val, β.val}` (symmetric by `Finset.pair_comm`, nonnegative by
`correlationInfinite_nonneg`, dominating finite-volume correlations by
`correlation_inducedGraph_cubic_le_correlationInfinite`). Combined with the
per-stage increment #2993, this yields `c_{k+1} − c_k` bounded by an
infinite-volume boundary sum, the input to the Phase B spatial-decay analysis. -/
theorem derivBound_inducedGraph_cubic_le_infiniteVolume_sum (d : ℕ)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ)
    (E₀ : Finset (Sym2 (↑(cubicBox d n) : Type _)))
    {r s : Fin d → ℤ} (hr : r ∈ cubicBox d n) (hs : s ∈ cubicBox d n) :
    derivBound (inducedGraph (latticeGraph d) (cubicBox d n)) E₀ p ⟨r, hr⟩ ⟨s, hs⟩
      ≤ p.β * p.J * ∑ e ∈ E₀, Sym2.lift ⟨fun a b =>
          correlationInfinite (latticeGraph d) (cubicExhaustion d) p {r, a.val} *
              correlationInfinite (latticeGraph d) (cubicExhaustion d) p {s, b.val} +
            correlationInfinite (latticeGraph d) (cubicExhaustion d) p {r, b.val} *
              correlationInfinite (latticeGraph d) (cubicExhaustion d) p {s, a.val} +
            correlationInfinite (latticeGraph d) (cubicExhaustion d) p {r, s} *
              correlationInfinite (latticeGraph d) (cubicExhaustion d) p {a.val, b.val},
          fun a b => by
            simp only [show ({a.val, b.val} : Finset (Fin d → ℤ)) = {b.val, a.val} from
              Finset.pair_comm _ _]
            ring⟩ e := by
  exact derivBound_le_of_correlation_le (inducedGraph (latticeGraph d) (cubicBox d n)) E₀ p hf
    ⟨r, hr⟩ ⟨s, hs⟩
    (fun α β => correlationInfinite (latticeGraph d) (cubicExhaustion d) p {α.val, β.val})
    (fun α β => by simp only [Finset.pair_comm α.val β.val])
    (fun α β => correlationInfinite_nonneg (latticeGraph d) (cubicExhaustion d) p hf _)
    (fun α β => correlation_inducedGraph_cubic_le_correlationInfinite d p n α β)

end Ambient
end IsingModel
