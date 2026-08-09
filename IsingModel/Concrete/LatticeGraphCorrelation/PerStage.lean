import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.ComplexAnalyticity
import IsingModel.PeierlsInfinite
import IsingModel.AmbientComplexAnalyticity
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume

/-!
# ℤ^d per-stage Gibbs expectation, FKG, and the plus-boundary bound

Concrete `latticeGraph d` statements along an arbitrary `Ambient.Exhaustion` of `Fin d → ℤ`,
each of which requires a `Fintype` instance on the edge set induced at every stage.

The along-exhaustion Gibbs expectation of a family of observables unfolds, at every stage, to
the ordinary Gibbs expectation on the subgraph induced by that stage's volume; this identity
carries no `Prop`-typed hypothesis. The FKG inequality then holds stage by stage for a
parameter record satisfying `Ferromagnetic` and families that are non-negative and monotone
at every stage: the product of the along-exhaustion expectations is bounded by the
expectation of the product.

Finally, at zero external field with positive coupling and positive inverse temperature, with
every induced stage subgraph preconnected, a nonempty plus-boundary set and a distinguished
site chosen at each stage, and a Peierls-type exponential bound assumed stage by stage, the
plus-boundary expectation of the spin sign at the distinguished site, taken as a `liminf`
along the exhaustion, differs from `1` by at most that exponential.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `gibbsExpectationAlongExhaustion` unfolding**: equal to
`gibbsExpectation` on the `n`-th volume with the `n`-th family
member. -/
theorem gibbsExpectationAlongExhaustion_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (F : (n : ℕ) → IsingModel.Config (↑(Λ.volume n) : Type _) → ℝ) (n : ℕ) :
    Ambient.gibbsExpectationAlongExhaustion
        (IsingModel.latticeGraph d) Λ p F n
      = IsingModel.gibbsExpectation
          (Ambient.inducedGraph
            (IsingModel.latticeGraph d) (Λ.volume n)) p (F n) :=
  Ambient.gibbsExpectationAlongExhaustion_apply
    (IsingModel.latticeGraph d) Λ p F n

/-- **ℤ^d per-stage FKG along an exhaustion** (GJ §4.4):
for ferromagnetic `p` and per-stage nonneg monotone families
`F n, G_fn n : Config (↑(Λ.volume n)) → ℝ`, the FKG inequality holds at
every stage `n`. Pass-through of `fkg_ising_along_exhaustion`. -/
theorem fkg_ising_along_exhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (F G_fn : (n : ℕ) → IsingModel.Config (↑(Λ.volume n) : Type _) → ℝ)
    (hF_nn : ∀ n, 0 ≤ F n) (hG_nn : ∀ n, 0 ≤ G_fn n)
    (hF_mono : ∀ n, Monotone (F n)) (hG_mono : ∀ n, Monotone (G_fn n))
    (n : ℕ) :
    Ambient.gibbsExpectationAlongExhaustion
        (IsingModel.latticeGraph d) Λ p F n
      * Ambient.gibbsExpectationAlongExhaustion
          (IsingModel.latticeGraph d) Λ p G_fn n
      ≤ Ambient.gibbsExpectationAlongExhaustion
          (IsingModel.latticeGraph d) Λ p (fun k => F k * G_fn k) n :=
  Ambient.fkg_ising_along_exhaustion
    (IsingModel.latticeGraph d) Λ p hf F G_fn
    hF_nn hG_nn hF_mono hG_mono n

/-- **ℤ^d GJ §5.4 Prop 5.4.2 genuine ∞-vol `+`-BC bound** (Λ-induced,
`liminf` form): for any exhaustion `Λ : Ambient.Exhaustion (Fin d → ℤ)`
with per-stage `Preconnected` + `Fintype G_n.edgeSet` instances and the
Peierls exponential bound `hexp`, the `liminf`-based canonical ∞-vol
`+`-expectation of `σ ↦ Spin.sign ℝ (σ (i n))` satisfies
`1 − plusGibbsExpectationLiminf ≤ exp(-c·β)`. Pass-through of
`IsingModel.prop_5_4_2_plusGibbsExpectationLiminf_bound`, with
`DecidableRel` supplied via `classical`. -/
theorem prop_5_4_2_plusGibbsExpectationLiminf_bound_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (hconn : ∀ n, (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).Preconnected)
    (J β c : ℝ) (hβ : 0 < β) (hJ : 0 < J)
    (B : ∀ n, Finset (↑(Λ.volume n) : Type _))
    (hB : ∀ n, (B n).Nonempty)
    (i : ∀ n, (↑(Λ.volume n) : Type _))
    (hexp : ∀ n,
      2 * ((2 : ℝ) ^ Fintype.card (↑(Λ.volume n) : Type _)) *
          Real.exp (-2 * β * J) ≤
        Real.exp (-c * β)) :
    1 - IsingModel.plusGibbsExpectationLiminf
          (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) B
          (fun n σ => IsingModel.Spin.sign ℝ (σ (i n)))
      ≤ Real.exp (-c * β) := by
  classical
  exact IsingModel.prop_5_4_2_plusGibbsExpectationLiminf_bound
    (IsingModel.latticeGraph d) Λ hconn J β c hβ hJ B hB i hexp

end Ambient
end IsingModel
