import IsingModel.Peierls
import IsingModel.AmbientLattice

/-!
# Peierls argument along an infinite-volume exhaustion

This file bridges the finite-volume Peierls bound
(`IsingModel.prop_5_4_2_self_contained`, GJ §5.4, p. 83) with the
ambient / exhaustion framework from `IsingModel.AmbientLattice`.

## Main result

* `prop_5_4_2_along_exhaustion`: if, for every stage `n` of an
  exhaustion `Λ : Exhaustion V`, the induced graph on `Λ.volume n`
  is preconnected and the finite-volume hypotheses of
  `prop_5_4_2_self_contained` hold with a common Peierls constant
  `c`, then the Peierls bound holds pointwise along the exhaustion:
  for every `n`,
  `0 ≤ 1 - ⟨σ_{iₙ}⟩₊^{Λₙ,Bₙ} ≤ exp (-c β)`.

This is a first scaffolding step toward the genuine infinite-volume
lift of GJ Prop 5.4.2
(`0 ≤ 1 - ⟨σᵢ⟩₊^∞ ≤ exp (-c β)`, Glimm–Jaffe §5.4, p. 83):
subsequent PRs on the same branch will define a canonical boundary
and basepoint choice and take the `limsup`/`liminf` of the sequence.

## Reference

* J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral
  Point of View*, 2nd ed., Springer 1987, §5.4, p. 83.
-/

universe u

namespace IsingModel

variable {V : Type u} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **Prop 5.4.2 along an exhaustion** (GJ §5.4, p. 83, per-stage
form). For a graph `G : SimpleGraph V` with an exhaustion
`Λ : Exhaustion V`, if

* each induced graph `Ambient.inducedGraph G (Λ.volume n)` is preconnected
  and has a decidable adjacency and a `Fintype` edge set;
* `J, β > 0`;
* a per-stage non-empty boundary `B n : Finset ↑(Λ.volume n)` and
  basepoint `i n : ↑(Λ.volume n)` are supplied;
* the exponential bound condition holds uniformly with a common
  constant `c`,

then the Peierls bound holds pointwise along the exhaustion: for
every `n`,

`0 ≤ 1 - plusGibbsExpectation (Gₙ) ⟨J, 0, β⟩ (Bₙ) (σ ↦ sign (σ iₙ))
  ≤ Real.exp (-c * β)`.

The proof is a direct application of
`prop_5_4_2_self_contained` at each stage.

Subsequent PRs on this branch will (i) pick a canonical `B` and `i`
from the ambient geometry, and (ii) take the `limsup`/`liminf` to
express the genuine infinite-volume bound
`0 ≤ 1 - ⟨σᵢ⟩₊^∞ ≤ exp (-c β)`. -/
theorem prop_5_4_2_along_exhaustion
    (G : SimpleGraph V) (Λ : Ambient.Exhaustion V)
    [∀ n, DecidableRel (Ambient.inducedGraph G (Λ.volume n)).Adj]
    [∀ n, Fintype (Ambient.inducedGraph G (Λ.volume n)).edgeSet]
    (hconn : ∀ n, (Ambient.inducedGraph G (Λ.volume n)).Preconnected)
    (J β c : ℝ) (hβ : 0 < β) (hJ : 0 < J)
    (B : ∀ n, Finset (↑(Λ.volume n) : Type _))
    (hB : ∀ n, (B n).Nonempty)
    (i : ∀ n, (↑(Λ.volume n) : Type _))
    (hexp : ∀ n,
      2 * ((2 : ℝ) ^ Fintype.card (↑(Λ.volume n) : Type _)) *
          Real.exp (-2 * β * J) ≤
        Real.exp (-c * β)) :
    ∀ n,
      0 ≤ 1 - plusGibbsExpectation (Ambient.inducedGraph G (Λ.volume n))
              ⟨J, 0, β⟩ (B n) (fun σ => Spin.sign ℝ (σ (i n))) ∧
      1 - plusGibbsExpectation (Ambient.inducedGraph G (Λ.volume n))
            ⟨J, 0, β⟩ (B n) (fun σ => Spin.sign ℝ (σ (i n))) ≤
        Real.exp (-c * β) := fun n =>
  prop_5_4_2_self_contained (Ambient.inducedGraph G (Λ.volume n)) (hconn n)
    J β c hβ hJ (B n) (hB n) (i n) (hexp n)

end IsingModel
