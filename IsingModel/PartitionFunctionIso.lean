import IsingModel.GibbsMeasure
import IsingModel.Hamiltonian
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.BigOperators

/-!
# Partition function and Hamiltonian invariance under graph isomorphism

For a type equivalence `e : V ≃ W` and a finite simple graph
`G : SimpleGraph V`, the Hamiltonian and partition function of `G`
are preserved by the pushforward `G.map e.toEmbedding` (as graph on
`W`) up to reindexing of configurations along `e`.

This is infrastructure for the Glimm–Jaffe §4.6 thermodynamic-limit
proof: when relating `inducedGraph G (Λ₁ ∪ Λ₂)` (as a graph on
`↑(Λ₁ ∪ Λ₂)`) to `inducedGraph G Λ₁ ⊕g inducedGraph G Λ₂`
(as a graph on `↑Λ₁ ⊕ ↑Λ₂`) via
`Equiv.Finset.disjUnionEquiv`, the partition function identity
reduces to Hamiltonian invariance under the type transport proved
here.

## Main declarations

* `IsingModel.edgeSpin_map_equiv_sym2Map` — per-edge spin product
  pulls back through `Sym2.map e`.
* `IsingModel.externalFieldEnergy_map_equiv` — external-field energy
  invariance under `e : V ≃ W` (via `Fintype.sum_equiv`).
* `IsingModel.interactionEnergy_map_equiv` — interaction energy
  invariance via mathlib `edgeFinset_map`.
* `IsingModel.hamiltonian_map_equiv` — Hamiltonian invariance,
  combining the two.
* `IsingModel.partitionFunction_map_equiv` — `Z` invariance under
  `G.map e.toEmbedding`.
* `IsingModel.log_partitionFunction_map_equiv` — logarithmic form.
-/

namespace IsingModel

variable {V W : Type*}
variable {K : Type*} [Field K]

/-- Per-edge spin product is invariant under the `Sym2.map` pushforward:
`edgeSpin τ (e.sym2Map s) = edgeSpin (τ ∘ e) s` for any `e : V ↪ W`,
`τ : Config W`, and `s : Sym2 V`. -/
theorem edgeSpin_map_equiv_sym2Map (e : V ↪ W) (τ : Config W) (s : Sym2 V) :
    edgeSpin (K := K) τ (e.sym2Map s) = edgeSpin (τ ∘ e) s := by
  refine s.ind (fun a b => ?_)
  simp [edgeSpin, Function.Embedding.sym2Map_apply, Sym2.map_mk]

/-- External field energy is invariant under the equivalence `e : V ≃ W`
reindexing of sites. -/
theorem externalFieldEnergy_map_equiv [Fintype V] [Fintype W]
    (e : V ≃ W) (h : K) (τ : Config W) :
    externalFieldEnergy (ι := W) h τ
      = externalFieldEnergy (ι := V) h (τ ∘ e) := by
  unfold externalFieldEnergy
  congr 1
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

/-- Interaction energy is invariant under the `SimpleGraph.map e.toEmbedding`
pushforward along `e : V ≃ W`: the `(G.map e).edgeFinset`
equality to `G.edgeFinset.map e.toEmbedding.sym2Map` is derived
from mathlib's set-level `edgeSet_map` (the finset-level
`edgeFinset_map` cannot be used directly because the ambient
`Fintype` instance on `(G.map e).edgeSet` is supplied as a
hypothesis rather than the canonical one), and the per-edge spin
then transports via `edgeSpin_map_equiv_sym2Map`. -/
theorem interactionEnergy_map_equiv
    (e : V ≃ W) (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype (G.map e.toEmbedding).edgeSet]
    (J : K) (τ : Config W) :
    interactionEnergy (G.map e.toEmbedding) J τ
      = interactionEnergy G J (τ ∘ e) := by
  have hEF : (G.map e.toEmbedding).edgeFinset
      = G.edgeFinset.map e.toEmbedding.sym2Map := by
    apply Finset.coe_injective
    rw [SimpleGraph.coe_edgeFinset, Finset.coe_map, SimpleGraph.coe_edgeFinset]
    exact SimpleGraph.edgeSet_map e.toEmbedding G
  unfold interactionEnergy
  rw [hEF, Finset.sum_map]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact edgeSpin_map_equiv_sym2Map (K := K) e.toEmbedding τ s

/-- Hamiltonian invariance under graph iso transport along `e : V ≃ W`:
`hamiltonian (G.map e) p τ = hamiltonian G p (τ ∘ e)`. -/
theorem hamiltonian_map_equiv [LinearOrder K] [IsStrictOrderedRing K]
    [Fintype V] [Fintype W]
    (e : V ≃ W) (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype (G.map e.toEmbedding).edgeSet]
    (p : IsingParams K) (τ : Config W) :
    hamiltonian (G.map e.toEmbedding) p τ
      = hamiltonian G p (τ ∘ e) := by
  unfold hamiltonian
  rw [interactionEnergy_map_equiv e G p.J τ,
      externalFieldEnergy_map_equiv e p.h τ]

/-- **Partition function invariance under graph iso transport**:
for a type equivalence `e : V ≃ W` and a finite simple graph
`G : SimpleGraph V`, pushing forward along `e` leaves the partition
function unchanged:
`partitionFunction (G.map e.toEmbedding) p = partitionFunction G p`. -/
theorem partitionFunction_map_equiv
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype (G.map e.toEmbedding).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunction (G.map e.toEmbedding) p = partitionFunction G p := by
  unfold partitionFunction boltzmannWeight
  rw [← Equiv.sum_comp (Equiv.arrowCongr e (Equiv.refl Spin))
        (fun τ : Config W => Real.exp (-p.β * hamiltonian (G.map e.toEmbedding) p τ))]
  apply Finset.sum_congr rfl
  intro σ _
  have hτ : (Equiv.arrowCongr e (Equiv.refl Spin)) σ = σ ∘ e.symm := by
    funext w; simp [Equiv.arrowCongr]
  rw [hτ, hamiltonian_map_equiv e G p (σ ∘ e.symm)]
  have hcomp : (σ ∘ e.symm) ∘ e = σ := by funext v; simp
  rw [hcomp]

/-- Logarithmic form of `partitionFunction_map_equiv`. -/
theorem log_partitionFunction_map_equiv
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype (G.map e.toEmbedding).edgeSet]
    (p : IsingParams ℝ) :
    Real.log (partitionFunction (G.map e.toEmbedding) p)
      = Real.log (partitionFunction G p) := by
  rw [partitionFunction_map_equiv]

end IsingModel
