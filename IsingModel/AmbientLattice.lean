import IsingModel.InfiniteVolume
import IsingModel.FreeEnergy

/-!
# Genuine infinite-volume framework: ambient lattice

The existing `IsingModel` framework parametrizes everything by a fixed
`Fintype ι`.  This file introduces a **genuinely infinite ambient
lattice** `V : Type*` (no `Fintype V` assumption) and defines the
finite-volume Ising model on any `Λ : Finset V` by instantiating the
existing framework on the Fintype `(↑Λ : Type _)`.

This is the foundation for the true thermodynamic limit (Phase 2), where
an exhaustion `Λₙ ↑ V` covers the whole ambient lattice.

## Design

- Ambient type `V` carries an ambient `SimpleGraph V` (the interaction
  graph), and we demand `DecidableEq V` + `DecidableRel G.Adj` so that
  finite restrictions remain decidable.
- For `Λ : Finset V`, the type `(↑Λ : Type _)` is Fintype (mathlib
  `Finset.instFintypeCoe`).  The induced subgraph
  `G.induce (↑Λ : Set V)` gives a `SimpleGraph (↑Λ : Type _)` with
  `Fintype edgeSet` derivable from the ambient `DecidableRel`.
- Correlations, partition functions, and free energies on `Λ` are
  defined by forwarding to the existing `IsingModel` constructors.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.2, §4.6 (the thermodynamic limit
  is stated over `Λ ↑ ℝᵈ`, i.e., an infinite ambient).
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ## Finite-volume configuration on `Λ`

Use `(↑Λ : Type _)` as the finite index type; this is a `Fintype`
(via `Finset.instFintypeCoe`). -/

/-- A configuration on a finite volume `Λ : Finset V`:
a function from `Λ` to `Spin`. -/
abbrev ConfigOn (Λ : Finset V) : Type _ := (↑Λ : Type _) → Spin

/-! ## Induced subgraph on `Λ`

For `G : SimpleGraph V`, the induced subgraph on `(↑Λ : Set V)` is a
`SimpleGraph (↑Λ : Type _)`. -/

/-- The induced subgraph of `G` on `Λ : Finset V`. -/
noncomputable def inducedGraph (G : SimpleGraph V) (Λ : Finset V) :
    SimpleGraph (↑Λ : Type _) :=
  G.induce (↑Λ : Set V)

/-! ## Partition function and correlation on `Λ`

Forward the existing `partitionFunction`, `correlation`, `freeEnergy`
definitions to the induced subgraph on `Λ`. -/

/-- The partition function on a finite volume `Λ`, instantiating the
existing `IsingModel.partitionFunction` on the induced subgraph. -/
noncomputable def partitionFunctionΛ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) : ℝ :=
  IsingModel.partitionFunction (inducedGraph G Λ) p

/-- The correlation function on a finite volume `Λ`, for a subset
`A : Finset (↑Λ)` of sites. -/
noncomputable def correlationΛ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) : ℝ :=
  IsingModel.correlation (inducedGraph G Λ) p A

/-- The free energy per site on a finite volume `Λ`. -/
noncomputable def freeEnergyΛ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) : ℝ :=
  IsingModel.freeEnergy (inducedGraph G Λ) p

/-! ## Basic lemmas (forwarded from existing framework)

Since the definitions are direct instantiations, the existing theorems
apply automatically under the appropriate instances. -/

/-- The partition function on `Λ` is positive. -/
theorem partitionFunctionΛ_pos (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) :
    0 < partitionFunctionΛ G Λ p :=
  IsingModel.partitionFunction_pos _ _

/-- The correlation on `Λ` is bounded: `|⟨σ^A⟩| ≤ 1`. -/
theorem abs_correlationΛ_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    |correlationΛ G Λ p A| ≤ 1 :=
  IsingModel.abs_correlation_le_one _ _ _

/-- The correlation on `Λ` is at most `1`. -/
theorem correlationΛ_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ G Λ p A ≤ 1 :=
  IsingModel.correlation_le_one _ _ _

/-- For ferromagnetic `p`, the correlation on `Λ` is non-negative
(GKS-I, lifted to the ambient framework). -/
theorem correlationΛ_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (A : Finset (↑Λ : Type _)) :
    0 ≤ correlationΛ G Λ p A :=
  gks_first _ _ hf _

/-! ## Thermodynamic limit along exhaustions

An **exhaustion** of the ambient lattice `V` by `G : SimpleGraph V` is
a monotone increasing sequence of finite volumes `Λₙ : ℕ → Finset V`
whose union covers all of `V`.  For each `n`, the finite-volume
correlation `correlationΛ G (Λₙ n) p A` is defined for
`A : Finset (↑(Λₙ n))`.

To speak of convergence of correlations along an exhaustion, we need
to compare correlations across different `Λ`s.  The simplest approach:
fix a finite set `A : Finset V` (subset of the ambient type), and
consider only exhaustions `Λₙ` such that `A ⊆ Λₙ` eventually
(`A ⊆ Λₙ` for all `n ≥ N` for some `N`).

For each such `n`, we can lift `A` to `A' : Finset (↑(Λₙ n))` via the
embedding `A ↪ Λₙ n` and evaluate `correlationΛ G (Λₙ n) p A'`. -/

/-- An exhaustion of `V` by an increasing sequence of finite volumes. -/
structure Exhaustion (V : Type*) where
  /-- The underlying sequence of finite volumes. -/
  volume : ℕ → Finset V
  /-- Monotone: `volume n ⊆ volume m` for `n ≤ m`. -/
  mono : Monotone volume
  /-- Eventually covers any finite set: for any `A : Finset V` there is
  `N` with `A ⊆ volume n` for all `n ≥ N`. -/
  exhaust : ∀ A : Finset V, ∃ N, ∀ n ≥ N, A ⊆ volume n

/-- Lift a finite set `A ⊆ V` to a finite set in `↑Λ` when `A ⊆ Λ`. -/
noncomputable def liftFinset {Λ : Finset V} (A : Finset V) (hA : A ⊆ Λ) :
    Finset (↑Λ : Type _) :=
  A.attach.image (fun ⟨v, hv⟩ => ⟨v, hA hv⟩)

/-- The correlation along an exhaustion, evaluated eventually (from the
first `n` with `A ⊆ volume n`). Returns a function `ℕ → ℝ` which equals
`correlationΛ G (volume n) p (liftFinset A _)` once `A ⊆ volume n`, and
is set arbitrarily (e.g. `0`) before. -/
noncomputable def correlationAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) : ℕ → ℝ :=
  fun n =>
    if h : A ⊆ Λ.volume n then
      correlationΛ G (Λ.volume n) p (liftFinset A h)
    else 0

/-- For any finite `A`, the correlation along an exhaustion is
eventually equal to the lifted correlation. -/
theorem correlationAlongExhaustion_eventually
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ hA : A ⊆ Λ.volume n,
      correlationAlongExhaustion G Λ p A n =
        correlationΛ G (Λ.volume n) p (liftFinset A hA) := by
  obtain ⟨N, hN⟩ := Λ.exhaust A
  refine ⟨N, fun n hn => ?_⟩
  have hA : A ⊆ Λ.volume n := hN n hn
  refine ⟨hA, ?_⟩
  simp [correlationAlongExhaustion, hA]

/-- The correlation along an exhaustion is bounded in absolute value
by `1` eventually. -/
theorem abs_correlationAlongExhaustion_eventually_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    ∀ᶠ n in Filter.atTop,
      |correlationAlongExhaustion G Λ p A n| ≤ 1 := by
  obtain ⟨N, hN⟩ := correlationAlongExhaustion_eventually G Λ p A
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hA, heq⟩ := hN n hn
  rw [heq]
  exact abs_correlationΛ_le_one G (Λ.volume n) p (liftFinset A hA)

end Ambient
end IsingModel
