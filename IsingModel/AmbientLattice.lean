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
open scoped symmDiff

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

/-- Membership characterization for `liftFinset`: a subtype element
`x : ↑Λ` lies in `liftFinset A hA` iff its underlying value `x.val`
lies in `A`. -/
theorem mem_liftFinset {Λ : Finset V} {A : Finset V} (hA : A ⊆ Λ)
    (x : (↑Λ : Type _)) :
    x ∈ liftFinset A hA ↔ x.val ∈ A := by
  simp only [liftFinset, Finset.mem_image, Finset.mem_attach, true_and]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨v, hv⟩, hxv⟩
    simpa [← hxv]
  · intro hx
    exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩

/-- `liftFinset` commutes with `symmDiff`: if `A, B ⊆ Λ` then
`liftFinset A hA Δ liftFinset B hB = liftFinset (A Δ B) hAB`
(where the subset `A Δ B ⊆ Λ` follows since `A Δ B ⊆ A ∪ B`).

Proof by extensional equality using `mem_liftFinset`. -/
theorem liftFinset_symmDiff {Λ : Finset V} {A B : Finset V}
    (hA : A ⊆ Λ) (hB : B ⊆ Λ) :
    liftFinset A hA ∆ liftFinset B hB =
      liftFinset (A ∆ B)
        (fun _ hx => (Finset.mem_symmDiff.mp hx).elim
          (fun h => hA h.1) (fun h => hB h.1)) := by
  ext x
  simp only [Finset.mem_symmDiff, mem_liftFinset]

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

/-- Unfold `correlationAlongExhaustion` when `A ⊆ Λ.volume n`:
it equals the lifted finite-volume correlation. -/
theorem correlationAlongExhaustion_of_subset
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {A : Finset V} {n : ℕ} (hA : A ⊆ Λ.volume n) :
    correlationAlongExhaustion G Λ p A n
      = correlationΛ G (Λ.volume n) p (liftFinset A hA) := by
  simp only [correlationAlongExhaustion, hA, dite_true]

/-- Unfold `correlationAlongExhaustion` when `A ⊄ Λ.volume n`:
it equals `0`. -/
theorem correlationAlongExhaustion_of_not_subset
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {A : Finset V} {n : ℕ} (hA : ¬ A ⊆ Λ.volume n) :
    correlationAlongExhaustion G Λ p A n = 0 := by
  simp only [correlationAlongExhaustion, hA, dite_false]

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

/-! ## Monotonicity in the ambient subgraph direction

For a fixed finite volume `Λ : Finset V`, if `G₁ ≤ G₂` as
`SimpleGraph V`, then the induced subgraphs satisfy
`G₁.induce Λ ≤ G₂.induce Λ` as `SimpleGraph (↑Λ)`.  Applying the
existing `partitionFunction_monotone_subgraph`,
`correlation_monotone_subgraph`, and `freeEnergy_monotone_subgraph`
on the finite `Fintype (↑Λ)` then gives monotonicity on `Λ` in the
ambient subgraph direction. -/

omit [DecidableEq V] in
/-- The induced subgraph is monotone in the ambient graph. -/
theorem inducedGraph_mono {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂)
    (Λ : Finset V) : inducedGraph G₁ Λ ≤ inducedGraph G₂ Λ := by
  intro u v hadj
  exact h hadj

/-- **Partition function ambient-subgraph monotonicity**:
for `G₁ ≤ G₂` (ambient) and ferromagnetic `p`,
`Z_{G₁,Λ} ≤ Z_{G₂,Λ}` on any finite volume `Λ`. -/
theorem partitionFunctionΛ_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Finset V)
    [Fintype (inducedGraph G₁ Λ).edgeSet]
    [Fintype (inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunctionΛ G₁ Λ p ≤ partitionFunctionΛ G₂ Λ p :=
  IsingModel.partitionFunction_monotone_subgraph (inducedGraph_mono h Λ) p hf

/-- **Correlation ambient-subgraph monotonicity**:
for `G₁ ≤ G₂` (ambient) and ferromagnetic `p`,
`⟨σ^A⟩_{G₁,Λ} ≤ ⟨σ^A⟩_{G₂,Λ}` on any finite volume `Λ` and
`A : Finset (↑Λ)`. -/
theorem correlationΛ_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Finset V)
    [Fintype (inducedGraph G₁ Λ).edgeSet]
    [Fintype (inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ G₁ Λ p A ≤ correlationΛ G₂ Λ p A :=
  IsingModel.correlation_monotone_subgraph (inducedGraph_mono h Λ) p hf A

/-- **Free energy ambient-subgraph monotonicity**:
for `G₁ ≤ G₂` (ambient) and ferromagnetic `p`,
`f_{G₁,Λ} ≤ f_{G₂,Λ}` on any finite volume `Λ`. -/
theorem freeEnergyΛ_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Finset V)
    [Fintype (inducedGraph G₁ Λ).edgeSet]
    [Fintype (inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyΛ G₁ Λ p ≤ freeEnergyΛ G₂ Λ p :=
  IsingModel.freeEnergy_monotone_subgraph (inducedGraph_mono h Λ) p hf

/-! ## Extension of a Λ₁-graph to Λ₂ (for volume-direction monotonicity)

For `Λ₁ ⊆ Λ₂` and `G : SimpleGraph V`, we construct a graph on
`(↑Λ₂)` whose edges are exactly the edges of `G.induce Λ₁`
embedded via the inclusion `↑Λ₁ ↪ ↑Λ₂`.  This graph is a subgraph
of `inducedGraph G Λ₂`, and will be used in the volume-direction
monotonicity argument to reduce to subgraph monotonicity on the
Fintype `(↑Λ₂)`.

The full volume-direction correlation monotonicity requires in
addition a configuration-factorization argument (the Boltzmann weight
on `extendGraphFromΛ₁` decouples between `↑Λ₁` and `↑(Λ₂\Λ₁)` sites,
giving an equality of correlations on the extended graph with those
on `inducedGraph G Λ₁`).  This PR establishes the extension graph
and its subgraph relation, which are the first technical ingredients. -/

omit [DecidableEq V] in
/-- The extension of `G.induce Λ₁` to `SimpleGraph (↑Λ₂)`:
edges are pairs `u, v : ↑Λ₂` with both endpoints in `Λ₁` and
adjacent in the ambient `G`. -/
noncomputable def extendGraphFromΛ₁ (G : SimpleGraph V)
    (Λ₁ Λ₂ : Finset V) : SimpleGraph (↑Λ₂ : Type _) where
  Adj u v := u.val ∈ Λ₁ ∧ v.val ∈ Λ₁ ∧ G.Adj u.val v.val
  symm := fun _ _ ⟨hu, hv, hadj⟩ => ⟨hv, hu, hadj.symm⟩
  loopless := ⟨fun _ ⟨_, _, hadj⟩ => hadj.ne rfl⟩

omit [DecidableEq V] in
/-- The extended Λ₁-graph is a subgraph of `inducedGraph G Λ₂`. -/
theorem extendGraphFromΛ₁_le_induce (G : SimpleGraph V)
    (Λ₁ Λ₂ : Finset V) :
    extendGraphFromΛ₁ G Λ₁ Λ₂ ≤ inducedGraph G Λ₂ := by
  intro u v hadj
  exact hadj.2.2

/-! ## Subtype / configuration helpers for volume-direction monotonicity

Infrastructure for comparing configurations on `↑Λ₁` and `↑Λ₂`
when `Λ₁ ⊆ Λ₂`:

* `subtypeIncl h12` — the canonical injection `↑Λ₁ → ↑Λ₂`.
* `restrictConfig h12 σ` — restriction of a `↑Λ₂`-configuration to `↑Λ₁`.
* `Λ₁subtypeEquiv h12` — the equivalence
  `{x : ↑Λ₂ // x.val ∈ Λ₁} ≃ ↑Λ₁`.

These are used to transport between configuration spaces in the
config-factorization proof of volume-direction monotonicity. -/

omit [DecidableEq V] in
/-- The canonical injection `↑Λ₁ → ↑Λ₂` when `Λ₁ ⊆ Λ₂`. -/
def subtypeIncl {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂) :
    (↑Λ₁ : Type _) → (↑Λ₂ : Type _) :=
  fun x => ⟨x.val, h12 x.property⟩

omit [DecidableEq V] in
/-- `subtypeIncl h12` is injective. -/
theorem subtypeIncl_injective {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂) :
    Function.Injective (subtypeIncl h12) := by
  intro x y h
  have : x.val = y.val := by
    have := congr_arg Subtype.val h
    simpa [subtypeIncl] using this
  exact Subtype.ext this

omit [DecidableEq V] in
/-- Restriction of a `↑Λ₂`-configuration to a `↑Λ₁`-configuration. -/
def restrictConfig {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    (σ : (↑Λ₂ : Type _) → Spin) : (↑Λ₁ : Type _) → Spin :=
  σ ∘ subtypeIncl h12

omit [DecidableEq V] in
/-- The equivalence `{x : ↑Λ₂ // x.val ∈ Λ₁} ≃ ↑Λ₁`
when `Λ₁ ⊆ Λ₂`.  The inverse reuses `subtypeIncl`. -/
def Λ₁subtypeEquiv {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂) :
    {x : (↑Λ₂ : Type _) // x.val ∈ Λ₁} ≃ (↑Λ₁ : Type _) where
  toFun := fun x => ⟨x.val.val, x.property⟩
  invFun := fun y => ⟨subtypeIncl h12 y, y.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

omit [DecidableEq V] in
@[simp]
theorem Λ₁subtypeEquiv_apply {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    (x : {x : (↑Λ₂ : Type _) // x.val ∈ Λ₁}) :
    (Λ₁subtypeEquiv h12 x : V) = x.val.val := rfl

omit [DecidableEq V] in
@[simp]
theorem Λ₁subtypeEquiv_symm_apply {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    (y : (↑Λ₁ : Type _)) :
    ((Λ₁subtypeEquiv h12).symm y : (↑Λ₂ : Type _)) = subtypeIncl h12 y := rfl

/-! ## Configuration factoring across `Λ₁ ⊆ Λ₂`

A configuration `σ : (↑Λ₂) → Spin` can be uniquely split into:
- its restriction to sites in `Λ₁` (via `Λ₁subtypeEquiv`), and
- its values on sites in `Λ₂ \ Λ₁`.

This decomposition is the key ingredient for the Boltzmann-weight
factoring argument underlying volume-direction monotonicity.

Uses `Equiv.piEquivPiSubtypeProd` (mathlib) on the predicate
`x.val ∈ Λ₁` over `↑Λ₂`, then transports the first component via
`Λ₁subtypeEquiv`. -/

/-- The decomposition equivalence
`((↑Λ₂) → Spin) ≃ ((↑Λ₁) → Spin) × ({x : ↑Λ₂ // x.val ∉ Λ₁} → Spin)`,
for `Λ₁ ⊆ Λ₂`.  Constructed by composing
`Equiv.piEquivPiSubtypeProd` (on the predicate `x.val ∈ Λ₁`) with
`Λ₁subtypeEquiv` on the first component. -/
noncomputable def configEquivSubtypeProd {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂) :
    ((↑Λ₂ : Type _) → Spin) ≃
      (((↑Λ₁ : Type _) → Spin) ×
        ({x : (↑Λ₂ : Type _) // x.val ∉ Λ₁} → Spin)) :=
  haveI : DecidablePred fun x : (↑Λ₂ : Type _) => x.val ∈ Λ₁ :=
    fun x => Finset.decidableMem x.val Λ₁
  (Equiv.piEquivPiSubtypeProd (fun x : (↑Λ₂ : Type _) => x.val ∈ Λ₁)
    (fun _ => Spin)).trans
    ((Equiv.arrowCongr (Λ₁subtypeEquiv h12) (Equiv.refl Spin)).prodCongr
      (Equiv.refl _))

/-- The first component of `configEquivSubtypeProd h12 σ` is the
restriction of `σ` to `↑Λ₁`. -/
theorem configEquivSubtypeProd_fst {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    (σ : (↑Λ₂ : Type _) → Spin) :
    (configEquivSubtypeProd h12 σ).1 = restrictConfig h12 σ := by
  ext v
  simp [configEquivSubtypeProd, restrictConfig, subtypeIncl,
    Equiv.piEquivPiSubtypeProd, Λ₁subtypeEquiv]

/-! ## Edge-spin preservation under `Sym2.map subtypeIncl`

For an edge `e : Sym2 (↑Λ₁)`, its image under `Sym2.map (subtypeIncl h12)`
is an edge on `↑Λ₂` with the same endpoint values.  Hence the
`edgeSpin` values coincide (with `restrictConfig` on the `↑Λ₁` side).

This is the pointwise identity underlying the eventual edge-sum
equality for the Boltzmann-weight factoring. -/

omit [DecidableEq V] in
/-- Pointwise edge-spin preservation:
`edgeSpin σ (Sym2.map (subtypeIncl h12) e) = edgeSpin (restrictConfig h12 σ) e`.

Generic in the coefficient field `K`; the `ℝ`-specialization arises
automatically when instantiated for the Ising Boltzmann weight. -/
theorem edgeSpin_subtypeIncl {K : Type*} [Field K]
    {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    (σ : (↑Λ₂ : Type _) → Spin) (e : Sym2 (↑Λ₁ : Type _)) :
    edgeSpin (K := K) σ (Sym2.map (subtypeIncl h12) e)
      = edgeSpin (K := K) (restrictConfig h12 σ) e := by
  refine Sym2.ind (fun u v => ?_) e
  simp [edgeSpin, restrictConfig, subtypeIncl]

/-! ## Edge-set transfer between `G.induce Λ₁` and `extendGraphFromΛ₁`

`Sym2.map (subtypeIncl h12)` gives an injection from
`Sym2 (↑Λ₁)` to `Sym2 (↑Λ₂)` that restricts to a bijection between
the edge sets of `G.induce Λ₁` and `extendGraphFromΛ₁ G Λ₁ Λ₂`.

Combined with `Finset.sum_bij` (or `sum_map`) and
`edgeSpin_subtypeIncl`, this yields the edge-sum equality underlying
the Boltzmann factoring. -/

omit [DecidableEq V] in
/-- The image of an induced-graph edge under `Sym2.map (subtypeIncl h12)`
is an edge of `extendGraphFromΛ₁`. -/
theorem mem_extendGraph_edgeSet_of_mem_induce
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    {e : Sym2 (↑Λ₁ : Type _)} (he : e ∈ (inducedGraph G Λ₁).edgeSet) :
    Sym2.map (subtypeIncl h12) e ∈ (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet := by
  refine Sym2.ind (fun u v he => ?_) e he
  rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
  rw [SimpleGraph.mem_edgeSet] at he
  exact ⟨u.property, v.property, he⟩

omit [DecidableEq V] in
/-- Conversely, every `extendGraphFromΛ₁` edge comes from a unique
induced-graph edge via `Sym2.map (subtypeIncl h12)`. -/
theorem exists_induce_edge_of_extendGraph
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    {e : Sym2 (↑Λ₂ : Type _)}
    (he : e ∈ (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet) :
    ∃ e' : Sym2 (↑Λ₁ : Type _),
      e' ∈ (inducedGraph G Λ₁).edgeSet ∧ Sym2.map (subtypeIncl h12) e' = e := by
  refine Sym2.ind (fun u v he => ?_) e he
  rw [SimpleGraph.mem_edgeSet] at he
  obtain ⟨hu, hv, hadj⟩ := he
  refine ⟨s(⟨u.val, hu⟩, ⟨v.val, hv⟩), ?_, ?_⟩
  · rw [SimpleGraph.mem_edgeSet]
    exact hadj
  · rw [Sym2.map_mk]
    rfl

/-! ## Edge sum equality and site sum splitting

Combine the edge-set bijection (PR #76) with `edgeSpin_subtypeIncl`
(PR #75) via `Finset.sum_bij` to obtain the edge-sum equality.
The site-sum splitting follows from `Fintype.sum_equiv` on
`configEquivSubtypeProd`, reducing the Boltzmann factoring to its
final step (PR #78). -/

/-- **Reindex helper for site sums**: for `Λ₁ ⊆ Λ₂`, the sum over the
subtype `{x : ↑Λ₂ // x.val ∈ Λ₁}` of a function evaluated at `σ v.val`
equals the sum over `↑Λ₁` of the same function with `restrictConfig`.

This is the core ingredient for site-sum splitting. -/
theorem sum_Λ₁_subtype_eq {K : Type*} [CommRing K]
    {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    (σ : (↑Λ₂ : Type _) → Spin) :
    ∑ v : {x : (↑Λ₂ : Type _) // x.val ∈ Λ₁}, Spin.sign K (σ v.val)
      = ∑ v : (↑Λ₁ : Type _), Spin.sign K (restrictConfig h12 σ v) := by
  refine Fintype.sum_equiv (Λ₁subtypeEquiv h12)
    (fun x : {y : (↑Λ₂ : Type _) // y.val ∈ Λ₁} => Spin.sign K (σ x.val))
    (fun v : (↑Λ₁ : Type _) => Spin.sign K (restrictConfig h12 σ v))
    (fun x => ?_)
  simp [restrictConfig, subtypeIncl, Λ₁subtypeEquiv]

/-- **Site-sum partition** on `↑Λ₂` along the `Λ₁/complement` partition.
Specialized form of `Fintype.sum_subtype_add_sum_subtype` for the
Ising model site-sum. -/
theorem siteSum_partition {K : Type*} [CommRing K]
    (Λ₁ Λ₂ : Finset V) (σ : (↑Λ₂ : Type _) → Spin) :
    ∑ v : (↑Λ₂ : Type _), Spin.sign K (σ v)
      = (∑ v : {x : (↑Λ₂ : Type _) // x.val ∈ Λ₁}, Spin.sign K (σ v.val))
        + ∑ v : {x : (↑Λ₂ : Type _) // ¬ (x.val ∈ Λ₁)}, Spin.sign K (σ v.val) := by
  classical
  exact (Fintype.sum_subtype_add_sum_subtype
    (fun x : (↑Λ₂ : Type _) => x.val ∈ Λ₁)
    (fun v => Spin.sign K (σ v))).symm

/-- **Site-sum splitting** on `↑Λ₂` along the `Λ₁/complement` partition,
with the Λ₁-part expressed via `restrictConfig` on `↑Λ₁`.
Combines `siteSum_partition` with `sum_Λ₁_subtype_eq`. -/
theorem siteSum_split {K : Type*} [CommRing K]
    {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    (σ : (↑Λ₂ : Type _) → Spin) :
    ∑ v : (↑Λ₂ : Type _), Spin.sign K (σ v)
      = (∑ v : (↑Λ₁ : Type _), Spin.sign K (restrictConfig h12 σ v))
        + ∑ v : {x : (↑Λ₂ : Type _) // ¬ (x.val ∈ Λ₁)}, Spin.sign K (σ v.val) := by
  rw [siteSum_partition Λ₁ Λ₂ σ, sum_Λ₁_subtype_eq h12 σ]

omit [DecidableEq V] in
/-- Edge-sum equality for the extendGraph via the Sym2.map-based
bijection.  Generic in the coefficient field `K`. -/
theorem extendGraph_edgeSum_eq {K : Type*} [Field K]
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (σ : (↑Λ₂ : Type _) → Spin) :
    ∑ e ∈ (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset, edgeSpin (K := K) σ e
      = ∑ e' ∈ (inducedGraph G Λ₁).edgeFinset,
          edgeSpin (K := K) (restrictConfig h12 σ) e' :=
  (Finset.sum_bij (fun e' _ => Sym2.map (subtypeIncl h12) e')
    (fun _ he' => by
      rw [SimpleGraph.mem_edgeFinset] at he' ⊢
      exact mem_extendGraph_edgeSet_of_mem_induce G h12 he')
    (fun _ _ _ _ heq =>
      Sym2.map.injective (subtypeIncl_injective h12) heq)
    (fun e he => by
      rw [SimpleGraph.mem_edgeFinset] at he
      obtain ⟨e', he', heq⟩ := exists_induce_edge_of_extendGraph G h12 he
      exact ⟨e', SimpleGraph.mem_edgeFinset.mpr he', heq⟩)
    (fun e' _ => (edgeSpin_subtypeIncl (K := K) h12 σ e').symm)).symm

/-! ## Hamiltonian factoring on `extendGraphFromΛ₁`

Combine `extendGraph_edgeSum_eq` and `siteSum_split` to decompose
the Hamiltonian on `extendGraphFromΛ₁` into a `G.induce Λ₁`-part
(with `restrictConfig`) plus a complement site contribution. -/

/-- Hamiltonian factoring: the Hamiltonian on `extendGraphFromΛ₁`
decomposes as the Hamiltonian on `inducedGraph G Λ₁` (with
`restrictConfig`) plus the complement site term. -/
theorem hamiltonian_extendGraph_factor
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ) (σ : (↑Λ₂ : Type _) → Spin) :
    hamiltonian (extendGraphFromΛ₁ G Λ₁ Λ₂) p σ
      = hamiltonian (inducedGraph G Λ₁) p (restrictConfig h12 σ)
        + (-p.h * ∑ v : {x : (↑Λ₂ : Type _) // ¬ (x.val ∈ Λ₁)},
            Spin.sign ℝ (σ v.val)) := by
  simp only [hamiltonian, interactionEnergy, externalFieldEnergy]
  rw [extendGraph_edgeSum_eq G h12 σ, siteSum_split h12 σ]
  ring

/-- Boltzmann weight factoring on `extendGraphFromΛ₁`: the weight on the
extended graph equals the weight on `inducedGraph G Λ₁` (with
`restrictConfig`) multiplied by an exponential factor over the
complement sites. -/
theorem boltzmannWeight_extendGraph_factor
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ) (σ : (↑Λ₂ : Type _) → Spin) :
    boltzmannWeight (extendGraphFromΛ₁ G Λ₁ Λ₂) p σ
      = boltzmannWeight (inducedGraph G Λ₁) p (restrictConfig h12 σ)
        * Real.exp (p.β * p.h *
            ∑ v : {x : (↑Λ₂ : Type _) // ¬ (x.val ∈ Λ₁)},
              Spin.sign ℝ (σ v.val)) := by
  simp only [boltzmannWeight]
  rw [hamiltonian_extendGraph_factor G h12 p σ, ← Real.exp_add]
  congr 1
  ring

/-! ## Spin product lift equality

For `A ⊆ Λ₁ ⊆ Λ₂`, the spin product of the `↑Λ₂`-lifted `A` evaluated
at a `↑Λ₂`-configuration equals the spin product of the `↑Λ₁`-lifted
`A` evaluated at the restricted configuration.

This is a key lemma for the correlation equality: the observable
`σ^A` transported through the `↑Λ₁ ↪ ↑Λ₂` embedding agrees with
the lifted one. -/

/-- The `↑Λ₂`-lift of `A ⊆ Λ₁` equals the image of the `↑Λ₁`-lift
under `subtypeIncl h12`. -/
theorem liftFinset_eq_image_subtypeIncl
    {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    {A : Finset V} (hA : A ⊆ Λ₁) :
    liftFinset A (hA.trans h12)
      = (liftFinset A hA).image (subtypeIncl h12) := by
  ext x
  simp only [liftFinset, Finset.mem_image, Finset.mem_attach,
    subtypeIncl, true_and]
  constructor
  · rintro ⟨⟨v, hv⟩, rfl⟩
    exact ⟨⟨v, hA hv⟩, ⟨⟨v, hv⟩, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨⟨v, hv⟩, rfl⟩, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

/-- **Spin product lift equality**: for `A ⊆ Λ₁ ⊆ Λ₂`,
`spinProduct (liftFinset A (hA.trans h12)) σ
  = spinProduct (liftFinset A hA) (restrictConfig h12 σ)`. -/
theorem spinProduct_lift_eq
    {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    {A : Finset V} (hA : A ⊆ Λ₁) (σ : (↑Λ₂ : Type _) → Spin) :
    spinProduct (liftFinset A (hA.trans h12)) σ
      = spinProduct (liftFinset A hA) (restrictConfig h12 σ) := by
  unfold spinProduct
  rw [liftFinset_eq_image_subtypeIncl h12 hA,
    Finset.prod_image
      (fun _ _ _ _ heq => subtypeIncl_injective h12 heq)]
  rfl

/-! ## Restriction of the config-equiv inverse

If `(σ₁, σ₂) : (↑Λ₁ → Spin) × (complement → Spin)` and
`σ := (configEquivSubtypeProd h12).symm (σ₁, σ₂)`, then
`restrictConfig h12 σ = σ₁`.  This is the content-bearing identity
that lets us split Boltzmann sums through the configuration
decomposition. -/

/-- The `restrictConfig` of the configEquiv-inverse of a pair recovers
the first component. -/
theorem restrictConfig_configEquivSubtypeProd_symm
    {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    (σ₁ : (↑Λ₁ : Type _) → Spin)
    (σ₂ : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁} → Spin) :
    restrictConfig h12 ((configEquivSubtypeProd h12).symm (σ₁, σ₂)) = σ₁ := by
  ext v
  simp [restrictConfig, subtypeIncl, configEquivSubtypeProd,
    Equiv.piEquivPiSubtypeProd, Λ₁subtypeEquiv, v.property]

/-- On the complement subtype, the configEquiv-inverse applied to a pair
gives the second component. -/
theorem configEquivSubtypeProd_symm_apply_compl
    {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    (σ₁ : (↑Λ₁ : Type _) → Spin)
    (σ₂ : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁} → Spin)
    (v : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁}) :
    (configEquivSubtypeProd h12).symm (σ₁, σ₂) v.val = σ₂ v := by
  simp [configEquivSubtypeProd, Equiv.piEquivPiSubtypeProd,
    Λ₁subtypeEquiv, v.property]

/-! ## Partition function factoring via config-equiv

Using Boltzmann factoring (PR #81) and config-equiv helpers
(PRs #82-84), express `partitionFunction extendGraph` as a product
of `partitionFunction inducedGraph Λ₁` and a complement factor. -/

/-- The complement factor used in the partition function factoring:
`F := ∑ σ₂ : (complement → Spin), exp(β·h · Σ_{v : C} sign(σ₂ v))`. -/
noncomputable def complementFactor
    {Λ₁ Λ₂ : Finset V} (_h12 : Λ₁ ⊆ Λ₂)
    (p : IsingParams ℝ) : ℝ :=
  ∑ σ₂ : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁} → Spin,
    Real.exp (p.β * p.h *
      ∑ v : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁}, Spin.sign ℝ (σ₂ v))

/-- **Partition function factoring**:
`Z_{extendGraphFromΛ₁} = Z_{inducedGraph Λ₁} · complementFactor`. -/
theorem partitionFunction_extendGraph_factor
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunction (extendGraphFromΛ₁ G Λ₁ Λ₂) p
      = partitionFunction (inducedGraph G Λ₁) p * complementFactor h12 p := by
  unfold partitionFunction complementFactor
  -- Reindex via configEquivSubtypeProd
  rw [← Fintype.sum_equiv (configEquivSubtypeProd h12).symm _
    (fun σ => boltzmannWeight (extendGraphFromΛ₁ G Λ₁ Λ₂) p σ)
    (fun x => rfl)]
  rw [Fintype.sum_prod_type]
  -- Rewrite summand using Boltzmann factoring and restrict identities
  have hsum : ∀ (σ₁ : (↑Λ₁ : Type _) → Spin)
      (σ₂ : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁} → Spin),
      boltzmannWeight (extendGraphFromΛ₁ G Λ₁ Λ₂) p
        ((configEquivSubtypeProd h12).symm (σ₁, σ₂))
      = boltzmannWeight (inducedGraph G Λ₁) p σ₁
        * Real.exp (p.β * p.h *
            ∑ v : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁}, Spin.sign ℝ (σ₂ v)) := by
    intro σ₁ σ₂
    simp_rw [boltzmannWeight_extendGraph_factor G h12 p,
      restrictConfig_configEquivSubtypeProd_symm,
      configEquivSubtypeProd_symm_apply_compl]
  simp_rw [hsum]
  rw [← Finset.sum_mul_sum]

/-- **Numerator factoring**: for `A ⊆ Λ₁`, the numerator for the
lifted spin product on `extendGraphFromΛ₁` equals the numerator on
`inducedGraph G Λ₁` times the complement factor. -/
theorem numerator_extendGraph_factor
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ)
    {A : Finset V} (hA : A ⊆ Λ₁) :
    numerator (extendGraphFromΛ₁ G Λ₁ Λ₂) p
        (spinProduct (liftFinset A (hA.trans h12)))
      = numerator (inducedGraph G Λ₁) p
          (spinProduct (liftFinset A hA))
        * complementFactor h12 p := by
  unfold numerator complementFactor
  rw [← Fintype.sum_equiv (configEquivSubtypeProd h12).symm _
    (fun σ => spinProduct (liftFinset A (hA.trans h12)) σ *
      boltzmannWeight (extendGraphFromΛ₁ G Λ₁ Λ₂) p σ)
    (fun x => rfl)]
  rw [Fintype.sum_prod_type]
  have hsum : ∀ (σ₁ : (↑Λ₁ : Type _) → Spin)
      (σ₂ : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁} → Spin),
      spinProduct (liftFinset A (hA.trans h12))
          ((configEquivSubtypeProd h12).symm (σ₁, σ₂))
        * boltzmannWeight (extendGraphFromΛ₁ G Λ₁ Λ₂) p
            ((configEquivSubtypeProd h12).symm (σ₁, σ₂))
      = spinProduct (liftFinset A hA) σ₁
          * boltzmannWeight (inducedGraph G Λ₁) p σ₁
        * Real.exp (p.β * p.h *
            ∑ v : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁}, Spin.sign ℝ (σ₂ v)) := by
    intro σ₁ σ₂
    simp_rw [spinProduct_lift_eq h12 hA,
      boltzmannWeight_extendGraph_factor G h12 p,
      restrictConfig_configEquivSubtypeProd_symm,
      configEquivSubtypeProd_symm_apply_compl]
    ring
  simp_rw [hsum]
  rw [← Finset.sum_mul_sum]

/-- **Correlation equality**: the correlation on `extendGraphFromΛ₁`
equals the correlation on `inducedGraph G Λ₁`, when `A ⊆ Λ₁`.

Proof: the complement factor in `numerator_extendGraph_factor` and
`partitionFunction_extendGraph_factor` is identical, so it cancels
in the ratio `correlation = numerator / partitionFunction`. -/
theorem correlationΛ_extendGraph_eq
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ)
    {A : Finset V} (hA : A ⊆ Λ₁) :
    correlation (extendGraphFromΛ₁ G Λ₁ Λ₂) p (liftFinset A (hA.trans h12))
      = correlation (inducedGraph G Λ₁) p (liftFinset A hA) := by
  have hZ : (0 : ℝ) < partitionFunction (inducedGraph G Λ₁) p :=
    partitionFunction_pos _ _
  have hF : (0 : ℝ) < complementFactor h12 p := by
    unfold complementFactor
    exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hZfac := partitionFunction_extendGraph_factor G h12 p
  have hnfac := numerator_extendGraph_factor G h12 p hA
  unfold correlation
  rw [gibbsExpectation_eq_div, gibbsExpectation_eq_div, hZfac, hnfac]
  field_simp

/-! ## Volume-direction monotonicity main theorem

Combining `correlationΛ_extendGraph_eq` (correlation equality via config
factoring) with `extendGraphFromΛ₁_le_induce` + `correlation_monotone_subgraph`
(subgraph monotonicity on `↑Λ₂`), we obtain the main volume-direction
monotonicity theorem. -/

/-- **Volume-direction monotonicity** (main theorem of the ambient
framework): for ferromagnetic `p`, `A ⊆ Λ₁ ⊆ Λ₂ : Finset V`,
`⟨σ^A⟩_{G, Λ₁} ≤ ⟨σ^A⟩_{G, Λ₂}`. -/
theorem correlationΛ_monotone_volume
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset V} (hA : A ⊆ Λ₁) :
    correlationΛ G Λ₁ p (liftFinset A hA)
      ≤ correlationΛ G Λ₂ p (liftFinset A (hA.trans h12)) := by
  classical
  haveI : Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet :=
    Fintype.ofFinite _
  unfold correlationΛ
  rw [← correlationΛ_extendGraph_eq G h12 p hA]
  exact correlation_monotone_subgraph
    (extendGraphFromΛ₁_le_induce G Λ₁ Λ₂) p hf _

/-! ## Convergence along an exhaustion

Apply `correlationΛ_monotone_volume` to show that the correlations
along an exhaustion converge. We use a shifted sequence
`n ↦ correlationΛ G (Λ.volume (n + N)) p (liftFinset A ...)` where
`N` is chosen so that `A ⊆ Λ.volume N` (from `Exhaustion.exhaust`).
Past `N`, `correlationAlongExhaustion` equals this shifted sequence. -/

/-- The shifted correlation sequence along an exhaustion: given
`N : ℕ` with `A ⊆ Λ.volume n` for `n ≥ N`, the sequence
`n ↦ correlationΛ G (Λ.volume (n + N)) p (liftFinset A ...)` is
monotone and bounded. -/
theorem correlationΛ_shifted_monotone_bounded
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset V} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    Monotone (fun n : ℕ =>
      correlationΛ G (Λ.volume (n + N)) p
        (liftFinset A (hN (n + N) (Nat.le_add_left N n))))
    ∧ ∀ n : ℕ,
      correlationΛ G (Λ.volume (n + N)) p
        (liftFinset A (hN (n + N) (Nat.le_add_left N n))) ≤ 1 := by
  refine ⟨?_, ?_⟩
  · intro n m hnm
    have hΛmono : Λ.volume (n + N) ⊆ Λ.volume (m + N) :=
      Λ.mono (Nat.add_le_add_right hnm N)
    exact correlationΛ_monotone_volume G hΛmono p hf
      (hN (n + N) (Nat.le_add_left N n))
  · intro n
    exact correlationΛ_le_one _ _ _ _

/-- **Tendsto convergence of the shifted correlation sequence**:
the shifted sequence (monotone and bounded by PR #88) converges
to its supremum by `tendsto_atTop_ciSup`. -/
theorem correlationΛ_shifted_tendsto
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset V} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    ∃ L : ℝ, Filter.Tendsto
      (fun m : ℕ => correlationΛ G (Λ.volume (m + N)) p
        (liftFinset A (hN (m + N) (Nat.le_add_left N m))))
      Filter.atTop (nhds L) := by
  obtain ⟨hmono, hbdd⟩ := correlationΛ_shifted_monotone_bounded G Λ p hf hN
  exact ⟨_, tendsto_atTop_ciSup hmono ⟨1, fun _ ⟨m, hm⟩ => hm ▸ hbdd m⟩⟩

/-- **Global monotonicity of `correlationAlongExhaustion`**:
because (1) for `n` where `A ⊆ Λ.volume n` fails, it equals 0;
(2) when it holds, `correlationΛ ≥ 0` by GKS-I; and (3) when both
endpoints satisfy the inclusion, `correlationΛ_monotone_volume`
(PR #87) applies. -/
theorem correlationAlongExhaustion_monotone
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    Monotone (correlationAlongExhaustion G Λ p A) := by
  intro n m hnm
  by_cases hAn : A ⊆ Λ.volume n
  · by_cases hAm : A ⊆ Λ.volume m
    · rw [correlationAlongExhaustion_of_subset G Λ p hAn,
          correlationAlongExhaustion_of_subset G Λ p hAm]
      exact correlationΛ_monotone_volume G (Λ.mono hnm) p hf hAn
    · exact absurd (hAn.trans (Λ.mono hnm)) hAm
  · rw [correlationAlongExhaustion_of_not_subset G Λ p hAn]
    by_cases hAm : A ⊆ Λ.volume m
    · rw [correlationAlongExhaustion_of_subset G Λ p hAm]
      exact correlationΛ_nonneg G (Λ.volume m) p hf _
    · rw [correlationAlongExhaustion_of_not_subset G Λ p hAm]

/-- **Global upper bound of `correlationAlongExhaustion` by 1**:
either the value is 0 (when `A ⊄ Λ.volume n`) or it is bounded
by `correlationΛ_le_one`. -/
theorem correlationAlongExhaustion_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G Λ p A n ≤ 1 := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ p hAn]
    exact correlationΛ_le_one _ _ _ _
  · rw [correlationAlongExhaustion_of_not_subset G Λ p hAn]
    norm_num

/-- **Range is bounded above by 1**: the range of the sequence
`correlationAlongExhaustion G Λ p A` is bounded above. Witness `1`
via `correlationAlongExhaustion_le_one`. -/
theorem correlationAlongExhaustion_bddAbove
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    BddAbove (Set.range (correlationAlongExhaustion G Λ p A)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact correlationAlongExhaustion_le_one G Λ p A n

/-- **Convergence of correlation along an exhaustion (explicit limit)**:
for a ferromagnetic Ising model and any exhaustion `Λₙ ↑ V` of an
ambient type `V`, the sequence `correlationAlongExhaustion` converges
to its supremum as `n → ∞`.

The limit is `⨆ n, correlationAlongExhaustion G Λ p A n`; this
exposes the limit's identity (as a supremum) so it can be related
to the thermodynamic-limit correlation once `Λ.exhaust` is used to
identify `A` with a subset of some `Λ.volume N`.

Note: this theorem itself only uses `Λ.mono` (monotonicity of the
exhaustion); `Λ.exhaust` is not required for convergence alone,
but is needed in downstream physical identifications of `L`. -/
theorem correlationAlongExhaustion_tendsto_ciSup
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    Filter.Tendsto (correlationAlongExhaustion G Λ p A)
      Filter.atTop (nhds (⨆ n, correlationAlongExhaustion G Λ p A n)) := by
  exact tendsto_atTop_ciSup
    (correlationAlongExhaustion_monotone G Λ p hf A)
    (correlationAlongExhaustion_bddAbove G Λ p A)

/-- **Convergence of correlation along an exhaustion (existential form)**:
thin wrapper around `correlationAlongExhaustion_tendsto_ciSup`. Use
the `_tendsto_ciSup` form when the identity of `L` as a supremum is
needed (e.g. for physical identification with the thermodynamic limit). -/
theorem correlationAlongExhaustion_convergent
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    ∃ L : ℝ, Filter.Tendsto
      (correlationAlongExhaustion G Λ p A)
      Filter.atTop (nhds L) :=
  ⟨_, correlationAlongExhaustion_tendsto_ciSup G Λ p hf A⟩

/-! ## Infinite-volume correlation function

The supremum exposed by `correlationAlongExhaustion_tendsto_ciSup`
is, by GKS-I and `Λ.exhaust`, the thermodynamic-limit correlation
for ferromagnetic Ising models on an ambient `V`.  We package it as
a `noncomputable def` and record its basic properties. -/

/-- **Infinite-volume correlation function**: for a ferromagnetic
Ising model on an ambient type `V` with an exhaustion `Λ` and a
finite `A : Finset V`,
`correlationInfinite G Λ p A := ⨆ n, correlationAlongExhaustion G Λ p A n`.
This is the thermodynamic-limit correlation identified via
`Λ.exhaust` (any finite `A` lies in some `Λ.volume N`). -/
noncomputable def correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) : ℝ :=
  ⨆ n, correlationAlongExhaustion G Λ p A n

/-- **Tendsto to infinite-volume correlation** (primary form):
`correlationAlongExhaustion` converges to `correlationInfinite`.
Restatement of `correlationAlongExhaustion_tendsto_ciSup` in terms
of the canonical `correlationInfinite` name. -/
theorem tendsto_correlationAlongExhaustion_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    Filter.Tendsto (correlationAlongExhaustion G Λ p A)
      Filter.atTop (nhds (correlationInfinite G Λ p A)) :=
  correlationAlongExhaustion_tendsto_ciSup G Λ p hf A

/-- **Upper bound**: `correlationInfinite ≤ 1`. Pointwise bound from
`correlationAlongExhaustion_le_one` + `ciSup_le`. -/
theorem correlationInfinite_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    correlationInfinite G Λ p A ≤ 1 := by
  refine ciSup_le ?_
  intro n
  exact correlationAlongExhaustion_le_one G Λ p A n

/-- **Nonnegativity** (ferromagnetic): `correlationInfinite ≥ 0`.
Uses `Λ.exhaust`: pick `N` with `A ⊆ Λ.volume N`; then
`correlationAlongExhaustion G Λ p A N ≥ 0` by GKS-I, and this is
a lower bound for the supremum (so the supremum is also `≥ 0`). -/
theorem correlationInfinite_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    0 ≤ correlationInfinite G Λ p A := by
  obtain ⟨N, hN⟩ := Λ.exhaust A
  have hA : A ⊆ Λ.volume N := hN N le_rfl
  have hval : 0 ≤ correlationAlongExhaustion G Λ p A N := by
    rw [correlationAlongExhaustion_of_subset G Λ p hA]
    exact correlationΛ_nonneg G (Λ.volume N) p hf _
  exact hval.trans (le_ciSup (correlationAlongExhaustion_bddAbove G Λ p A) N)

/-- **Tendsto of the lifted `correlationΛ` sequence (explicit form)**:
given an explicit `N` and a hypothesis `hN : ∀ n ≥ N, A ⊆ Λ.volume n`,
the sequence `m ↦ correlationΛ G (Λ.volume (m+N)) p (liftFinset A …)`
converges to `correlationInfinite G Λ p A`.

The shifted sequence coincides with `correlationAlongExhaustion` on
indices `≥ N` (both branches of the dite agree since `A ⊆ Λ.volume (m+N)`),
and the base sequence's limit is `correlationInfinite` by
`tendsto_correlationAlongExhaustion_correlationInfinite`. -/
theorem tendsto_correlationΛ_correlationInfinite_of_subset
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset V} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    Filter.Tendsto
      (fun m : ℕ => correlationΛ G (Λ.volume (m + N)) p
        (liftFinset A (hN (m + N) (Nat.le_add_left N m))))
      Filter.atTop (nhds (correlationInfinite G Λ p A)) := by
  have hbase := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf A
  have hshift :
      Filter.Tendsto (fun m : ℕ => correlationAlongExhaustion G Λ p A (m + N))
        Filter.atTop (nhds (correlationInfinite G Λ p A)) :=
    hbase.comp (Filter.tendsto_add_atTop_nat N)
  refine hshift.congr ?_
  intro m
  have hA : A ⊆ Λ.volume (m + N) := hN (m + N) (Nat.le_add_left N m)
  exact correlationAlongExhaustion_of_subset G Λ p hA

/-- **Tendsto of the lifted `correlationΛ` sequence (corollary)**:
using `Λ.exhaust` to produce an `N` with `A ⊆ Λ.volume n` for `n ≥ N`,
the sequence `m ↦ correlationΛ G (Λ.volume (m+N)) p (liftFinset A …)`
converges to `correlationInfinite G Λ p A`.

This is the physical statement: as the volume grows, the finite-volume
correlation converges to the thermodynamic-limit correlation. -/
theorem tendsto_correlationΛ_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    ∃ N : ℕ, ∃ hN : ∀ n ≥ N, A ⊆ Λ.volume n,
      Filter.Tendsto
        (fun m : ℕ => correlationΛ G (Λ.volume (m + N)) p
          (liftFinset A (hN (m + N) (Nat.le_add_left N m))))
        Filter.atTop (nhds (correlationInfinite G Λ p A)) := by
  obtain ⟨N, hN⟩ := Λ.exhaust A
  exact ⟨N, hN, tendsto_correlationΛ_correlationInfinite_of_subset G Λ p hf hN⟩

/-! ## Exhaustion-independence of `correlationInfinite`

Although `correlationInfinite` is defined as a supremum tied to a
specific `Λ`, the value does not depend on the choice of exhaustion:
any two exhaustions yield the same thermodynamic-limit correlation. -/

/-- **Key sandwich lemma**: every value of `correlationAlongExhaustion`
along one exhaustion is bounded above by `correlationInfinite` along
another exhaustion of the same ambient type.

Proof sketch: if `A ⊆ Λ'.volume n`, apply `Λ.exhaust` to the finite
set `Λ'.volume n` to get `m` with `Λ'.volume n ⊆ Λ.volume m`; then
`correlationΛ_monotone_volume` sandwiches the two finite-volume
correlations, and `le_ciSup` moves from `Λ.volume m` to the supremum.
Otherwise `correlationAlongExhaustion Λ' n = 0 ≤ correlationInfinite Λ`
via `correlationInfinite_nonneg`. -/
theorem correlationAlongExhaustion_le_correlationInfinite_of_other
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G Λ' p A n ≤ correlationInfinite G Λ p A := by
  by_cases hAn : A ⊆ Λ'.volume n
  · -- A ⊆ Λ'.volume n: use Λ.exhaust on Λ'.volume n
    obtain ⟨m, hm⟩ := Λ.exhaust (Λ'.volume n)
    have hsubset : Λ'.volume n ⊆ Λ.volume m := hm m le_rfl
    have hAm : A ⊆ Λ.volume m := hAn.trans hsubset
    have hmono :
        correlationΛ G (Λ'.volume n) p (liftFinset A hAn) ≤
          correlationΛ G (Λ.volume m) p (liftFinset A hAm) :=
      correlationΛ_monotone_volume G hsubset p hf hAn
    calc correlationAlongExhaustion G Λ' p A n
        = correlationΛ G (Λ'.volume n) p (liftFinset A hAn) :=
          correlationAlongExhaustion_of_subset G Λ' p hAn
      _ ≤ correlationΛ G (Λ.volume m) p (liftFinset A hAm) := hmono
      _ = correlationAlongExhaustion G Λ p A m :=
          (correlationAlongExhaustion_of_subset G Λ p hAm).symm
      _ ≤ correlationInfinite G Λ p A :=
          le_ciSup (correlationAlongExhaustion_bddAbove G Λ p A) m
  · -- A ⊄ Λ'.volume n: LHS = 0 ≤ correlationInfinite (nonneg)
    rw [correlationAlongExhaustion_of_not_subset G Λ' p hAn]
    exact correlationInfinite_nonneg G Λ p hf A

/-- **Exhaustion-independence** of `correlationInfinite`: for any two
exhaustions `Λ, Λ'` of the same ambient type `V`, the thermodynamic-limit
correlation is the same:
`correlationInfinite G Λ p A = correlationInfinite G Λ' p A`.

Proof: both `≤` directions by `ciSup_le` applied to the sandwich
lemma `correlationAlongExhaustion_le_correlationInfinite_of_other`. -/
theorem correlationInfinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    correlationInfinite G Λ p A = correlationInfinite G Λ' p A := by
  refine le_antisymm ?_ ?_
  · refine ciSup_le ?_
    intro n
    exact correlationAlongExhaustion_le_correlationInfinite_of_other
      G Λ' Λ p hf A n
  · refine ciSup_le ?_
    intro n
    exact correlationAlongExhaustion_le_correlationInfinite_of_other
      G Λ Λ' p hf A n

/-! ## Ambient-subgraph monotonicity of infinite-volume correlation

Finite-volume monotonicity in the ambient subgraph
(`correlationΛ_monotone_ambient_subgraph`, PR #58) lifts to the
thermodynamic-limit correlation: for ferromagnetic Ising on an
ambient type `V` and exhaustion `Λ`, `G₁ ≤ G₂` implies
`correlationInfinite G₁ Λ p A ≤ correlationInfinite G₂ Λ p A`. -/

/-- **Ambient-subgraph monotonicity of `correlationAlongExhaustion`**:
if `G₁ ≤ G₂` then the exhaustion sequence is pointwise monotone in
the ambient subgraph. -/
theorem correlationAlongExhaustion_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G₁ Λ p A n
      ≤ correlationAlongExhaustion G₂ Λ p A n := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G₁ Λ p hAn,
        correlationAlongExhaustion_of_subset G₂ Λ p hAn]
    exact correlationΛ_monotone_ambient_subgraph h (Λ.volume n) p hf _
  · rw [correlationAlongExhaustion_of_not_subset G₁ Λ p hAn,
        correlationAlongExhaustion_of_not_subset G₂ Λ p hAn]

/-- **Ambient-subgraph monotonicity of `correlationInfinite`**:
if `G₁ ≤ G₂` then
`correlationInfinite G₁ Λ p A ≤ correlationInfinite G₂ Λ p A`.

Proof: pointwise monotonicity of the exhaustion sequence
(`correlationAlongExhaustion_monotone_ambient_subgraph`) combined
with `le_ciSup` and `ciSup_le`. -/
theorem correlationInfinite_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    correlationInfinite G₁ Λ p A ≤ correlationInfinite G₂ Λ p A := by
  refine ciSup_le ?_
  intro n
  exact (correlationAlongExhaustion_monotone_ambient_subgraph h Λ p hf A n).trans
    (le_ciSup (correlationAlongExhaustion_bddAbove G₂ Λ p A) n)

/-! ## GKS-II (second Griffiths inequality) at infinite volume

Lift the finite-volume second Griffiths inequality (`gks_second`,
`Inequalities/GKS.lean`) to the thermodynamic limit. For ferromagnetic
Ising and any two finite subsets `A, B`,
`correlationInfinite A * correlationInfinite B ≤ correlationInfinite (A ∆ B)`.

Reference: Glimm-Jaffe, *Quantum Physics* §4.2 Theorem 4.2.3 (GKS-II
for the infinite-volume limit).  Friedli-Velenik Thm 3.49 for the
finite-volume version. -/

/-- Helper: if `A ⊆ Λ` and `B ⊆ Λ` then `A ∆ B ⊆ Λ`. -/
private theorem symmDiff_subset_of_subset
    {A B Λ : Finset V} (hA : A ⊆ Λ) (hB : B ⊆ Λ) :
    A ∆ B ⊆ Λ :=
  fun _ hx => (Finset.mem_symmDiff.mp hx).elim (fun h => hA h.1) (fun h => hB h.1)

/-- `correlationAlongExhaustion` is always `≥ 0` for a ferromagnetic
Ising model: either the value is `0` (when `A ⊄ Λ.volume n`) or it is
`correlationΛ ≥ 0` by GKS-I (`correlationΛ_nonneg`). -/
theorem correlationAlongExhaustion_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ p A n := by
  by_cases hA : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ p hA]
    exact correlationΛ_nonneg G (Λ.volume n) p hf _
  · rw [correlationAlongExhaustion_of_not_subset G Λ p hA]

/-- **GKS-II at finite volume** (Λ-lifted form): for a ferromagnetic
Ising model and `A, B ⊆ Λ`,
`correlationΛ G Λ p (lift A) * correlationΛ G Λ p (lift B)
  ≤ correlationΛ G Λ p (lift (A ∆ B))`.

Obtained by applying `IsingModel.gks_second` at the induced graph
on `↑Λ` and rewriting the RHS via `liftFinset_symmDiff`. -/
theorem correlationΛ_gks_second
    (G : SimpleGraph V) {Λ : Finset V}
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A B : Finset V} (hA : A ⊆ Λ) (hB : B ⊆ Λ) :
    correlationΛ G Λ p (liftFinset A hA) * correlationΛ G Λ p (liftFinset B hB)
      ≤ correlationΛ G Λ p (liftFinset (A ∆ B) (symmDiff_subset_of_subset hA hB)) := by
  have hgks : IsingModel.correlation (inducedGraph G Λ) p (liftFinset A hA)
      * IsingModel.correlation (inducedGraph G Λ) p (liftFinset B hB)
      ≤ IsingModel.correlation (inducedGraph G Λ) p
          (liftFinset A hA ∆ liftFinset B hB) :=
    IsingModel.gks_second (inducedGraph G Λ) p hf _ _
  rw [liftFinset_symmDiff hA hB] at hgks
  exact hgks

/-- **GKS-II at infinite volume**: for a ferromagnetic Ising model on
an ambient type `V` with an exhaustion `Λ`,
`correlationInfinite G Λ p A * correlationInfinite G Λ p B
  ≤ correlationInfinite G Λ p (A ∆ B)`.

Proof: pick `N` via `Λ.exhaust (A ∪ B)` so that for `n ≥ N` both
`A, B ⊆ Λ.volume n` (hence `A ∆ B ⊆ Λ.volume n`).  Eventually the
finite-volume `correlationΛ_gks_second` gives the product inequality
for the three `correlationAlongExhaustion` sequences.  Pass to the
limit using `Tendsto.mul` +
`tendsto_correlationAlongExhaustion_correlationInfinite` and
`le_of_tendsto_of_tendsto'` to preserve the inequality. -/
theorem correlationInfinite_gks_second
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset V) :
    correlationInfinite G Λ p A * correlationInfinite G Λ p B
      ≤ correlationInfinite G Λ p (A ∆ B) := by
  have hlhs :
      Filter.Tendsto
        (fun n => correlationAlongExhaustion G Λ p A n
          * correlationAlongExhaustion G Λ p B n)
        Filter.atTop
        (nhds (correlationInfinite G Λ p A * correlationInfinite G Λ p B)) :=
    (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf A).mul
      (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf B)
  have hrhs :=
    tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf (A ∆ B)
  refine le_of_tendsto_of_tendsto' hlhs hrhs ?_
  intro n
  by_cases hAn : A ⊆ Λ.volume n
  · by_cases hBn : B ⊆ Λ.volume n
    · -- Both in: use finite-volume gks_second
      have hAΔB : A ∆ B ⊆ Λ.volume n := symmDiff_subset_of_subset hAn hBn
      rw [correlationAlongExhaustion_of_subset G Λ p hAn,
          correlationAlongExhaustion_of_subset G Λ p hBn,
          correlationAlongExhaustion_of_subset G Λ p hAΔB]
      exact correlationΛ_gks_second G p hf hAn hBn
    · -- B ⊄: LHS = 0, RHS ≥ 0
      rw [correlationAlongExhaustion_of_not_subset G Λ p hBn, mul_zero]
      exact correlationAlongExhaustion_nonneg G Λ p hf (A ∆ B) n
  · -- A ⊄: LHS = 0, RHS ≥ 0
    rw [correlationAlongExhaustion_of_not_subset G Λ p hAn, zero_mul]
    exact correlationAlongExhaustion_nonneg G Λ p hf (A ∆ B) n

end Ambient
end IsingModel
