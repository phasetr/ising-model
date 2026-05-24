import IsingModel.AmbientLattice.Monotonicity.AmbientSubgraph

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*}

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

/-- The extension of `G.induce Λ₁` to `SimpleGraph (↑Λ₂)`:
edges are pairs `u, v : ↑Λ₂` with both endpoints in `Λ₁` and
adjacent in the ambient `G`. -/
noncomputable def extendGraphFromΛ₁ (G : SimpleGraph V)
    (Λ₁ Λ₂ : Finset V) : SimpleGraph (↑Λ₂ : Type _) where
  Adj u v := u.val ∈ Λ₁ ∧ v.val ∈ Λ₁ ∧ G.Adj u.val v.val
  symm := fun _ _ ⟨hu, hv, hadj⟩ => ⟨hv, hu, hadj.symm⟩
  loopless := ⟨fun _ ⟨_, _, hadj⟩ => hadj.ne rfl⟩

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

/-- The canonical injection `↑Λ₁ → ↑Λ₂` when `Λ₁ ⊆ Λ₂`. -/
def subtypeIncl {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂) :
    (↑Λ₁ : Type _) → (↑Λ₂ : Type _) :=
  fun x => ⟨x.val, h12 x.property⟩

/-- `subtypeIncl h12` is injective. -/
theorem subtypeIncl_injective {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂) :
    Function.Injective (subtypeIncl h12) := by
  intro x y h
  have : x.val = y.val := by
    have := congr_arg Subtype.val h
    simpa [subtypeIncl] using this
  exact Subtype.ext this

/-- Restriction of a `↑Λ₂`-configuration to a `↑Λ₁`-configuration. -/
def restrictConfig {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    (σ : (↑Λ₂ : Type _) → Spin) : (↑Λ₁ : Type _) → Spin :=
  σ ∘ subtypeIncl h12

/-- The equivalence `{x : ↑Λ₂ // x.val ∈ Λ₁} ≃ ↑Λ₁`
when `Λ₁ ⊆ Λ₂`.  The inverse reuses `subtypeIncl`. -/
def Λ₁subtypeEquiv {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂) :
    {x : (↑Λ₂ : Type _) // x.val ∈ Λ₁} ≃ (↑Λ₁ : Type _) where
  toFun := fun x => ⟨x.val.val, x.property⟩
  invFun := fun y => ⟨subtypeIncl h12 y, y.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The forward equivalence from the `Λ₁` subtype inside `↑Λ₂` returns the
underlying ambient vertex. -/
@[simp]
theorem Λ₁subtypeEquiv_apply {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    (x : {x : (↑Λ₂ : Type _) // x.val ∈ Λ₁}) :
    (Λ₁subtypeEquiv h12 x : V) = x.val.val := rfl

/-- The inverse equivalence from `↑Λ₁` to the matching subtype inside `↑Λ₂`
is the canonical subtype inclusion. -/
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
noncomputable def configEquivSubtypeProd [DecidableEq V]
    {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂) :
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
theorem configEquivSubtypeProd_fst [DecidableEq V]
    {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
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


end Ambient
end IsingModel
