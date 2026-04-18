import IsingModel.InfiniteVolume
import IsingModel.FreeEnergy
import IsingModel.Inequalities.GHS

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

/-- `liftFinset` commutes with `insert`: if `a ∈ Λ` and `A ⊆ Λ` then
`insert ⟨a, ha⟩ (liftFinset A hA) = liftFinset (insert a A) h_insert`. -/
theorem liftFinset_insert {Λ : Finset V} {A : Finset V} {a : V}
    (ha : a ∈ Λ) (hA : A ⊆ Λ) :
    insert (⟨a, ha⟩ : (↑Λ : Type _)) (liftFinset A hA)
      = liftFinset (insert a A)
          (fun _ hx => (Finset.mem_insert.mp hx).elim
            (fun h => h ▸ ha) (fun h => hA h)) := by
  ext x
  simp only [Finset.mem_insert, mem_liftFinset]
  constructor
  · rintro (rfl | hx)
    · exact Or.inl rfl
    · exact Or.inr hx
  · rintro (rfl | hx)
    · exact Or.inl (Subtype.ext rfl)
    · exact Or.inr hx

/-- `liftFinset` commutes with `sdiff` (set difference): if `A, B ⊆ Λ` then
`liftFinset A hA \ liftFinset B hB = liftFinset (A \ B) h_sdiff`. -/
theorem liftFinset_sdiff {Λ : Finset V} {A B : Finset V}
    (hA : A ⊆ Λ) (hB : B ⊆ Λ) :
    liftFinset A hA \ liftFinset B hB
      = liftFinset (A \ B) (fun _ hx => hA (Finset.mem_sdiff.mp hx).1) := by
  ext x
  simp only [Finset.mem_sdiff, mem_liftFinset]

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

/-- **Free energy along an exhaustion**: the volume-direction free
energy density sequence $f_n := f_{\Lambda_n}$ whose convergence
Glimm–Jaffe §4.6 Proposition 4.6.1 (pp. 78ff) asserts.

This is the scaffold object; the full convergence theorem (volume
direction, genuine `Λ ↑ V`) requires subadditivity of `log Z`
combined with Fekete's lemma and is deferred to a follow-up PR. -/
noncomputable def freeEnergyAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) : ℕ → ℝ :=
  fun n => freeEnergyΛ G (Λ.volume n) p

/-- **Unfolding of `freeEnergyAlongExhaustion`**: by construction, equal
to `freeEnergyΛ` at the `n`-th volume of the exhaustion.  Marked `@[simp]`
(unconditional `rfl`-proved unfolding) for ergonomic downstream use in
the Fekete/subadditivity follow-up. -/
@[simp]
theorem freeEnergyAlongExhaustion_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ p n = freeEnergyΛ G (Λ.volume n) p :=
  rfl

/-- **Partition function along an exhaustion**: the volume-direction
partition function sequence $Z_n := Z_{\Lambda_n}$.  Companion to
`freeEnergyAlongExhaustion` (Glimm–Jaffe §4.6); useful for Prop 4.6.1
∞-vol proofs that decompose `freeEnergy = log Z / |Λ|`. -/
noncomputable def partitionFunctionAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) : ℕ → ℝ :=
  fun n => partitionFunctionΛ G (Λ.volume n) p

/-- **Unfolding of `partitionFunctionAlongExhaustion`**: by construction
equal to `partitionFunctionΛ` at the `n`-th volume.  Unconditional
`rfl`-proof, marked `@[simp]`. -/
@[simp]
theorem partitionFunctionAlongExhaustion_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ p n
      = partitionFunctionΛ G (Λ.volume n) p :=
  rfl

/-- **Positivity along an exhaustion**:
`0 < partitionFunctionAlongExhaustion G Λ p n` for every `n`. -/
theorem partitionFunctionAlongExhaustion_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    0 < partitionFunctionAlongExhaustion G Λ p n :=
  partitionFunctionΛ_pos G (Λ.volume n) p

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

/-- **Subgraph monotonicity of `freeEnergyAlongExhaustion`**: for
`G₁ ≤ G₂` and ferromagnetic parameters, the free energy along the
exhaustion is pointwise monotone in the ambient subgraph. Direct
specialization of `freeEnergyΛ_monotone_ambient_subgraph` at each
`Λ.volume n`. -/
theorem freeEnergyAlongExhaustion_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    freeEnergyAlongExhaustion G₁ Λ p n
      ≤ freeEnergyAlongExhaustion G₂ Λ p n :=
  freeEnergyΛ_monotone_ambient_subgraph h (Λ.volume n) p hf

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

/-- **Named alias for the FKG-form correlation inequality at infinite volume**.

For ferromagnetic Ising, the infinite-volume correlations satisfy
$\langle \sigma^A \rangle_\infty \langle \sigma^B \rangle_\infty
  \le \langle \sigma^{A \triangle B} \rangle_\infty$, which is the
numerical inequality one would obtain from the FKG inequality if one
naively applied it to $f = \sigma^A, g = \sigma^B$ together with the
spin-flip product identity $\sigma^A \cdot \sigma^B
  = \sigma^{A \triangle B}$.

**Important caveat**: spinProduct observables are **not** generally
monotone (e.g., flipping two spins increases a cardinality-2 product
from $+1$ to $+1$ but intermediate configurations have the product
equal to $-1$), so the general FKG inequality (Glimm–Jaffe §4.4 p. 67,
requiring monotone $f, g$) does not directly apply to arbitrary
spinProducts.  This theorem gives the same numerical conclusion via a
different route — it is literally the GKS-II theorem
(`correlationInfinite_gks_second`, PR #94), proved through the HNC /
log-supermodularity of Boltzmann weights rather than FKG's lattice
condition argument.

Provided for nomenclature/searchability and to document the §4.4
coverage (the full FKG inequality for general monotone observables at
infinite volume requires a monotone-function framework on infinite
configs, which is out of scope).

Reference: Glimm–Jaffe §4.4 p. 67 (FKG inequality general);
Friedli–Velenik §3.2.2 (FKG lattice condition). -/
theorem correlationInfinite_fkg_spinProduct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset V) :
    correlationInfinite G Λ p A * correlationInfinite G Λ p B
      ≤ correlationInfinite G Λ p (A ∆ B) :=
  correlationInfinite_gks_second G Λ p hf A B

/-! ## h-direction monotonicity at infinite volume

Lift `IsingModel.correlation_monotone_h` (finite volume, external
field direction) to the thermodynamic limit.  For fixed `J ≥ 0`,
`β > 0`, the map `h ↦ correlationInfinite G Λ ⟨J, h, β⟩ A` is
monotone on `Set.Ici 0`.

Reference: Glimm–Jaffe, Proposition 4.2.4. -/

/-- **h-direction monotonicity of `correlationΛ`**: for fixed
`J ≥ 0`, `β > 0`, the correlation on `Λ : Finset V` is monotone in
the external field `h ∈ Set.Ici 0`. -/
theorem correlationΛ_monotone_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun h : ℝ => correlationΛ G Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  IsingModel.correlation_monotone_h (inducedGraph G Λ) J hJ β hβ A

/-- **h-direction monotonicity of `correlationAlongExhaustion`**:
pointwise on the exhaustion sequence.  For `0 ≤ h₁ ≤ h₂`,
`correlationAlongExhaustion G Λ ⟨J, h₁, β⟩ A n
  ≤ correlationAlongExhaustion G Λ ⟨J, h₂, β⟩ A n`
for every `n`. -/
theorem correlationAlongExhaustion_monotone_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset V) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) (n : ℕ) :
    correlationAlongExhaustion G Λ ⟨J, h₁, β⟩ A n
      ≤ correlationAlongExhaustion G Λ ⟨J, h₂, β⟩ A n := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ ⟨J, h₁, β⟩ hAn,
        correlationAlongExhaustion_of_subset G Λ ⟨J, h₂, β⟩ hAn]
    exact correlationΛ_monotone_h G (Λ.volume n) hJ hβ _ hh₁ (hh₁.trans hh₁₂) hh₁₂
  · rw [correlationAlongExhaustion_of_not_subset G Λ ⟨J, h₁, β⟩ hAn,
        correlationAlongExhaustion_of_not_subset G Λ ⟨J, h₂, β⟩ hAn]

/-- **h-direction monotonicity of `correlationInfinite`**: for fixed
`J ≥ 0`, `β > 0`, the thermodynamic-limit correlation is monotone in
the external field `h ∈ Set.Ici 0`.

Glimm–Jaffe, Proposition 4.2.4 at infinite volume. -/
theorem correlationInfinite_monotone_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset V) :
    MonotoneOn
      (fun h : ℝ => correlationInfinite G Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) := by
  intro h₁ hh₁ h₂ _ hh₁₂
  refine ciSup_le ?_
  intro n
  exact (correlationAlongExhaustion_monotone_h G Λ hJ hβ A hh₁ hh₁₂ n).trans
    (le_ciSup (correlationAlongExhaustion_bddAbove G Λ ⟨J, h₂, β⟩ A) n)

/-! ## β-direction monotonicity at infinite volume

Lift `IsingModel.correlation_monotone_beta` (inverse-temperature
direction) to the thermodynamic limit.  For fixed `J ≥ 0`, `h ≥ 0`,
the map `β ↦ correlationInfinite G Λ ⟨J, h, β⟩ A` is monotone on
`Set.Ioi 0`.

Reference: Glimm–Jaffe, Proposition 4.2.4 (β-direction). -/

/-- **β-direction monotonicity of `correlationΛ`**: for fixed
`J ≥ 0`, `h ≥ 0`, the correlation on `Λ : Finset V` is monotone in
the inverse temperature `β ∈ Set.Ioi 0`. -/
theorem correlationΛ_monotone_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun β : ℝ => correlationΛ G Λ ⟨J, h, β⟩ A)
      (Set.Ioi 0) :=
  IsingModel.correlation_monotone_beta (inducedGraph G Λ) J hJ h hh A

/-- **β-direction monotonicity of `correlationAlongExhaustion`**:
pointwise on the exhaustion sequence.  For `0 < β₁ ≤ β₂`,
`correlationAlongExhaustion G Λ ⟨J, h, β₁⟩ A n
  ≤ correlationAlongExhaustion G Λ ⟨J, h, β₂⟩ A n`
for every `n`. -/
theorem correlationAlongExhaustion_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (A : Finset V) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) (n : ℕ) :
    correlationAlongExhaustion G Λ ⟨J, h, β₁⟩ A n
      ≤ correlationAlongExhaustion G Λ ⟨J, h, β₂⟩ A n := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ ⟨J, h, β₁⟩ hAn,
        correlationAlongExhaustion_of_subset G Λ ⟨J, h, β₂⟩ hAn]
    exact correlationΛ_monotone_beta G (Λ.volume n) hJ hh _ hβ₁
      (lt_of_lt_of_le hβ₁ hβ₁₂) hβ₁₂
  · rw [correlationAlongExhaustion_of_not_subset G Λ ⟨J, h, β₁⟩ hAn,
        correlationAlongExhaustion_of_not_subset G Λ ⟨J, h, β₂⟩ hAn]

/-- **β-direction monotonicity of `correlationInfinite`**: for fixed
`J ≥ 0`, `h ≥ 0`, the thermodynamic-limit correlation is monotone in
the inverse temperature `β ∈ Set.Ioi 0`.

Glimm–Jaffe, Proposition 4.2.4 at infinite volume (β-direction). -/
theorem correlationInfinite_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (A : Finset V) :
    MonotoneOn
      (fun β : ℝ => correlationInfinite G Λ ⟨J, h, β⟩ A)
      (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ _ hβ₁₂
  refine ciSup_le ?_
  intro n
  exact (correlationAlongExhaustion_monotone_beta G Λ hJ hh A hβ₁ hβ₁₂ n).trans
    (le_ciSup (correlationAlongExhaustion_bddAbove G Λ ⟨J, h, β₂⟩ A) n)

/-! ## J-direction monotonicity at infinite volume

Lift `IsingModel.correlation_monotone_J` (coupling-constant
direction) to the thermodynamic limit.  For fixed `h ≥ 0`, `β > 0`,
the map `J ↦ correlationInfinite G Λ ⟨J, h, β⟩ A` is monotone on
`Set.Ici 0`.

Reference: Glimm–Jaffe, Proposition 4.2.4, p. 58 (J-direction). -/

/-- **J-direction monotonicity of `correlationΛ`**: for fixed
`h ≥ 0`, `β > 0`, the correlation on `Λ : Finset V` is monotone in
the coupling constant `J ∈ Set.Ici 0`. -/
theorem correlationΛ_monotone_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun J : ℝ => correlationΛ G Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  IsingModel.correlation_monotone_J (inducedGraph G Λ) h hh β hβ A

/-- **J-direction monotonicity of `correlationAlongExhaustion`**:
pointwise on the exhaustion sequence.  For `0 ≤ J₁ ≤ J₂`,
`correlationAlongExhaustion G Λ ⟨J₁, h, β⟩ A n
  ≤ correlationAlongExhaustion G Λ ⟨J₂, h, β⟩ A n`
for every `n`. -/
theorem correlationAlongExhaustion_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (A : Finset V) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) (n : ℕ) :
    correlationAlongExhaustion G Λ ⟨J₁, h, β⟩ A n
      ≤ correlationAlongExhaustion G Λ ⟨J₂, h, β⟩ A n := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ ⟨J₁, h, β⟩ hAn,
        correlationAlongExhaustion_of_subset G Λ ⟨J₂, h, β⟩ hAn]
    exact correlationΛ_monotone_J G (Λ.volume n) hh hβ _ hJ₁ (hJ₁.trans hJ₁₂) hJ₁₂
  · rw [correlationAlongExhaustion_of_not_subset G Λ ⟨J₁, h, β⟩ hAn,
        correlationAlongExhaustion_of_not_subset G Λ ⟨J₂, h, β⟩ hAn]

/-- **J-direction monotonicity of `correlationInfinite`**: for fixed
`h ≥ 0`, `β > 0`, the thermodynamic-limit correlation is monotone in
the coupling constant `J ∈ Set.Ici 0`.

Glimm–Jaffe, Proposition 4.2.4 at infinite volume (J-direction). -/
theorem correlationInfinite_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (A : Finset V) :
    MonotoneOn
      (fun J : ℝ => correlationInfinite G Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) := by
  intro J₁ hJ₁ J₂ _ hJ₁₂
  refine ciSup_le ?_
  intro n
  exact (correlationAlongExhaustion_monotone_J G Λ hh hβ A hJ₁ hJ₁₂ n).trans
    (le_ciSup (correlationAlongExhaustion_bddAbove G Λ ⟨J₂, h, β⟩ A) n)

/-! ## Infinite-volume single-site magnetization

Specialize `correlationInfinite` to single sites `A = {i}` to obtain
the formal thermodynamic-limit magnetization `magnetizationInfinite`.
All basic properties follow directly from the general
`correlationInfinite` API (PR #91–#97).

Reference: Glimm–Jaffe §4.2 (pp. 57ff) / §5.1 (p. 77, $m^* := \lim_{h \to 0^+} M$). -/

/-- **Infinite-volume single-site magnetization**: for a ferromagnetic
Ising model on an ambient type `V`, exhaustion `Λ`, and site `i : V`,
`magnetizationInfinite G Λ p i := correlationInfinite G Λ p {i}`.

This is the formal thermodynamic-limit magnetization
$\langle \sigma_i \rangle_\infty^{\mathrm{FM}}$. -/
noncomputable def magnetizationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) : ℝ :=
  correlationInfinite G Λ p {i}

/-- **Nonnegativity of `magnetizationInfinite`** (ferromagnetic):
`0 ≤ magnetizationInfinite G Λ p i`.  Specialization of
`correlationInfinite_nonneg` at `A = {i}`. -/
theorem magnetizationInfinite_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    0 ≤ magnetizationInfinite G Λ p i :=
  correlationInfinite_nonneg G Λ p hf {i}

/-- **Upper bound**: `magnetizationInfinite G Λ p i ≤ 1`. Specialization
of `correlationInfinite_le_one`. -/
theorem magnetizationInfinite_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    magnetizationInfinite G Λ p i ≤ 1 :=
  correlationInfinite_le_one G Λ p {i}

/-- **Exhaustion-independence of `magnetizationInfinite`**:
the value does not depend on the choice of exhaustion.  Specialization
of `correlationInfinite_indep_exhaustion`. -/
theorem magnetizationInfinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    magnetizationInfinite G Λ p i = magnetizationInfinite G Λ' p i :=
  correlationInfinite_indep_exhaustion G Λ Λ' p hf {i}

/-- **J-direction monotonicity of `magnetizationInfinite`** (for
fixed `h ≥ 0, β > 0`).  Specialization of
`correlationInfinite_monotone_J`. -/
theorem magnetizationInfinite_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (i : V) :
    MonotoneOn
      (fun J : ℝ => magnetizationInfinite G Λ ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  correlationInfinite_monotone_J G Λ hh hβ {i}

/-- **h-direction monotonicity of `magnetizationInfinite`** (for
fixed `J ≥ 0, β > 0`).  Specialization of
`correlationInfinite_monotone_h`. -/
theorem magnetizationInfinite_monotone_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (i : V) :
    MonotoneOn
      (fun h : ℝ => magnetizationInfinite G Λ ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  correlationInfinite_monotone_h G Λ hJ hβ {i}

/-- **β-direction monotonicity of `magnetizationInfinite`** (for
fixed `J ≥ 0, h ≥ 0`).  Specialization of
`correlationInfinite_monotone_beta`. -/
theorem magnetizationInfinite_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (i : V) :
    MonotoneOn
      (fun β : ℝ => magnetizationInfinite G Λ ⟨J, h, β⟩ i)
      (Set.Ioi 0) :=
  correlationInfinite_monotone_beta G Λ hJ hh {i}

/-- **Z₂ symmetry at `h = 0` for `correlationΛ`**: at vanishing external
field, the correlation on `Λ` of an odd-cardinality set is zero.
Lift of `IsingModel.correlation_odd_vanish` (GHS.lean). -/
theorem correlationΛ_odd_vanish_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) (hodd : Odd A.card) :
    correlationΛ G Λ ⟨J, 0, β⟩ A = 0 :=
  IsingModel.correlation_odd_vanish (inducedGraph G Λ) J β A hodd

/-- **Z₂ symmetry at `h = 0` for `correlationAlongExhaustion`**:
pointwise zero at every `n`.  Either `A ⊄ Λ.volume n` (both branches
of the dite give `0`) or `A ⊆ Λ.volume n` and the lifted correlation
vanishes by `correlationΛ_odd_vanish_h_zero`. -/
theorem correlationAlongExhaustion_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (hodd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion G Λ ⟨J, 0, β⟩ A n = 0 := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hAn]
    refine correlationΛ_odd_vanish_h_zero G (Λ.volume n) J β _ ?_
    -- liftFinset preserves cardinality (attach.image of an injection)
    have hinj : Function.Injective
        (fun (x : { v // v ∈ A }) => (⟨x.val, hAn x.property⟩ : (↑(Λ.volume n) : Type _))) := by
      intro x y heq
      apply Subtype.ext
      exact Subtype.mk.inj heq
    have hcard : (liftFinset A hAn).card = A.card := by
      simp only [liftFinset, Finset.card_image_of_injective _ hinj, Finset.card_attach]
    rw [hcard]
    exact hodd
  · exact correlationAlongExhaustion_of_not_subset G Λ ⟨J, 0, β⟩ hAn

/-- **Z₂ symmetry at `h = 0` for `correlationInfinite`**: vanishes
for odd-cardinality sets.  Supremum of a constantly-zero sequence. -/
theorem correlationInfinite_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (hodd : Odd A.card) :
    correlationInfinite G Λ ⟨J, 0, β⟩ A = 0 := by
  simp only [correlationInfinite,
    correlationAlongExhaustion_h_zero G Λ J β A hodd, ciSup_const]

/-- **`magnetizationInfinite` at `h = 0` vanishes**: the Z₂ spin-flip
symmetry at zero external field forces the single-site thermodynamic
magnetization to be zero.

This gives the zero-field **symmetric** value, which is distinct from
the *spontaneous magnetization* $m^* := \lim_{h \to 0^+} M(h)$ studied
in Glimm–Jaffe §5.1 (p. 77): symmetry breaking is detected by the
one-sided limit $h \to 0^+$ (or boundary-condition selection), not by
evaluating at $h = 0$. -/
theorem magnetizationInfinite_zero_at_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) :
    magnetizationInfinite G Λ ⟨J, 0, β⟩ i = 0 :=
  correlationInfinite_h_zero G Λ J β {i} (by simp)

/-! ## Spontaneous magnetization

Define the spontaneous magnetization
$m^*(G, \Lambda; J, \beta; i) := \lim_{h \to 0^+} M^{\mathrm{FM}}(J, h, \beta; i)$
as the infimum over `h > 0` of `magnetizationInfinite`.  Since
`magnetizationInfinite` is monotone in `h` on `Set.Ici 0` (PR #95) and
bounded below by `0` (ferromagnetic, PR #98), the right-limit at `h = 0`
equals this infimum.

Reference: Glimm–Jaffe §5.1 p. 77. Friedli–Velenik §3.10 (self-consistent
magnetization). -/

/-! ## Spontaneous correlation function (general `A`)

Generalize `spontaneousMagnetization` (single-site, `A = {i}`) to an
arbitrary finite set `A : Finset V`.  Same infimum-form over `h > 0`,
derived from PR #91–#100's `correlationInfinite` API. -/

/-- **Spontaneous correlation function** (infimum form):
`spontaneousCorrelation G Λ J β A := ⨅ h : ↥(Set.Ioi 0), correlationInfinite G Λ ⟨J, h, β⟩ A`.

Generalization of `spontaneousMagnetization` to arbitrary `A : Finset V`.
For $A = \{i\}$, coincides with `spontaneousMagnetization` by definition. -/
noncomputable def spontaneousCorrelation
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) : ℝ :=
  ⨅ h : ↥(Set.Ioi (0 : ℝ)), correlationInfinite G Λ ⟨J, h.val, β⟩ A

/-- **Bounded-below witness** for `spontaneousCorrelation`: the family
`h ↦ correlationInfinite G Λ ⟨J, h, β⟩ A` over `Set.Ioi 0` is bounded
below by `0` (ferromagnetic). -/
private theorem correlationInfinite_bddBelow_on_Ioi
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    BddBelow (Set.range
      (fun h : ↥(Set.Ioi (0 : ℝ)) =>
        correlationInfinite G Λ ⟨J, h.val, β⟩ A)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨h, rfl⟩
  exact correlationInfinite_nonneg G Λ ⟨J, h.val, β⟩
    ⟨hJ, le_of_lt h.property, hβ⟩ A

/-- **Nonnegativity** (ferromagnetic): $\langle \sigma^A \rangle^* \ge 0$. -/
theorem spontaneousCorrelation_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    0 ≤ spontaneousCorrelation G Λ J β A := by
  refine le_ciInf ?_
  rintro h
  exact correlationInfinite_nonneg G Λ ⟨J, h.val, β⟩
    ⟨hJ, le_of_lt h.property, hβ⟩ A

/-- **Upper bound**: $\langle \sigma^A \rangle^* \le 1$. -/
theorem spontaneousCorrelation_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    spontaneousCorrelation G Λ J β A ≤ 1 := by
  refine ciInf_le_of_le
    (correlationInfinite_bddBelow_on_Ioi G Λ hJ hβ A)
    ⟨1, by norm_num⟩ ?_
  exact correlationInfinite_le_one G Λ ⟨J, 1, β⟩ A

/-- **Lower bound by `correlationInfinite` at positive `h`**: for any
`h > 0`, $\langle \sigma^A \rangle^* \le \langle \sigma^A \rangle(h)$. -/
theorem spontaneousCorrelation_le_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) (A : Finset V) :
    spontaneousCorrelation G Λ J β A
      ≤ correlationInfinite G Λ ⟨J, h, β⟩ A :=
  ciInf_le
    (correlationInfinite_bddBelow_on_Ioi G Λ hJ hβ A)
    ⟨h, hh⟩

/-- **Exhaustion-independence**: $\langle \sigma^A \rangle^*$ does not
depend on the choice of exhaustion. -/
theorem spontaneousCorrelation_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    spontaneousCorrelation G Λ J β A
      = spontaneousCorrelation G Λ' J β A := by
  unfold spontaneousCorrelation
  congr 1
  funext h
  exact correlationInfinite_indep_exhaustion G Λ Λ' ⟨J, h.val, β⟩
    ⟨hJ, le_of_lt h.property, hβ⟩ A

/-- **Right-limit Tendsto**: for ferromagnetic Ising, the general-`A`
`correlationInfinite ⟨J, h, β⟩ A` tends to `spontaneousCorrelation` as
`h → 0⁺`. Analogous to
`tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT`. -/
theorem tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    Filter.Tendsto
      (fun h : ℝ => correlationInfinite G Λ ⟨J, h, β⟩ A)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousCorrelation G Λ J β A)) := by
  set f : ℝ → ℝ := fun h => correlationInfinite G Λ ⟨J, h, β⟩ A with hf_def
  have hmono : MonotoneOn f (Set.Ioi 0) := by
    have hmono_Ici : MonotoneOn f (Set.Ici 0) :=
      correlationInfinite_monotone_h G Λ hJ hβ A
    exact hmono_Ici.mono Set.Ioi_subset_Ici_self
  have hbdd : BddBelow (f '' Set.Ioi 0) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    exact correlationInfinite_nonneg G Λ ⟨J, h, β⟩
      ⟨hJ, le_of_lt hh, hβ⟩ A
  have htendsto := hmono.tendsto_nhdsGT hbdd
  have hsInf : sInf (f '' Set.Ioi 0) = spontaneousCorrelation G Λ J β A := by
    unfold spontaneousCorrelation
    rw [← sInf_range, ← Set.image_univ]
    congr 1
    ext y
    simp [hf_def, Set.image_univ, Set.mem_image, Set.mem_Ioi, Subtype.exists]
  rw [← hsInf]
  exact htendsto

/-! ## Spontaneous magnetization (single-site specialization)

`spontaneousMagnetization` is the single-site case `A = {i}` of
`spontaneousCorrelation`.  All basic properties are one-line
specializations.

Reference: Glimm–Jaffe §5.1 p. 77 (the order parameter $m^*$
distinguishing ordered/disordered phases). -/

/-- **Spontaneous magnetization at infinite volume** (*infimum form*):
for ferromagnetic Ising on an ambient type `V`, exhaustion `Λ`, and
fixed `J, β`,
`spontaneousMagnetization G Λ J β i := spontaneousCorrelation G Λ J β {i}`.

This is the order parameter $m^*$.  Since `magnetizationInfinite` is
monotone in `h` on `Set.Ici 0` and bounded in `[0, 1]`, this infimum
coincides with $\lim_{h \to 0^+} M(h)$
(`tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT`). -/
noncomputable def spontaneousMagnetization
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) : ℝ :=
  spontaneousCorrelation G Λ J β {i}

/-- **Agreement at singletons**: `spontaneousCorrelation` on `{i}`
equals `spontaneousMagnetization`. Holds by definition. -/
theorem spontaneousCorrelation_singleton_eq_spontaneousMagnetization
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) :
    spontaneousCorrelation G Λ J β {i}
      = spontaneousMagnetization G Λ J β i :=
  rfl

/-- **Nonnegativity of `spontaneousMagnetization`** (ferromagnetic):
$m^* \ge 0$.  Specialization of `spontaneousCorrelation_nonneg` at
`A = {i}`. -/
theorem spontaneousMagnetization_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    0 ≤ spontaneousMagnetization G Λ J β i :=
  spontaneousCorrelation_nonneg G Λ hJ hβ {i}

/-- **Upper bound**: $m^* \le 1$.  Specialization of
`spontaneousCorrelation_le_one` at `A = {i}`. -/
theorem spontaneousMagnetization_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    spontaneousMagnetization G Λ J β i ≤ 1 :=
  spontaneousCorrelation_le_one G Λ hJ hβ {i}

/-- **Lower bound for `magnetizationInfinite` at positive `h`**:
$m^* \le M(h)$ for $h > 0$. Specialization of
`spontaneousCorrelation_le_correlationInfinite` at `A = {i}` (noting
`magnetizationInfinite = correlationInfinite ... {i}`). -/
theorem spontaneousMagnetization_le_magnetizationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) (i : V) :
    spontaneousMagnetization G Λ J β i
      ≤ magnetizationInfinite G Λ ⟨J, h, β⟩ i :=
  spontaneousCorrelation_le_correlationInfinite G Λ hJ hβ hh {i}

/-- **Exhaustion-independence of `spontaneousMagnetization`**:
the value does not depend on the choice of exhaustion.  Specialization
of `spontaneousCorrelation_indep_exhaustion` at `A = {i}`. -/
theorem spontaneousMagnetization_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    spontaneousMagnetization G Λ J β i
      = spontaneousMagnetization G Λ' J β i :=
  spontaneousCorrelation_indep_exhaustion G Λ Λ' hJ hβ {i}

/-- **Right-limit Tendsto**: for ferromagnetic Ising,
`magnetizationInfinite` tends to `spontaneousMagnetization` as
`h → 0⁺`.  Specialization of
`tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT` at
`A = {i}` (noting `magnetizationInfinite = correlationInfinite ... {i}`). -/
theorem tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    Filter.Tendsto
      (fun h : ℝ => magnetizationInfinite G Λ ⟨J, h, β⟩ i)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousMagnetization G Λ J β i)) :=
  tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT G Λ hJ hβ {i}

/-! ## Truncated 2-point correlation at infinite volume

Specialize `correlationInfinite_gks_second` (PR #94) to the
two-point case, obtaining the truncated 2-point correlation function
$U_2(i, j) := \langle \sigma_i \sigma_j \rangle_\infty
  - \langle \sigma_i \rangle_\infty \langle \sigma_j \rangle_\infty$
and the nonnegativity $U_2 \ge 0$ for $i \ne j$.

Reference: Glimm–Jaffe §4.2 p. 57ff, Friedli–Velenik §3.6.3. -/

/-- **Truncated 2-point correlation at infinite volume**:
$U_2(i, j) := \langle \sigma_i \sigma_j \rangle_\infty
  - \langle \sigma_i \rangle_\infty \langle \sigma_j \rangle_\infty$. -/
noncomputable def truncated2Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j : V) : ℝ :=
  correlationInfinite G Λ p {i, j}
    - correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j}

/-- **Symmetry in the two arguments**: $U_2(i, j) = U_2(j, i)$. -/
theorem truncated2Infinite_symm
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j : V) :
    truncated2Infinite G Λ p i j = truncated2Infinite G Λ p j i := by
  unfold truncated2Infinite
  rw [Finset.pair_comm, mul_comm]

/-- **Nonnegativity for distinct sites**: $U_2(i, j) \ge 0$ for
$i \ne j$.  Direct corollary of `correlationInfinite_gks_second`:
$\{i, j\} = \{i\} \,\triangle\, \{j\}$ when $i \ne j$. -/
theorem truncated2Infinite_nonneg_of_ne
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {i j : V} (hij : i ≠ j) :
    0 ≤ truncated2Infinite G Λ p i j := by
  unfold truncated2Infinite
  have hset : ({i, j} : Finset V) = ({i} : Finset V) ∆ ({j} : Finset V) := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hij⟩
      · exact Or.inr ⟨rfl, hij.symm⟩
    · rintro (⟨rfl, _⟩ | ⟨rfl, _⟩)
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [hset]
  linarith [correlationInfinite_gks_second G Λ p hf {i} {j}]

/-- **Nonnegativity for coincident sites**: $U_2(i, i) \ge 0$.
On the diagonal `{i, i} = {i}` so $U_2(i, i) = M(i) - M(i)^2
  = M(i)(1 - M(i)) \ge 0$ since $M(i) \in [0, 1]$. -/
theorem truncated2Infinite_nonneg_of_eq
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    0 ≤ truncated2Infinite G Λ p i i := by
  unfold truncated2Infinite
  have hset : ({i, i} : Finset V) = {i} := by simp
  rw [hset]
  have h0 : 0 ≤ correlationInfinite G Λ p {i} :=
    correlationInfinite_nonneg G Λ p hf {i}
  have h1 : correlationInfinite G Λ p {i} ≤ 1 :=
    correlationInfinite_le_one G Λ p {i}
  nlinarith

/-- **Nonnegativity of `truncated2Infinite`** (general): $U_2(i, j) \ge 0$
for all `i, j : V`, combining the `_of_ne` and `_of_eq` cases. -/
theorem truncated2Infinite_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    0 ≤ truncated2Infinite G Λ p i j := by
  by_cases hij : i = j
  · subst hij
    exact truncated2Infinite_nonneg_of_eq G Λ p hf i
  · exact truncated2Infinite_nonneg_of_ne G Λ p hf hij

/-- **Exhaustion-independence of `truncated2Infinite`**: the value
does not depend on the choice of exhaustion.  Follows from
`correlationInfinite_indep_exhaustion` applied to each of the three
`correlationInfinite` occurrences in the definition. -/
theorem truncated2Infinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    truncated2Infinite G Λ p i j = truncated2Infinite G Λ' p i j := by
  unfold truncated2Infinite
  rw [correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j}]

/-- **`truncated2Infinite` at `h = 0`**: since
$\langle \sigma_i \rangle_\infty = \langle \sigma_j \rangle_\infty = 0$
at $h = 0$ (singletons have odd cardinality 1, so
`correlationInfinite_h_zero` applies), the truncated 2-point function
reduces to the raw 2-point correlation:
$U_2(i, j; \langle J, 0, \beta \rangle) = \langle \sigma_i \sigma_j \rangle_\infty$.

Holds for all `i, j : V` (no distinctness needed): if `i = j`, both
sides equal `correlationInfinite G Λ ⟨J, 0, β⟩ {i}` which is `0` by
the same Z₂ argument.  Useful as a closed-form expression for the
truncated correlation at zero external field (connects to
susceptibility/fluctuation analysis). -/
theorem truncated2Infinite_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i j : V) :
    truncated2Infinite G Λ ⟨J, 0, β⟩ i j
      = correlationInfinite G Λ ⟨J, 0, β⟩ {i, j} := by
  unfold truncated2Infinite
  have h_i : Odd ({i} : Finset V).card := by simp
  have h_j : Odd ({j} : Finset V).card := by simp
  rw [correlationInfinite_h_zero G Λ J β _ h_i,
      correlationInfinite_h_zero G Λ J β _ h_j]
  ring

/-! ## Truncated 3-point correlation + GHS at infinite volume

Lift the finite-volume GHS inequality (`ghs_inequality`,
`Inequalities/GHS.lean`) to the thermodynamic limit.
For ferromagnetic Ising and pairwise distinct sites,
$U_3(i, j, k) \le 0$ at infinite volume.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.4, pp. 68ff;
Friedli–Velenik §3.6.4. -/

/-- **Truncated 3-point correlation at infinite volume**:
the thermodynamic-limit analog of `IsingModel.truncated3`:
$U_3 := \langle \sigma^{\{i,j,k\}} \rangle_\infty
  - \langle \sigma^{\{i\}} \rangle_\infty \langle \sigma^{\{j,k\}} \rangle_\infty
  - \langle \sigma^{\{j\}} \rangle_\infty \langle \sigma^{\{i,k\}} \rangle_\infty
  - \langle \sigma^{\{k\}} \rangle_\infty \langle \sigma^{\{i,j\}} \rangle_\infty
  + 2 \langle \sigma^{\{i\}} \rangle_\infty \langle \sigma^{\{j\}} \rangle_\infty
    \langle \sigma^{\{k\}} \rangle_\infty$. -/
noncomputable def truncated3Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) : ℝ :=
  correlationInfinite G Λ p {i, j, k}
    - correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j, k}
    - correlationInfinite G Λ p {j} * correlationInfinite G Λ p {i, k}
    - correlationInfinite G Λ p {k} * correlationInfinite G Λ p {i, j}
    + 2 * correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j}
      * correlationInfinite G Λ p {k}

/-- **Truncated 3-point along an exhaustion** (local helper): evaluates
the `truncated3`-style algebraic expression at the `n`-th volume of
the exhaustion, using `correlationAlongExhaustion` instead of the
limit `correlationInfinite`.  Bridges the finite-volume
`ghs_inequality` and the infinite-volume `truncated3Infinite_nonpos`
via `le_of_tendsto`. -/
private noncomputable def truncated3AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) (n : ℕ) : ℝ :=
  correlationAlongExhaustion G Λ p {i, j, k} n
    - correlationAlongExhaustion G Λ p {i} n
      * correlationAlongExhaustion G Λ p {j, k} n
    - correlationAlongExhaustion G Λ p {j} n
      * correlationAlongExhaustion G Λ p {i, k} n
    - correlationAlongExhaustion G Λ p {k} n
      * correlationAlongExhaustion G Λ p {i, j} n
    + 2 * correlationAlongExhaustion G Λ p {i} n
      * correlationAlongExhaustion G Λ p {j} n
      * correlationAlongExhaustion G Λ p {k} n

/-- **Tendsto for the truncated 3-point sequence**: the pointwise
`truncated3AlongExhaustion` converges to `truncated3Infinite`.

Key technical step establishing that the thermodynamic limit of
the finite-volume truncated 3-point correlation exists and equals
the infinite-volume definition.  Proof: apply `Tendsto.sub`,
`Tendsto.add`, and `Tendsto.mul` to the seven `correlationInfinite`
convergences from
`tendsto_correlationAlongExhaustion_correlationInfinite`. -/
private theorem tendsto_truncated3AlongExhaustion_truncated3Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : V) :
    Filter.Tendsto
      (truncated3AlongExhaustion G Λ p i j k)
      Filter.atTop
      (nhds (truncated3Infinite G Λ p i j k)) := by
  unfold truncated3AlongExhaustion truncated3Infinite
  have h_ijk := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i,j,k}
  have h_jk := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {j,k}
  have h_ik := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i,k}
  have h_ij := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i,j}
  have h_i := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i}
  have h_j := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {j}
  have h_k := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {k}
  exact ((((h_ijk.sub (h_i.mul h_jk)).sub (h_j.mul h_ik)).sub
    (h_k.mul h_ij)).add
    (((tendsto_const_nhds (x := (2 : ℝ))).mul h_i).mul h_j |>.mul h_k))

/-- **GHS at infinite volume**: for a ferromagnetic Ising model and
pairwise distinct sites `i, j, k`, $U_3(i, j, k) \le 0$.

Proof: at each `n` with `{i, j, k} ⊆ Λ.volume n`, the finite-volume
`ghs_inequality` gives `truncated3AlongExhaustion n ≤ 0` after
identifying the along-exhaustion sequence with the lifted
finite-volume `truncated3`.  Pass to the limit using
`tendsto_truncated3AlongExhaustion_truncated3Infinite` and
`le_of_tendsto`. -/
theorem truncated3Infinite_nonpos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {i j k : V} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite G Λ p i j k ≤ 0 := by
  refine le_of_tendsto
    (tendsto_truncated3AlongExhaustion_truncated3Infinite G Λ p hf i j k) ?_
  -- Eventually at atTop: truncated3AlongExhaustion n ≤ 0
  obtain ⟨N, hN⟩ := Λ.exhaust ({i, j, k} : Finset V)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have habc : ({i, j, k} : Finset V) ⊆ Λ.volume n := hN n hn
  have ha : ({i} : Finset V) ⊆ Λ.volume n := fun x hx => by
    simp only [Finset.mem_singleton] at hx; subst hx
    exact habc (by simp)
  have hb : ({j} : Finset V) ⊆ Λ.volume n := fun x hx => by
    simp only [Finset.mem_singleton] at hx; subst hx
    exact habc (by simp)
  have hc : ({k} : Finset V) ⊆ Λ.volume n := fun x hx => by
    simp only [Finset.mem_singleton] at hx; subst hx
    exact habc (by simp)
  have hab : ({i, j} : Finset V) ⊆ Λ.volume n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact habc (by simp)
    · exact habc (by simp)
  have hac : ({i, k} : Finset V) ⊆ Λ.volume n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact habc (by simp)
    · exact habc (by simp)
  have hbc : ({j, k} : Finset V) ⊆ Λ.volume n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact habc (by simp)
    · exact habc (by simp)
  -- Rewrite truncated3AlongExhaustion using correlationAlongExhaustion_of_subset
  change truncated3AlongExhaustion G Λ p i j k n ≤ 0
  unfold truncated3AlongExhaustion
  rw [correlationAlongExhaustion_of_subset G Λ p habc,
      correlationAlongExhaustion_of_subset G Λ p ha,
      correlationAlongExhaustion_of_subset G Λ p hb,
      correlationAlongExhaustion_of_subset G Λ p hc,
      correlationAlongExhaustion_of_subset G Λ p hab,
      correlationAlongExhaustion_of_subset G Λ p hac,
      correlationAlongExhaustion_of_subset G Λ p hbc]
  -- Convert to finite-volume ghs_inequality on inducedGraph
  -- Build the lifted indices via subtype coercion
  have := IsingModel.ghs_inequality (inducedGraph G (Λ.volume n)) p hf
    ⟨i, ha (by simp)⟩ ⟨j, hb (by simp)⟩ ⟨k, hc (by simp)⟩
    (by intro h; apply hij; exact Subtype.mk.inj h)
    (by intro h; apply hjk; exact Subtype.mk.inj h)
    (by intro h; apply hik; exact Subtype.mk.inj h)
  unfold IsingModel.truncated3 at this
  -- Show liftFinset {...} equals { ⟨·, ...⟩, ... }
  -- Instead, rewrite the goal to match ghs_inequality
  -- The finite-volume ghs_inequality uses {i', j', k'} : Finset ↑(Λ.volume n)
  -- where i' = ⟨i, _⟩ etc. This coincides with liftFinset {i,j,k} etc.
  have hlift_ijk : liftFinset ({i, j, k} : Finset V) habc
      = ({⟨i, ha (by simp)⟩, ⟨j, hb (by simp)⟩, ⟨k, hc (by simp)⟩} :
        Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inl (by rfl)
      · exact Or.inr (Or.inl (by rfl))
      · exact Or.inr (Or.inr (by rfl))
    · rintro (rfl | rfl | rfl) <;> simp
  have hlift_i : liftFinset ({i} : Finset V) ha
      = ({⟨i, ha (by simp)⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; subst hx; rfl
    · rintro rfl; rfl
  have hlift_j : liftFinset ({j} : Finset V) hb
      = ({⟨j, hb (by simp)⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; subst hx; rfl
    · rintro rfl; rfl
  have hlift_k : liftFinset ({k} : Finset V) hc
      = ({⟨k, hc (by simp)⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; subst hx; rfl
    · rintro rfl; rfl
  have hlift_ij : liftFinset ({i, j} : Finset V) hab
      = ({⟨i, ha (by simp)⟩, ⟨j, hb (by simp)⟩} :
        Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl
      · exact Or.inl (by rfl)
      · exact Or.inr (by rfl)
    · rintro (rfl | rfl) <;> simp
  have hlift_ik : liftFinset ({i, k} : Finset V) hac
      = ({⟨i, ha (by simp)⟩, ⟨k, hc (by simp)⟩} :
        Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl
      · exact Or.inl (by rfl)
      · exact Or.inr (by rfl)
    · rintro (rfl | rfl) <;> simp
  have hlift_jk : liftFinset ({j, k} : Finset V) hbc
      = ({⟨j, hb (by simp)⟩, ⟨k, hc (by simp)⟩} :
        Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl
      · exact Or.inl (by rfl)
      · exact Or.inr (by rfl)
    · rintro (rfl | rfl) <;> simp
  simp only [correlationΛ, hlift_ijk, hlift_i, hlift_j, hlift_k,
    hlift_ij, hlift_ik, hlift_jk]
  linarith [this]

/-- **`truncated3Infinite` at `h = 0`**: for pairwise distinct sites,
$U_3 = 0$ at vanishing external field.

All singletons $\{i\}, \{j\}, \{k\}$ have odd cardinality, so their
`correlationInfinite` at $h = 0$ vanishes (`correlationInfinite_h_zero`),
making the three product terms and the triple product vanish.  With
distinct sites, $\{i, j, k\}$ also has odd cardinality (= 3), so the
first term vanishes too.  All five terms are zero. -/
theorem truncated3Infinite_h_zero_of_distinct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) {i j k : V} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite G Λ ⟨J, 0, β⟩ i j k = 0 := by
  unfold truncated3Infinite
  have h_ijk : Odd ({i, j, k} : Finset V).card := by
    rw [show ({i, j, k} : Finset V).card = 3 from ?_]
    · exact ⟨1, by norm_num⟩
    · rw [Finset.card_insert_of_notMem (by
        simp [Finset.mem_insert, Finset.mem_singleton, hij, hik])]
      rw [Finset.card_insert_of_notMem (by
        simp [Finset.mem_singleton, hjk])]
      simp
  have h_i : Odd ({i} : Finset V).card := by simp
  have h_j : Odd ({j} : Finset V).card := by simp
  have h_k : Odd ({k} : Finset V).card := by simp
  rw [correlationInfinite_h_zero G Λ J β _ h_ijk,
      correlationInfinite_h_zero G Λ J β _ h_i,
      correlationInfinite_h_zero G Λ J β _ h_j,
      correlationInfinite_h_zero G Λ J β _ h_k]
  ring

/-- **Exhaustion-independence of `truncated3Infinite`**: the value
does not depend on the choice of exhaustion. -/
theorem truncated3Infinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : V) :
    truncated3Infinite G Λ p i j k = truncated3Infinite G Λ' p i j k := by
  unfold truncated3Infinite
  rw [correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j, k},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {k},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, k},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j, k}]

/-! ## Truncated 4-point correlation + `U_4 ≤ 0` at `h = 0`

Lift `IsingModel.cor_4_3_3` (finite-volume `U_4 ≤ 0` at $h = 0$) to
the thermodynamic limit. For ferromagnetic Ising at $h = 0$ and
four pairwise-distinct sites:
$U_4(i, j, k, l) := \langle \sigma^{\{i,j,k,l\}} \rangle_\infty
  - \sum_\text{pairings} \langle \sigma^{\{·,·\}} \rangle_\infty
    \langle \sigma^{\{·,·\}} \rangle_\infty \le 0$.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.3, pp. 68ff;
Friedli–Velenik §3.6.4. -/

/-- **Truncated 4-point correlation at infinite volume**:
the thermodynamic-limit analog of `IsingModel.truncated4`. -/
noncomputable def truncated4Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) : ℝ :=
  correlationInfinite G Λ p {i, j, k, l}
    - correlationInfinite G Λ p {i, j} * correlationInfinite G Λ p {k, l}
    - correlationInfinite G Λ p {i, k} * correlationInfinite G Λ p {j, l}
    - correlationInfinite G Λ p {i, l} * correlationInfinite G Λ p {j, k}

/-- **Truncated 4-point along an exhaustion** (local helper): evaluates
the `truncated4`-style algebraic expression at the `n`-th volume of
the exhaustion, using `correlationAlongExhaustion` instead of the
limit `correlationInfinite`.  This is the pointwise sequence whose
limit as `n → ∞` is `truncated4Infinite`; established separately so
that the `le_of_tendsto`-based `_nonpos_h_zero` proof can apply the
finite-volume `cor_4_3_3` to each term of the sequence. -/
private noncomputable def truncated4AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) (n : ℕ) : ℝ :=
  correlationAlongExhaustion G Λ p {i, j, k, l} n
    - correlationAlongExhaustion G Λ p {i, j} n
      * correlationAlongExhaustion G Λ p {k, l} n
    - correlationAlongExhaustion G Λ p {i, k} n
      * correlationAlongExhaustion G Λ p {j, l} n
    - correlationAlongExhaustion G Λ p {i, l} n
      * correlationAlongExhaustion G Λ p {j, k} n

/-- **Tendsto for the truncated 4-point sequence**: the pointwise
`truncated4AlongExhaustion` converges to `truncated4Infinite`.

This is the key technical step establishing that the thermodynamic
limit of the finite-volume truncated 4-point correlation exists and
equals the infinite-volume definition.  Proof: apply `Tendsto.sub`
and `Tendsto.mul` to the 7 `correlationInfinite` convergences from
`tendsto_correlationAlongExhaustion_correlationInfinite`. -/
private theorem tendsto_truncated4AlongExhaustion_truncated4Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k l : V) :
    Filter.Tendsto
      (truncated4AlongExhaustion G Λ p i j k l)
      Filter.atTop
      (nhds (truncated4Infinite G Λ p i j k l)) := by
  unfold truncated4AlongExhaustion truncated4Infinite
  have h_ijkl := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {i,j,k,l}
  have h_ij := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {i,j}
  have h_kl := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {k,l}
  have h_ik := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {i,k}
  have h_jl := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {j,l}
  have h_il := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {i,l}
  have h_jk := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {j,k}
  exact ((h_ijkl.sub (h_ij.mul h_kl)).sub (h_ik.mul h_jl)).sub
    (h_il.mul h_jk)

/-- **`U_4 ≤ 0` at `h = 0`** at infinite volume: for a ferromagnetic
Ising model at vanishing external field and four pairwise-distinct
sites, $U_4 \le 0$.

Proof: at each `n` with `{i, j, k, l} ⊆ Λ.volume n`, the
finite-volume `cor_4_3_3` gives `truncated4AlongExhaustion n ≤ 0`
after identifying `liftFinset` patterns with the required subtype
Finsets.  Pass to the limit using
`tendsto_truncated4AlongExhaustion_truncated4Infinite` and
`le_of_tendsto`. -/
theorem truncated4Infinite_nonpos_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l ≤ 0 := by
  refine le_of_tendsto
    (tendsto_truncated4AlongExhaustion_truncated4Infinite G Λ _ hf i j k l) ?_
  obtain ⟨N, hN⟩ := Λ.exhaust ({i, j, k, l} : Finset V)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have habcd : ({i, j, k, l} : Finset V) ⊆ Λ.volume n := hN n hn
  -- Site memberships
  have mem_i : i ∈ Λ.volume n := habcd (by simp)
  have mem_j : j ∈ Λ.volume n := habcd (by simp)
  have mem_k : k ∈ Λ.volume n := habcd (by simp)
  have mem_l : l ∈ Λ.volume n := habcd (by simp)
  -- Pair subsets via a reusable helper
  have pair_sub : ∀ {a b : V}, a ∈ Λ.volume n → b ∈ Λ.volume n →
      ({a, b} : Finset V) ⊆ Λ.volume n := by
    intro a b ha hb x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hab : ({i, j} : Finset V) ⊆ Λ.volume n := pair_sub mem_i mem_j
  have hcd : ({k, l} : Finset V) ⊆ Λ.volume n := pair_sub mem_k mem_l
  have hac : ({i, k} : Finset V) ⊆ Λ.volume n := pair_sub mem_i mem_k
  have hbd : ({j, l} : Finset V) ⊆ Λ.volume n := pair_sub mem_j mem_l
  have had : ({i, l} : Finset V) ⊆ Λ.volume n := pair_sub mem_i mem_l
  have hbc : ({j, k} : Finset V) ⊆ Λ.volume n := pair_sub mem_j mem_k
  change truncated4AlongExhaustion G Λ ⟨J, 0, β⟩ i j k l n ≤ 0
  unfold truncated4AlongExhaustion
  rw [correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ habcd,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hab,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hcd,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hac,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hbd,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ had,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hbc]
  -- Apply finite-volume cor_4_3_3
  have hfin := IsingModel.cor_4_3_3 (inducedGraph G (Λ.volume n)) J β hf
    ⟨i, mem_i⟩ ⟨j, mem_j⟩ ⟨k, mem_k⟩ ⟨l, mem_l⟩
    (by intro h; apply hij; exact Subtype.mk.inj h)
    (by intro h; apply hik; exact Subtype.mk.inj h)
    (by intro h; apply hil; exact Subtype.mk.inj h)
    (by intro h; apply hjk; exact Subtype.mk.inj h)
    (by intro h; apply hjl; exact Subtype.mk.inj h)
    (by intro h; apply hkl; exact Subtype.mk.inj h)
  unfold IsingModel.truncated4 at hfin
  -- Identify liftFinset patterns
  have hlift_ijkl : liftFinset ({i, j, k, l} : Finset V) habcd
      = ({⟨i, mem_i⟩, ⟨j, mem_j⟩, ⟨k, mem_k⟩, ⟨l, mem_l⟩} :
          Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl) <;> simp
  have hlift_ij : liftFinset ({i, j} : Finset V) hab
      = ({⟨i, mem_i⟩, ⟨j, mem_j⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_kl : liftFinset ({k, l} : Finset V) hcd
      = ({⟨k, mem_k⟩, ⟨l, mem_l⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_ik : liftFinset ({i, k} : Finset V) hac
      = ({⟨i, mem_i⟩, ⟨k, mem_k⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_jl : liftFinset ({j, l} : Finset V) hbd
      = ({⟨j, mem_j⟩, ⟨l, mem_l⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_il : liftFinset ({i, l} : Finset V) had
      = ({⟨i, mem_i⟩, ⟨l, mem_l⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_jk : liftFinset ({j, k} : Finset V) hbc
      = ({⟨j, mem_j⟩, ⟨k, mem_k⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  simp only [correlationΛ, hlift_ijkl, hlift_ij, hlift_kl, hlift_ik,
    hlift_jl, hlift_il, hlift_jk]
  linarith [hfin]

/-- **Exhaustion-independence of `truncated4Infinite`**. -/
theorem truncated4Infinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k l : V) :
    truncated4Infinite G Λ p i j k l = truncated4Infinite G Λ' p i j k l := by
  unfold truncated4Infinite
  rw [correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j, k, l},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {k, l},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, k},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j, l},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, l},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j, k}]

/-! ## Parameter monotonicity of `spontaneous*`

Combine the parameter-direction monotonicity of `correlationInfinite`
(PR #95–#97) with the infimum definition of `spontaneousCorrelation`
to obtain monotonicity of the spontaneous correlation function in
`J` and `β`.  The `h`-direction is already collapsed by the infimum
over `h > 0`, so only `J` and `β` remain as free parameters. -/

/-- **J-direction monotonicity of `spontaneousCorrelation`**: for
fixed `β > 0`, $\langle \sigma^A \rangle^*(J, \beta)$ is monotone in
$J \in \mathrm{Ici}\,0$.

Since `correlationInfinite_monotone_J` gives pointwise monotonicity
for each `h ∈ Ioi 0`, the iInf over `h > 0` is also monotone in `J`.
Proof via `ciInf_mono` + `correlationInfinite_bddBelow_on_Ioi`. -/
theorem spontaneousCorrelation_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    MonotoneOn
      (fun J : ℝ => spontaneousCorrelation G Λ J β A)
      (Set.Ici 0) := by
  intro J₁ hJ₁ J₂ _ hJ₁₂
  unfold spontaneousCorrelation
  refine ciInf_mono
    (correlationInfinite_bddBelow_on_Ioi G Λ hJ₁ hβ A) ?_
  intro h
  exact correlationInfinite_monotone_J G Λ h.property.le hβ A
    hJ₁ (hJ₁.trans hJ₁₂) hJ₁₂

/-- **β-direction monotonicity of `spontaneousCorrelation`**: for
fixed `J ≥ 0`, the map `β ↦ spontaneousCorrelation G Λ J β A` is
monotone on `Set.Ioi 0`.

Companion to `spontaneousCorrelation_monotone_J`.  Since
`correlationInfinite_monotone_beta` gives pointwise monotonicity in
`β` for each `h ∈ Ioi 0` (with the remaining parameters bounded
below by `0`), the iInf over `h > 0` is also monotone in `β`.
Proof via `ciInf_mono` + `correlationInfinite_bddBelow_on_Ioi`. -/
theorem spontaneousCorrelation_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) (A : Finset V) :
    MonotoneOn
      (fun β : ℝ => spontaneousCorrelation G Λ J β A)
      (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ _ hβ₁₂
  unfold spontaneousCorrelation
  refine ciInf_mono
    (correlationInfinite_bddBelow_on_Ioi G Λ hJ hβ₁ A) ?_
  intro h
  exact correlationInfinite_monotone_beta G Λ hJ h.property.le A
    hβ₁ (lt_of_lt_of_le hβ₁ hβ₁₂) hβ₁₂

/-- **J-direction monotonicity of `spontaneousMagnetization`**:
specialization of `spontaneousCorrelation_monotone_J` at `A = {i}`. -/
theorem spontaneousMagnetization_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (i : V) :
    MonotoneOn
      (fun J : ℝ => spontaneousMagnetization G Λ J β i)
      (Set.Ici 0) :=
  spontaneousCorrelation_monotone_J G Λ hβ {i}

/-- **β-direction monotonicity of `spontaneousMagnetization`**:
specialization of `spontaneousCorrelation_monotone_beta` at `A = {i}`. -/
theorem spontaneousMagnetization_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) (i : V) :
    MonotoneOn
      (fun β : ℝ => spontaneousMagnetization G Λ J β i)
      (Set.Ioi 0) :=
  spontaneousCorrelation_monotone_beta G Λ hJ {i}

/-! ## Cor 4.3.5 (inductive n-point at h=0) at infinite volume

Lift `IsingModel.cor_4_3_5_h0` to the thermodynamic limit using the
liftFinset infrastructure from PR #107 and `Finset.sum_bij` to reindex
the powerset sum.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.5, p. 62. -/

/-- **Cor 4.3.5 lifted to infinite volume**: the inductive (n+2)-point
bound holds for `correlationInfinite` at `h = 0`.  For ferromagnetic
Ising at zero external field, any finite set `S`, and distinct sites
`j, k ∉ S`, the infinite-volume correlation satisfies the same
inductive bound as the finite-volume version. -/
theorem correlationInfinite_cor_4_3_5_h0
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    (S : Finset V) {j k : V} (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    correlationInfinite G Λ ⟨J, 0, β⟩ (insert j (insert k S)) ≤
      correlationInfinite G Λ ⟨J, 0, β⟩ S *
        correlationInfinite G Λ ⟨J, 0, β⟩ {j, k} +
      ∑ T ∈ S.powerset,
        correlationInfinite G Λ ⟨J, 0, β⟩ (insert j T) *
          correlationInfinite G Λ ⟨J, 0, β⟩ (insert k (S \ T)) := by
  set p := (⟨J, 0, β⟩ : IsingParams ℝ)
  have hlhs_tendsto := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf (insert j (insert k S))
  have hrhs_main :=
    (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf S).mul
      (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {j, k})
  have hrhs_sum : Filter.Tendsto
      (fun n => ∑ T ∈ S.powerset,
        correlationAlongExhaustion G Λ p (insert j T) n *
          correlationAlongExhaustion G Λ p (insert k (S \ T)) n)
      Filter.atTop
      (nhds (∑ T ∈ S.powerset,
        correlationInfinite G Λ p (insert j T) *
          correlationInfinite G Λ p (insert k (S \ T)))) := by
    refine tendsto_finset_sum _ (fun T _ => ?_)
    exact (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf _).mul
      (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf _)
  have hrhs_tendsto := hrhs_main.add hrhs_sum
  refine le_of_tendsto_of_tendsto' hlhs_tendsto hrhs_tendsto ?_
  intro n
  by_cases hall : (insert j (insert k S) : Finset V) ⊆ Λ.volume n
  · have hj_vol : j ∈ Λ.volume n := hall (Finset.mem_insert_self _ _)
    have hk_vol : k ∈ Λ.volume n :=
      hall (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hS_vol : S ⊆ Λ.volume n := fun x hx =>
      hall (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have hjk_vol : ({j, k} : Finset V) ⊆ Λ.volume n := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hj_vol
      · exact hk_vol
    let j' : (↑(Λ.volume n) : Type _) := ⟨j, hj_vol⟩
    let k' : (↑(Λ.volume n) : Type _) := ⟨k, hk_vol⟩
    let S' : Finset (↑(Λ.volume n) : Type _) := liftFinset S hS_vol
    have hj'_notin : j' ∉ S' := fun h => hj ((mem_liftFinset _ _).mp h)
    have hk'_notin : k' ∉ S' := fun h => hk ((mem_liftFinset _ _).mp h)
    have hjk' : j' ≠ k' := fun h => hjk (Subtype.mk.inj h)
    have hfin := IsingModel.cor_4_3_5_h0
      (inducedGraph G (Λ.volume n)) J β hf S' j' k' hj'_notin hk'_notin hjk'
    rw [correlationAlongExhaustion_of_subset G Λ p hall,
        correlationAlongExhaustion_of_subset G Λ p hS_vol,
        correlationAlongExhaustion_of_subset G Λ p hjk_vol]
    have hlift_jkS :
        liftFinset (insert j (insert k S)) hall = insert j' (insert k' S') := by
      rw [← liftFinset_insert hj_vol (fun x hx =>
        hall (Finset.mem_insert_of_mem hx))]
      simp only [S', k']
      rw [← liftFinset_insert hk_vol hS_vol]
    have hlift_jk :
        liftFinset ({j, k} : Finset V) hjk_vol = ({j', k'} : Finset _) := by
      ext x
      simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton, j', k']
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl (by rfl)
        · exact Or.inr (by rfl)
      · rintro (h | h)
        · exact Or.inl (congrArg Subtype.val h)
        · exact Or.inr (congrArg Subtype.val h)
    rw [hlift_jkS, hlift_jk]
    have hsum_eq :
        ∑ T ∈ S.powerset,
          correlationAlongExhaustion G Λ p (insert j T) n *
            correlationAlongExhaustion G Λ p (insert k (S \ T)) n
        = ∑ T' ∈ S'.powerset,
          correlationΛ G (Λ.volume n) p (insert j' T') *
            correlationΛ G (Λ.volume n) p (insert k' (S' \ T')) := by
      refine Finset.sum_bij
        (fun T hT => liftFinset T
          (fun x hx => hS_vol ((Finset.mem_powerset.mp hT) hx)))
        ?_ ?_ ?_ ?_
      · intro T hT
        simp only [S', Finset.mem_powerset]
        intro x hx
        simp only [mem_liftFinset] at hx ⊢
        exact (Finset.mem_powerset.mp hT) hx
      · intro T₁ hT₁ T₂ hT₂ heq
        have h₁ := Finset.mem_powerset.mp hT₁
        have h₂ := Finset.mem_powerset.mp hT₂
        -- Beta-reduce heq to pure liftFinset equality
        have heq' : liftFinset T₁ (fun x hx => hS_vol (h₁ hx))
            = liftFinset T₂ (fun x hx => hS_vol (h₂ hx)) := heq
        ext x
        by_cases hx_vol : x ∈ Λ.volume n
        · constructor
          · intro hxT₁
            have hlift : (⟨x, hx_vol⟩ : ↑(Λ.volume n))
                ∈ liftFinset T₁ (fun y hy => hS_vol (h₁ hy)) :=
              (mem_liftFinset _ _).mpr hxT₁
            rw [heq'] at hlift
            exact (mem_liftFinset _ _).mp hlift
          · intro hxT₂
            have hlift : (⟨x, hx_vol⟩ : ↑(Λ.volume n))
                ∈ liftFinset T₂ (fun y hy => hS_vol (h₂ hy)) :=
              (mem_liftFinset _ _).mpr hxT₂
            rw [← heq'] at hlift
            exact (mem_liftFinset _ _).mp hlift
        · exact ⟨fun h => absurd (hS_vol (h₁ h)) hx_vol,
                fun h => absurd (hS_vol (h₂ h)) hx_vol⟩
      · intro T' hT'
        simp only [S', Finset.mem_powerset] at hT'
        refine ⟨T'.image (fun x => x.val), ?_, ?_⟩
        · simp only [Finset.mem_powerset]
          intro x hx
          simp only [Finset.mem_image] at hx
          obtain ⟨y, hyT', rfl⟩ := hx
          have := hT' hyT'
          simpa only [mem_liftFinset] using this
        · ext x
          simp only [mem_liftFinset, Finset.mem_image]
          refine ⟨?_, ?_⟩
          · rintro ⟨y, hyT', hyx⟩
            have : y = x := Subtype.ext hyx
            exact this ▸ hyT'
          · intro h
            exact ⟨x, h, rfl⟩
      · intro T hT
        have hT_sub := Finset.mem_powerset.mp hT
        have hjT_vol : (insert j T : Finset V) ⊆ Λ.volume n := fun x hx => by
          simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact hj_vol
          · exact hS_vol (hT_sub hx)
        have hkST_vol : (insert k (S \ T) : Finset V) ⊆ Λ.volume n :=
          fun x hx => by
            simp only [Finset.mem_insert, Finset.mem_sdiff] at hx
            rcases hx with rfl | ⟨hxS, _⟩
            · exact hk_vol
            · exact hS_vol hxS
        rw [correlationAlongExhaustion_of_subset G Λ p hjT_vol,
            correlationAlongExhaustion_of_subset G Λ p hkST_vol]
        have h_liftFinset_jT :
            liftFinset (insert j T) hjT_vol
            = insert j' (liftFinset T (fun x hx => hS_vol (hT_sub hx))) := by
          rw [← liftFinset_insert hj_vol (fun x hx => hS_vol (hT_sub hx))]
        have h_liftFinset_kST :
            liftFinset (insert k (S \ T)) hkST_vol
            = insert k' (S' \ liftFinset T (fun x hx => hS_vol (hT_sub hx))) := by
          rw [← liftFinset_insert hk_vol (fun x hx => hS_vol
            ((Finset.mem_sdiff.mp hx).1))]
          congr 1
          simp only [S']
          exact (liftFinset_sdiff hS_vol (fun x hx => hS_vol (hT_sub hx))).symm
        rw [h_liftFinset_jT, h_liftFinset_kST]
    rw [hsum_eq]
    unfold correlationΛ
    exact hfin
  · rw [correlationAlongExhaustion_of_not_subset G Λ p hall]
    have h_main :
        0 ≤ correlationAlongExhaustion G Λ p S n *
          correlationAlongExhaustion G Λ p {j, k} n :=
      mul_nonneg
        (correlationAlongExhaustion_nonneg G Λ p hf _ n)
        (correlationAlongExhaustion_nonneg G Λ p hf _ n)
    have h_sum : 0 ≤ ∑ T ∈ S.powerset,
        correlationAlongExhaustion G Λ p (insert j T) n *
          correlationAlongExhaustion G Λ p (insert k (S \ T)) n := by
      refine Finset.sum_nonneg fun T _ => ?_
      exact mul_nonneg
        (correlationAlongExhaustion_nonneg G Λ p hf _ n)
        (correlationAlongExhaustion_nonneg G Λ p hf _ n)
    linarith

end Ambient
end IsingModel

