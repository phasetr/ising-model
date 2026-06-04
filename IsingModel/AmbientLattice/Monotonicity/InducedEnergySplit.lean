import IsingModel.AmbientLattice.Monotonicity.EdgeSiteSums

/-!
# Energy split of an induced graph over the extension graph

`EdgeSiteSums.lean` factors the Ising energy on the **extension graph**
`extendGraphFromΛ₁ G Λ₁ Λ₂` (the `Λ₁`-induced edges carried on the larger vertex
set `↑Λ₂`, with no edges touching `Λ₂ ∖ Λ₁`).  The genuine induced graph
`inducedGraph G Λ₂` additionally carries every edge touching the complement
`Λ₂ ∖ Λ₁`.  This file records the difference: the energy on `inducedGraph G Λ₂`
equals the energy on the extension graph plus the interaction over the **extra
edges** `(inducedGraph G Λ₂).edgeFinset ∖ (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset`.

Combined with the extension-graph factoring (`hamiltonian_extendGraph_factor`),
this expresses the energy on `inducedGraph G Λ₂` as the energy on
`inducedGraph G Λ₁` (restricted configuration) plus a complement-site field term
plus the extra-edge interaction.  This is the energy-level heart of the
nearest-neighbour screening of the `+` state (Issue #3565): on the cubic box the
extra edges all touch the frozen `+` shell, so the extra-edge interaction is a
constant that cancels in the normalised expectation.

* `interactionEnergy_inducedGraph_extendGraph_split` — the interaction-energy
  split.
* `hamiltonian_inducedGraph_extendGraph_split` — the full Hamiltonian split.
* `hamiltonian_inducedGraph_restrict_add` — the composed form over
  `inducedGraph G Λ₁`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
Lemma 3.22, §6.
-/

namespace IsingModel

namespace Ambient

open Finset

variable {V : Type*} [DecidableEq V]

/-- **Interaction-energy split of an induced graph over the extension graph**: for
`Λ₁ ⊆ Λ₂`, the interaction energy on `inducedGraph G Λ₂` equals the interaction
energy on `extendGraphFromΛ₁ G Λ₁ Λ₂` plus the `-J`-weighted edge-spin sum over the
extra edges (those of the induced graph not present in the extension graph).  The
extension graph is a subgraph (`extendGraphFromΛ₁_le_induce`), so its edge finset
is contained in the induced one and `Finset.sum_sdiff` splits the sum. -/
theorem interactionEnergy_inducedGraph_extendGraph_split (G : SimpleGraph V)
    (Λ₁ Λ₂ : Finset V)
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (J : ℝ) (σ : (↑Λ₂ : Type _) → Spin) :
    interactionEnergy (inducedGraph G Λ₂) J σ
      = interactionEnergy (extendGraphFromΛ₁ G Λ₁ Λ₂) J σ
        + (-J) * ∑ e ∈ (inducedGraph G Λ₂).edgeFinset \
            (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset, edgeSpin (K := ℝ) σ e := by
  have hsub : (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset ⊆ (inducedGraph G Λ₂).edgeFinset :=
    SimpleGraph.edgeFinset_mono (extendGraphFromΛ₁_le_induce G Λ₁ Λ₂)
  unfold interactionEnergy
  rw [← Finset.sum_sdiff hsub, mul_add]
  ring

/-- **Hamiltonian split of an induced graph over the extension graph**: the
Hamiltonian on `inducedGraph G Λ₂` equals the Hamiltonian on the extension graph
plus the extra-edge interaction (the field terms coincide — both graphs carry the
same vertex set `↑Λ₂`). -/
theorem hamiltonian_inducedGraph_extendGraph_split (G : SimpleGraph V)
    (Λ₁ Λ₂ : Finset V)
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ) (σ : (↑Λ₂ : Type _) → Spin) :
    hamiltonian (inducedGraph G Λ₂) p σ
      = hamiltonian (extendGraphFromΛ₁ G Λ₁ Λ₂) p σ
        + (-p.J) * ∑ e ∈ (inducedGraph G Λ₂).edgeFinset \
            (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset, edgeSpin (K := ℝ) σ e := by
  unfold hamiltonian
  rw [interactionEnergy_inducedGraph_extendGraph_split G Λ₁ Λ₂ p.J σ]
  ring

/-- **Composed Hamiltonian split**: the Hamiltonian on `inducedGraph G Λ₂` equals
the Hamiltonian on `inducedGraph G Λ₁` (restricted configuration) plus the
complement-site field term plus the extra-edge interaction.  Composes
`hamiltonian_inducedGraph_extendGraph_split` with the extension-graph factoring
`hamiltonian_extendGraph_factor`. -/
theorem hamiltonian_inducedGraph_restrict_add (G : SimpleGraph V)
    {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ) (σ : (↑Λ₂ : Type _) → Spin) :
    hamiltonian (inducedGraph G Λ₂) p σ
      = hamiltonian (inducedGraph G Λ₁) p (restrictConfig h12 σ)
        + (-p.h * ∑ v : {x : (↑Λ₂ : Type _) // ¬ (x.val ∈ Λ₁)},
            Spin.sign ℝ (σ v.val))
        + (-p.J) * ∑ e ∈ (inducedGraph G Λ₂).edgeFinset \
            (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset, edgeSpin (K := ℝ) σ e := by
  rw [hamiltonian_inducedGraph_extendGraph_split G Λ₁ Λ₂ p σ,
    hamiltonian_extendGraph_factor G h12 p σ]

end Ambient

end IsingModel
