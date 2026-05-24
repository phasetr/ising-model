import IsingModel.AmbientLattice.Monotonicity.ExtensionGraph

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

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


end Ambient
end IsingModel
