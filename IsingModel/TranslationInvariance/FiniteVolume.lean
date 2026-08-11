import IsingModel.TranslationInvariance.ConfigEquiv

/-!
# Translating a finite volume: spin products, correlations, and lifted observables

The setting continues that of the site and configuration bijections: an additive group `T` acting
on a vertex type `V` with `[DecidableEq V]`, and a group element `t : T`.

For a finite volume `Λ : Finset V`, an observable `A : Finset ↥Λ` and a configuration
`σ : Config ↥Λ`, the spin product of the image of `A` under the site bijection, evaluated at the
configuration transported by `configVaddEquiv t Λ`, equals the spin product of `A` at `σ`; this is
a reindexing of a product over `A` and needs neither an ambient graph nor an invariance
assumption. Assuming a graph `G : SimpleGraph V` translation invariant under the action, and
`Fintype` instances on the edge sets of the graphs induced on `Λ` and on `vaddFinset t Λ`, the
finite-volume correlation of the transported observable in the translated volume equals the
correlation of `A` in `Λ`: the partition functions agree, and the numerators match term by term
under the same reindexing.

Two set-level facts prepare the passage to exhaustions. Translating both sides of an inclusion of
finite sets is reversible, so `vaddFinset t A ⊆ vaddFinset t Λ` holds exactly when `A ⊆ Λ`. And
for `hA : A ⊆ Λ`, lifting the translated set into the subtype of the translated volume gives the
image, under the site bijection for `Λ`, of the lift of `A` into the subtype of `Λ` — the
identification that lets the correlation statement above be read at a stage of an exhaustion.
-/

universe u v

namespace IsingModel

namespace Ambient

/-- **Spin product equivariance under `configVaddEquiv`**:
for `A : Finset ↑Λ`, `σ : Config ↑Λ`, and translation `t : T`,

`spinProduct (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
  (configVaddEquiv t Λ σ) = spinProduct A σ`.

The image Finset `A.map (vaddSubtypeEquiv t Λ).toEmbedding` is the
translated set of sites inside `↑(vaddFinset t Λ)`. Reindexing the
`∏_j toSign((configVaddEquiv σ) j)` product via `Finset.prod_map`
reduces to `∏_i toSign((configVaddEquiv σ) (emb i)) = ∏_i toSign(σ i)`,
since `configVaddEquiv t Λ σ = σ ∘ (vaddSubtypeEquiv t Λ).symm` and
`emb = (vaddSubtypeEquiv t Λ).toEmbedding`. -/
theorem spinProduct_map_configVaddEquiv {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) (A : Finset (↑Λ : Type _))
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
        (configVaddEquiv t Λ σ)
      = IsingModel.spinProduct A σ := by
  unfold IsingModel.spinProduct
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i _
  -- `configVaddEquiv t Λ σ = σ ∘ (vaddSubtypeEquiv t Λ).symm`, so at
  -- `emb i = vaddSubtypeEquiv t Λ i` we get `σ ((vaddSubtypeEquiv ...).symm
  -- ((vaddSubtypeEquiv ...) i)) = σ i`.
  have h : configVaddEquiv t Λ σ (vaddSubtypeEquiv t Λ i) = σ i := by
    simp
  -- Goal: `↑((configVaddEquiv t Λ σ) ((vaddSubtypeEquiv t Λ).toEmbedding i)).toSign
  --        = ↑(σ i).toSign` (cast into ℝ).
  change (↑((configVaddEquiv t Λ σ)
      (vaddSubtypeEquiv t Λ i)).toSign : ℝ) = (↑(σ i).toSign : ℝ)
  rw [h]

/-- **Correlation equivariance under ambient translation**: for a
translation-invariant graph `G` and any `A : Finset ↑Λ`,

`correlationΛ G (vaddFinset t Λ) p (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
  = correlationΛ G Λ p A`.

Composes `partitionFunctionΛ_vaddFinset_eq` (denominator) with
`hamiltonian_configVaddEquiv_symm` + `spinProduct_map_configVaddEquiv`
(numerator) via `configVaddEquiv` reindexing. -/
theorem correlationΛ_vaddFinset_eq {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (t : T) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    [Fintype (inducedGraph G (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) (A : Finset (↑Λ : Type _)) :
    correlationΛ G (vaddFinset t Λ) p
        (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
      = correlationΛ G Λ p A := by
  -- Unfold `correlationΛ = IsingModel.correlation = gibbsExpectation (spinProduct _)`.
  change IsingModel.correlation (inducedGraph G (vaddFinset t Λ)) p
      (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
    = IsingModel.correlation (inducedGraph G Λ) p A
  unfold IsingModel.correlation IsingModel.gibbsExpectation
  -- The partition function factors are equal by `partitionFunctionΛ_vaddFinset_eq`.
  have hZ : IsingModel.partitionFunction (inducedGraph G (vaddFinset t Λ)) p
      = IsingModel.partitionFunction (inducedGraph G Λ) p := by
    change partitionFunctionΛ G (vaddFinset t Λ) p = partitionFunctionΛ G Λ p
    exact partitionFunctionΛ_vaddFinset_eq G t Λ p
  rw [hZ]
  congr 1
  -- Reindex ∑_{σ'} over Config ↑(vaddFinset t Λ) to ∑_σ over Config ↑Λ.
  refine (Fintype.sum_equiv (configVaddEquiv t Λ)
    (fun σ => IsingModel.spinProduct A σ
        * IsingModel.boltzmannWeight (inducedGraph G Λ) p σ)
    (fun σ' => IsingModel.spinProduct
        (A.map (vaddSubtypeEquiv t Λ).toEmbedding) σ'
      * IsingModel.boltzmannWeight (inducedGraph G (vaddFinset t Λ)) p σ')
    ?_).symm
  intro σ
  -- Both factors equal under `configVaddEquiv`:
  -- spinProduct via `spinProduct_map_configVaddEquiv`,
  -- boltzmannWeight via `hamiltonian_configVaddEquiv_symm`.
  have h_sp := spinProduct_map_configVaddEquiv t Λ A σ
  have h_bw : IsingModel.boltzmannWeight (inducedGraph G Λ) p σ
      = IsingModel.boltzmannWeight (inducedGraph G (vaddFinset t Λ)) p
          (configVaddEquiv t Λ σ) := by
    unfold IsingModel.boltzmannWeight
    rw [hamiltonian_configVaddEquiv_symm G t Λ p (configVaddEquiv t Λ σ),
        Equiv.symm_apply_apply]
  simp only [h_bw, h_sp]

/-- **Subset transport under translation**: `A ⊆ Λ` is equivalent to
`vaddFinset t A ⊆ vaddFinset t Λ`, via injectivity of the translate. -/
theorem vaddFinset_subset_iff {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V] (t : T) (A Λ : Finset V) :
    vaddFinset t A ⊆ vaddFinset t Λ ↔ A ⊆ Λ := by
  refine ⟨fun h x hxA => ?_, fun h x hx => ?_⟩
  · -- `x ∈ A` ⇒ `t +ᵥ x ∈ vaddFinset t A ⊆ vaddFinset t Λ` ⇒ `x ∈ Λ`.
    have : t +ᵥ x ∈ vaddFinset t A :=
      (mem_vaddFinset t A (t +ᵥ x)).mpr ⟨x, hxA, rfl⟩
    have := h this
    rw [mem_vaddFinset] at this
    obtain ⟨u, huΛ, heq⟩ := this
    have : u = x := vadd_injective t heq
    exact this ▸ huΛ
  · rw [mem_vaddFinset] at hx
    obtain ⟨u, huA, heq⟩ := hx
    rw [← heq, mem_vaddFinset]
    exact ⟨u, h huA, rfl⟩

/-- **Image of `liftFinset` under `vaddSubtypeEquiv`**: for `A ⊆ Λ`,
`liftFinset (vaddFinset t A) _` in `↑(vaddFinset t Λ)` equals the
image of `liftFinset A hA` in `↑Λ` under the translation bijection.

This bridges the volume-translation identity `partitionFunctionΛ_vaddFinset_eq`
and its correlation counterpart with the along-exhaustion framework. -/
theorem liftFinset_vaddFinset_eq {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (t : T) {Λ : Finset V} {A : Finset V} (hA : A ⊆ Λ) :
    liftFinset (vaddFinset t A)
        ((vaddFinset_subset_iff t A Λ).mpr hA)
      = (liftFinset A hA).map (vaddSubtypeEquiv t Λ).toEmbedding := by
  ext x
  rw [mem_liftFinset, Finset.mem_map]
  simp only [Equiv.coe_toEmbedding]
  refine ⟨fun hx => ?_, ?_⟩
  · -- `x : ↑(vaddFinset t Λ)`, `x.val ∈ vaddFinset t A`.
    rw [mem_vaddFinset] at hx
    obtain ⟨u, huA, heq⟩ := hx
    refine ⟨⟨u, hA huA⟩, ?_, ?_⟩
    · rw [mem_liftFinset]; exact huA
    · -- `vaddSubtypeEquiv t Λ ⟨u, hA huA⟩ = ⟨t + u, _⟩ = x`.
      apply Subtype.ext
      change t +ᵥ u = x.val
      exact heq
  · rintro ⟨⟨u, huΛ⟩, huA, hxeq⟩
    rw [mem_liftFinset] at huA
    -- `vaddSubtypeEquiv t Λ ⟨u, huΛ⟩ = ⟨t + u, _⟩`.
    have hxval : x.val = t +ᵥ u := by
      have : x = vaddSubtypeEquiv t Λ ⟨u, huΛ⟩ := hxeq.symm
      rw [this]
      rfl
    rw [hxval, mem_vaddFinset]
    exact ⟨u, huA, rfl⟩

end Ambient

end IsingModel
