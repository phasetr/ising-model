import IsingModel.TranslationInvariance.Shift

/-!
# Translating a finite volume: site and configuration bijections, and invariance of `Z_Λ`

Every statement here fixes an additive group `T` acting on a vertex type `V` with
`[DecidableEq V]`, a group element `t : T`, and a finite volume `Λ : Finset V`, and relates
objects attached to `Λ` with objects attached to its translate `vaddFinset t Λ`, the image of `Λ`
under `t +ᵥ ·`.

The carriers are an `Equiv` between the coercions of `Λ` and of `vaddFinset t Λ`, sending a site
to its translate by `t` and back by `-t`, and the `Equiv` between `Config ↥Λ` and
`Config ↥(vaddFinset t Λ)` obtained from it by `Equiv.arrowCongr` with the identity on `Spin`.
Pointwise `simp` lemmas evaluate them: the underlying vertex of the image of a site is `t +ᵥ`
that site; the transported configuration at a site of the translate is the original configuration
at the preimage site; and the inverse transport at a site of `Λ` is the given configuration at
the image site.

The statements that mention the ambient graph `G : SimpleGraph V` assume it translation invariant
under the action, recorded as an `IsTranslationInvariant T G` instance, whose content is that
`G.Adj (t +ᵥ u) (t +ᵥ v) ↔ G.Adj u v`. One transfers that to the induced graphs: two sites of `Λ`
are adjacent in the graph induced on `Λ` exactly when their images are adjacent in the graph
induced on `vaddFinset t Λ`. Another packages it as a graph isomorphism from the graph induced on
`vaddFinset t Λ` to the graph induced on `Λ`, whose underlying equivalence is the inverse of the
site bijection.

The transport identities come in two layers. The external-field energy of a configuration on the
translate equals the external-field energy of its pullback along the configuration equivalence,
and the per-edge spin product of a configuration on the translate at a `Sym2`-image edge equals
that product for the pullback at the original edge; the binders of these two carry the group
action and the volume, and neither an ambient graph nor a translation-invariance instance.
Assuming that `G` is translation invariant and that both induced graphs carry a `Fintype`
instance on their edge sets, the interaction energy at a coupling `J`, and then the Hamiltonian
at parameters `p`, of a configuration on the translate agree with the same quantity for its
pullback. Reindexing the Boltzmann sum by the configuration equivalence then yields
`partitionFunctionΛ G (vaddFinset t Λ) p = partitionFunctionΛ G Λ p`.
-/

universe u v

namespace IsingModel

namespace Ambient

/-- **Subtype bijection between `↑Λ` and `↑(t +ᵥ Λ)`**: the natural
translation-induced bijection, sending `⟨v, hv⟩ : ↑Λ` to
`⟨t +ᵥ v, _⟩ : ↑(vaddFinset t Λ)` and vice versa via `-t`.

This is the structural datum underlying partition-function
translation invariance: summing over configurations of `↑Λ` and
of `↑(t +ᵥ Λ)` yield the same value after the identification. -/
def vaddSubtypeEquiv {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) :
    (↑Λ : Type _) ≃ (↑(vaddFinset t Λ) : Type _) where
  toFun := fun ⟨v, hv⟩ =>
    ⟨t +ᵥ v, by
      rw [mem_vaddFinset]
      exact ⟨v, hv, rfl⟩⟩
  invFun := fun ⟨v, hv⟩ =>
    ⟨(-t) +ᵥ v, by
      rw [mem_vaddFinset] at hv
      obtain ⟨u, huΛ, heq⟩ := hv
      have : (-t) +ᵥ v = u := by
        rw [← heq, ← add_vadd, neg_add_cancel, zero_vadd]
      rw [this]
      exact huΛ⟩
  left_inv := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    change (-t) +ᵥ (t +ᵥ v) = v
    rw [← add_vadd, neg_add_cancel, zero_vadd]
  right_inv := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    change t +ᵥ ((-t) +ᵥ v) = v
    rw [← add_vadd, add_neg_cancel, zero_vadd]

/-- **`vaddSubtypeEquiv` forward map unfolds to `t +ᵥ ·`**. -/
@[simp]
theorem vaddSubtypeEquiv_apply_coe {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) (x : (↑Λ : Type _)) :
    ((vaddSubtypeEquiv t Λ) x : V) = t +ᵥ (x : V) := by
  rfl

/-- **Induced-graph adjacency is preserved by translation**: when
`G : SimpleGraph V` is translation invariant under an `AddAction T V`
and `Λ : Finset V`, the induced adjacency on the translated Finset
matches that on the original via `vaddSubtypeEquiv`:

`(inducedGraph G (vaddFinset t Λ)).Adj (vaddSubtypeEquiv t Λ u)
  (vaddSubtypeEquiv t Λ v) ↔ (inducedGraph G Λ).Adj u v`.

Proof: both sides unfold to `G.Adj (·) (·)` on raw vertex values;
on the LHS the raw values are `t +ᵥ u.val` and `t +ᵥ v.val`,
and `IsTranslationInvariant.adj_vadd` converts to the RHS. -/
theorem inducedGraph_vaddFinset_adj_iff {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (t : T) (Λ : Finset V) (u v : (↑Λ : Type _)) :
    (inducedGraph G (vaddFinset t Λ)).Adj
        (vaddSubtypeEquiv t Λ u) (vaddSubtypeEquiv t Λ v)
      ↔ (inducedGraph G Λ).Adj u v := by
  unfold inducedGraph
  -- G.induce S.Adj x y = G.Adj x.val y.val definitionally.
  change G.Adj (((vaddSubtypeEquiv t Λ) u : V))
      ((vaddSubtypeEquiv t Λ v : V)) ↔ G.Adj (u : V) (v : V)
  rw [vaddSubtypeEquiv_apply_coe, vaddSubtypeEquiv_apply_coe]
  exact IsTranslationInvariant.adj_vadd t (u : V) (v : V)

/-- **Config-level translation equiv**:
`Config ↑Λ ≃ Config ↑(vaddFinset t Λ)`, obtained by pre-composing
spin configurations with `(vaddSubtypeEquiv t Λ).symm`.

Explicit directions:
- `configVaddEquiv t Λ σ = σ ∘ (vaddSubtypeEquiv t Λ).symm`.
- `(configVaddEquiv t Λ).symm σ' = σ' ∘ vaddSubtypeEquiv t Λ`.

This is the reindexing isomorphism used in the subsequent
partition-function translation-invariance step (rewrite
`∑_{σ' : Config ↑(vaddFinset t Λ)} f(σ')` as
`∑_{σ : Config ↑Λ} f(configVaddEquiv t Λ σ)` via
`Fintype.sum_equiv`). -/
def configVaddEquiv {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) :
    Config (↑Λ : Type _) ≃ Config (↑(vaddFinset t Λ) : Type _) :=
  Equiv.arrowCongr (vaddSubtypeEquiv t Λ) (Equiv.refl Spin)

/-- **Action of `configVaddEquiv` on a point** (forward direction):
`(configVaddEquiv t Λ σ) j = σ ((vaddSubtypeEquiv t Λ).symm j)` for
`j : ↑(vaddFinset t Λ)`. Unfolding lemma for the `Equiv.arrowCongr`
construction. -/
@[simp]
theorem configVaddEquiv_apply {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) (σ : Config (↑Λ : Type _))
    (j : (↑(vaddFinset t Λ) : Type _)) :
    (configVaddEquiv t Λ σ) j = σ ((vaddSubtypeEquiv t Λ).symm j) := rfl

/-- **Action of `(configVaddEquiv t Λ).symm` on a point**:
`((configVaddEquiv t Λ).symm σ') i = σ' (vaddSubtypeEquiv t Λ i)` for
`i : ↑Λ`. Unfolding lemma for the inverse of the `Equiv.arrowCongr`. -/
@[simp]
theorem configVaddEquiv_symm_apply {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) (σ' : Config (↑(vaddFinset t Λ) : Type _))
    (i : (↑Λ : Type _)) :
    ((configVaddEquiv t Λ).symm σ') i = σ' (vaddSubtypeEquiv t Λ i) := rfl

/-- **`externalFieldEnergy` is invariant under `configVaddEquiv`**:
for any translation `t : T` and any `Λ : Finset V`,

`externalFieldEnergy h σ' = externalFieldEnergy h
  ((configVaddEquiv t Λ).symm σ')`

where `σ' : Config ↑(vaddFinset t Λ)`.

Proof: `externalFieldEnergy h σ = -h * ∑_i Spin.sign ℝ (σ i)`;
the sum `∑_{i : ↑(vaddFinset t Λ)} Spin.sign ℝ (σ' i)` reindexes
via `Fintype.sum_equiv (vaddSubtypeEquiv t Λ)` to
`∑_{j : ↑Λ} Spin.sign ℝ (σ' (vaddSubtypeEquiv t Λ j))`, and the
inner term equals `((configVaddEquiv t Λ).symm σ') j` definitionally
(by the definition of `Equiv.arrowCongr`, whose `.symm` applied to
`σ'` is exactly `σ' ∘ (vaddSubtypeEquiv t Λ)`). -/
theorem externalFieldEnergy_configVaddEquiv_symm {T : Type u}
    [AddGroup T] {V : Type v} [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) (h : ℝ)
    (σ' : Config (↑(vaddFinset t Λ) : Type _)) :
    IsingModel.externalFieldEnergy h σ'
      = IsingModel.externalFieldEnergy h
          ((configVaddEquiv t Λ).symm σ') := by
  unfold IsingModel.externalFieldEnergy
  congr 1
  symm
  exact Fintype.sum_equiv (vaddSubtypeEquiv t Λ)
      (fun j => Spin.sign ℝ (((configVaddEquiv t Λ).symm σ') j))
      (fun i => Spin.sign ℝ (σ' i))
      (fun _ => rfl)

/-- **Induced-graph translation isomorphism**: for a translation-
invariant graph `G` and a translate `vaddFinset t Λ`, the induced
graphs are isomorphic via `(vaddSubtypeEquiv t Λ).symm` (as a
graph isomorphism `≃g`).

`map_rel_iff'` uses `inducedGraph_vaddFinset_adj_iff` (PR #227);
the underlying equivalence is the inverse of `vaddSubtypeEquiv`
so the direction matches `RelIso`'s convention.

Intended use: pull back sums over edges of
`inducedGraph G (vaddFinset t Λ)` to sums over edges of
`inducedGraph G Λ` via the induced `mapEdgeSet` equivalence, in
the subsequent step deriving translation-invariance of
`interactionEnergy` / `partitionFunctionΛ`. -/
def inducedGraphVaddIso {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (t : T) (Λ : Finset V) :
    inducedGraph G (vaddFinset t Λ) ≃g inducedGraph G Λ where
  toEquiv := (vaddSubtypeEquiv t Λ).symm
  map_rel_iff' := by
    intro u v
    -- Goal:
    --   (inducedGraph G Λ).Adj
    --       ((vaddSubtypeEquiv t Λ).symm u)
    --       ((vaddSubtypeEquiv t Λ).symm v)
    --     ↔ (inducedGraph G (vaddFinset t Λ)).Adj u v
    have := inducedGraph_vaddFinset_adj_iff G t Λ
              ((vaddSubtypeEquiv t Λ).symm u)
              ((vaddSubtypeEquiv t Λ).symm v)
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm

/-- **`edgeSpin` compatibility with `Sym2.map (vaddSubtypeEquiv)`**:
for any `σ' : Config ↑(vaddFinset t Λ)` and any `e : Sym2 ↑Λ`,

`edgeSpin σ' (Sym2.map (vaddSubtypeEquiv t Λ) e)
  = edgeSpin ((configVaddEquiv t Λ).symm σ') e`.

Reading right-to-left: evaluating `σ := σ' ∘ vaddSubtypeEquiv` on
the untranslated edge `e` equals evaluating the original `σ'` on
the translated edge `Sym2.map vaddSubtypeEquiv e`.

Proof by `Sym2.ind` + definitional unfolding of `Sym2.lift`/
`Sym2.map`/`Equiv.arrowCongr`. -/
theorem edgeSpin_map_vaddSubtypeEquiv {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V)
    (σ' : Config (↑(vaddFinset t Λ) : Type _))
    (e : Sym2 (↑Λ : Type _)) :
    (IsingModel.edgeSpin σ'
        (Sym2.map (vaddSubtypeEquiv t Λ) e) : ℝ)
      = IsingModel.edgeSpin
          ((configVaddEquiv t Λ).symm σ') e := by
  refine Sym2.ind (fun _ _ => ?_) e
  rfl

/-- **`interactionEnergy` is invariant under `configVaddEquiv`**:
for a translation-invariant graph `G` and any `Λ : Finset V`,

`interactionEnergy (inducedGraph G (vaddFinset t Λ)) J σ'
  = interactionEnergy (inducedGraph G Λ) J ((configVaddEquiv t Λ).symm σ')`.

Proof: unfold to the sum over edges; rewrite using
`Finset.sum_nbij'` with `i := Sym2.map (vaddSubtypeEquiv t Λ).symm`
and inverse `j := Sym2.map (vaddSubtypeEquiv t Λ)`. Membership
preservation comes from the graph iso `inducedGraphVaddIso`
(step 6e) applied at the `SimpleGraph.Hom.map_mem_edgeSet` level;
per-edge equality follows from `edgeSpin_map_vaddSubtypeEquiv`. -/
theorem interactionEnergy_configVaddEquiv_symm {T : Type u}
    [AddGroup T] {V : Type v} [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (t : T) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    [Fintype (inducedGraph G (vaddFinset t Λ)).edgeSet]
    (J : ℝ) (σ' : Config (↑(vaddFinset t Λ) : Type _)) :
    IsingModel.interactionEnergy (inducedGraph G (vaddFinset t Λ)) J σ'
      = IsingModel.interactionEnergy (inducedGraph G Λ) J
          ((configVaddEquiv t Λ).symm σ') := by
  unfold IsingModel.interactionEnergy
  congr 1
  -- Direct proof via Finset.sum_nbij' with explicit (vaddSubtypeEquiv t Λ).symm
  -- as the forward map on Sym2 (from G₁-edges to G₂-edges).
  refine Finset.sum_nbij'
    (fun e => Sym2.map (vaddSubtypeEquiv t Λ).symm e)
    (fun e' => Sym2.map (vaddSubtypeEquiv t Λ) e') ?_ ?_ ?_ ?_ ?_
  · -- hi: maps edges of G₁ to edges of G₂ via the iso
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact (inducedGraphVaddIso G t Λ).toEmbedding.toHom.map_mem_edgeSet he
  · -- hj: inverse direction via the symm iso
    intro e' he'
    rw [SimpleGraph.mem_edgeFinset] at he' ⊢
    change Sym2.map (vaddSubtypeEquiv t Λ) e' ∈
      (inducedGraph G (vaddFinset t Λ)).edgeSet
    exact (inducedGraphVaddIso G t Λ).symm.toEmbedding.toHom.map_mem_edgeSet he'
  · -- left_inv: j (i e) = e on ι = Sym2 ↑(vaddFinset t Λ)
    intro e _
    change Sym2.map (vaddSubtypeEquiv t Λ)
          (Sym2.map (vaddSubtypeEquiv t Λ).symm e) = e
    rw [Sym2.map_map]
    simp
  · -- right_inv: i (j e') = e' on κ = Sym2 ↑Λ
    intro e' _
    change Sym2.map (vaddSubtypeEquiv t Λ).symm
          (Sym2.map (vaddSubtypeEquiv t Λ) e') = e'
    rw [Sym2.map_map]
    simp
  · -- h: edgeSpin σ' e = edgeSpin (symm σ') (Sym2.map symm e)
    intro e _
    -- Use edgeSpin_map_vaddSubtypeEquiv with e'' := Sym2.map (symm) e; then
    -- LHS goal becomes edgeSpin σ' (Sym2.map eq (Sym2.map symm e))
    -- which equals edgeSpin σ' e by Sym2.map_map + apply_symm_apply.
    have hidentity : e = Sym2.map (vaddSubtypeEquiv t Λ)
        (Sym2.map (vaddSubtypeEquiv t Λ).symm e) := by
      rw [Sym2.map_map]; simp
    conv_lhs => rw [hidentity]
    exact edgeSpin_map_vaddSubtypeEquiv t Λ σ'
      (Sym2.map (vaddSubtypeEquiv t Λ).symm e)

/-- **Hamiltonian equivariance under `configVaddEquiv`**: combine
interaction (step 6f) + external-field (step 6d) energies. -/
theorem hamiltonian_configVaddEquiv_symm {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (t : T) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    [Fintype (inducedGraph G (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ)
    (σ' : Config (↑(vaddFinset t Λ) : Type _)) :
    IsingModel.hamiltonian (inducedGraph G (vaddFinset t Λ)) p σ'
      = IsingModel.hamiltonian (inducedGraph G Λ) p
          ((configVaddEquiv t Λ).symm σ') := by
  unfold IsingModel.hamiltonian
  rw [interactionEnergy_configVaddEquiv_symm G t Λ p.J σ',
      externalFieldEnergy_configVaddEquiv_symm t Λ p.h σ']

/-- **`partitionFunctionΛ` is translation invariant**: for a
translation-invariant graph `G` and `Λ : Finset V`,

`partitionFunctionΛ G (vaddFinset t Λ) p = partitionFunctionΛ G Λ p`.

Proof: unfold both sides to sums over Config of the respective
Finsets, then reindex via `Fintype.sum_equiv (configVaddEquiv t Λ).symm`
(thus mapping σ' on ↑(vaddFinset t Λ) to σ := (symm) σ' on ↑Λ), and
use Hamiltonian equivariance to match summands. -/
theorem partitionFunctionΛ_vaddFinset_eq {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (t : T) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    [Fintype (inducedGraph G (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunctionΛ G (vaddFinset t Λ) p
      = partitionFunctionΛ G Λ p := by
  change IsingModel.partitionFunction
      (inducedGraph G (vaddFinset t Λ)) p
    = IsingModel.partitionFunction (inducedGraph G Λ) p
  unfold IsingModel.partitionFunction IsingModel.boltzmannWeight
  -- Reindex ∑_{σ'} over Config ↑(t +ᵥ Λ) to ∑_σ over Config ↑Λ.
  refine (Fintype.sum_equiv (configVaddEquiv t Λ)
    (fun σ => Real.exp (-p.β *
        IsingModel.hamiltonian (inducedGraph G Λ) p σ))
    (fun σ' => Real.exp (-p.β *
        IsingModel.hamiltonian (inducedGraph G (vaddFinset t Λ)) p σ'))
    ?_).symm
  intro σ
  -- Want: exp(-β H_Λ σ) = exp(-β H_{t+Λ} ((configVaddEquiv) σ)).
  change Real.exp (-p.β *
        IsingModel.hamiltonian (inducedGraph G Λ) p σ)
      = Real.exp (-p.β *
        IsingModel.hamiltonian (inducedGraph G (vaddFinset t Λ)) p
            ((configVaddEquiv t Λ) σ))
  rw [hamiltonian_configVaddEquiv_symm G t Λ p (configVaddEquiv t Λ σ),
      Equiv.symm_apply_apply]

end Ambient

end IsingModel
