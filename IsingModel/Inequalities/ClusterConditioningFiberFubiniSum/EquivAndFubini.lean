import IsingModel.Inequalities.ClusterConditioningFiberFubiniSum.BlocksAndRestrict

/-!
# SL-D brick D1b part 2b (2/2): the bijection `Φ` and the weight-level `tsum` Fubini

Structural split (2/2) of `ClusterConditioningFiberFubiniSum`. This child holds the
`SL-D₁` range-independence bijection `Current.pivotalFiberEquiv` (`Φ`), the weight
factorisation `Current.weight_glueBlocks_factor`, and the headline weight-level `tsum`
Fubini `Current.pivotalNumerator_fiber_factor` (`Σ_C = (βJ)·Ξ_int·Ξ_ext`). It builds
on the blocks/round-trip lemmas in the sibling `...BlocksAndRestrict`. See the
`ClusterConditioningFiberFubiniSum` facade module for the full contents/status overview.
-/

namespace IsingModel

namespace Ambient

open scoped symmDiff

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) (Λ : Finset V)
  [Fintype (inducedGraph G Λ).edgeSet]

set_option linter.unusedDecidableInType false in
/-- **SL-D₁ range-independence bijection `Φ`** (part 2b, spec `prop:phi`). The map
`Φ : 𝓕_C ≃ 𝒜_int(C, x, a) × 𝒜_ext(C, b, y)`, `Φ(M) = (M|_{E_int}, M|_{E_ext})`, with
inverse the gluing `Ψ`. This is the combinatorial heart of `SL-D₁`: the pinned
pivotal fiber factorises as a product of the interior and exterior block ensembles,
on the single ambient current type (no subgraph current). Round-trips are
`glueBlocks_restrictOn` (left) and `restrictOn_glueBlocks_interior`/`_exterior`
(right); landing is `restrictOn_mem_interiorBlockSet`/`_exteriorBlockSet` (forward)
and `glueBlocks_mem_pivotalFiberSet` (reverse). Part of ingredient **SL-D₁** brick
D1b part 2b (tracked ingredient, Group 1a; SL-D₂ awaits explicit user
authorisation); weight source FV (3.45). -/
noncomputable def Current.pivotalFiberEquiv (e₀ : (inducedGraph G Λ).edgeSet)
    (C : Finset ↑Λ) (x y a b : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (haC : a ∈ C) (hbC : b ∉ C) :
    ↥(Current.pivotalFiberSet G Λ e₀ C x y) ≃
      ↥(Current.interiorBlockSet G Λ C x a)
        × ↥(Current.exteriorBlockSet G Λ C b y) where
  toFun M :=
    (⟨M.1.restrictOn G Λ (Current.interiorEdges G Λ C),
        Current.restrictOn_mem_interiorBlockSet G Λ e₀ C x y a b hab haC hbC M.1 M.2⟩,
     ⟨M.1.restrictOn G Λ (Current.interiorEdges G Λ Cᶜ),
        Current.restrictOn_mem_exteriorBlockSet G Λ e₀ C x y a b hab haC hbC M.1 M.2⟩)
  invFun p :=
    ⟨Current.glueBlocks G Λ e₀ p.1.1 p.2.1,
      Current.glueBlocks_mem_pivotalFiberSet G Λ e₀ C x y a b hab haC hbC
        p.1.1 p.2.1 p.1.2 p.2.2⟩
  left_inv := by
    rintro ⟨M, hM⟩
    exact Subtype.ext
      (Current.glueBlocks_restrictOn G Λ e₀ C x y a b hab haC hbC M hM)
  right_inv := by
    rintro ⟨⟨ni, hni⟩, ⟨ne, hne⟩⟩
    refine Prod.ext_iff.mpr ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · exact Current.restrictOn_glueBlocks_interior G Λ e₀ C x y a b hab hbC
        ni ne hni hne
    · exact Current.restrictOn_glueBlocks_exterior G Λ e₀ C x y a b hab haC
        ni ne hni hne

set_option linter.unusedDecidableInType false in
/-- **Pointwise weight factorisation of the glue** (part 2b §④ weight preservation).
For block currents `n_int ∈ 𝒜_int`, `n_ext ∈ 𝒜_ext`, the FV (3.45) weight of the glue
factors as `weight (glueBlocks e₀ n_int n_ext) = (βJ)·w_int(n_int)·w_ext(n_ext)`, with
`w_int`/`w_ext` the interior/exterior block products. Proof: the glue is in the pinned
pivotal fiber (`glueBlocks_mem_pivotalFiberSet`), so the SL-C fiber factorisation
`weight_pivotal_fiber_factor` applies; on `E_int` (resp. `E_ext`) the glue reads
`n_int` (resp. `n_ext`). Part of ingredient **SL-D₁** brick D1b part 2b;
weight source FV (3.45). -/
theorem Current.weight_glueBlocks_factor (β J : ℝ) (e₀ : (inducedGraph G Λ).edgeSet)
    (C : Finset ↑Λ) (x y a b : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (haC : a ∈ C) (hbC : b ∉ C) (n_int n_ext : Current G Λ)
    (hint : n_int ∈ Current.interiorBlockSet G Λ C x a)
    (hext : n_ext ∈ Current.exteriorBlockSet G Λ C b y) :
    (Current.glueBlocks G Λ e₀ n_int n_ext).weight G Λ β J
      = (β * J)
        * (∏ e ∈ Current.interiorEdges G Λ C,
            (β * J) ^ (n_int e) / ((n_int e).factorial : ℝ))
        * ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
            (β * J) ^ (n_ext e) / ((n_ext e).factorial : ℝ) := by
  have hdisj := Current.interiorEdges_disjoint G Λ C
  have he0_int := Current.dominant_not_mem_interiorEdges G Λ e₀ C a b hab hbC
  have he0_ext := Current.dominant_not_mem_interiorEdges_compl G Λ e₀ C a b hab haC
  have hni_r := hint.1
  have hne_r := hext.1
  have hni_off : ∀ e ∉ Current.interiorEdges G Λ C, n_int e = 0 := by
    intro e he
    have := Current.restrictOn_apply_not_mem G Λ _ n_int he
    rwa [hni_r] at this
  have hne_off : ∀ e ∉ Current.interiorEdges G Λ Cᶜ, n_ext e = 0 := by
    intro e he
    have := Current.restrictOn_apply_not_mem G Λ _ n_ext he
    rwa [hne_r] at this
  obtain ⟨hpiv, _, hC⟩ := Current.glueBlocks_mem_pivotalFiberSet G Λ e₀ C x y a b
    hab haC hbC n_int n_ext hint hext
  have hg_int : ∀ e ∈ Current.interiorEdges G Λ C,
      Current.glueBlocks G Λ e₀ n_int n_ext e = n_int e := by
    intro e he
    simp only [Current.glueBlocks, Current.add_apply,
      Current.fromEdgeFinset_singleton_apply]
    have hne : n_ext e = 0 := hne_off e (Finset.disjoint_left.mp hdisj he)
    have he0 : e ≠ e₀ := fun h => he0_int (h ▸ he)
    rw [if_neg he0]; omega
  have hg_ext : ∀ e ∈ Current.interiorEdges G Λ Cᶜ,
      Current.glueBlocks G Λ e₀ n_int n_ext e = n_ext e := by
    intro e he
    simp only [Current.glueBlocks, Current.add_apply,
      Current.fromEdgeFinset_singleton_apply]
    have hni : n_int e = 0 := hni_off e (Finset.disjoint_right.mp hdisj he)
    have he0 : e ≠ e₀ := fun h => he0_ext (h ▸ he)
    rw [if_neg he0]; omega
  have hint_prod : (∏ e ∈ Current.interiorEdges G Λ C,
        (β * J) ^ (Current.glueBlocks G Λ e₀ n_int n_ext e)
          / ((Current.glueBlocks G Λ e₀ n_int n_ext e).factorial : ℝ))
      = ∏ e ∈ Current.interiorEdges G Λ C,
          (β * J) ^ (n_int e) / ((n_int e).factorial : ℝ) :=
    Finset.prod_congr rfl (fun e he => by rw [hg_int e he])
  have hext_prod : (∏ e ∈ Current.interiorEdges G Λ Cᶜ,
        (β * J) ^ (Current.glueBlocks G Λ e₀ n_int n_ext e)
          / ((Current.glueBlocks G Λ e₀ n_int n_ext e).factorial : ℝ))
      = ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
          (β * J) ^ (n_ext e) / ((n_ext e).factorial : ℝ) :=
    Finset.prod_congr rfl (fun e he => by rw [hg_ext e he])
  rw [Current.weight_pivotal_fiber_factor G Λ β J e₀
    (Current.glueBlocks G Λ e₀ n_int n_ext) x y a b C hab hpiv hC,
    hint_prod, hext_prod]
  ring

set_option linter.unusedDecidableInType false in
/-- **SL-D₁ weight-level `tsum` Fubini** (part 2b headline, spec `prop:fubini`,
eq. (sld1)). The pinned pivotal fiber weight sum factors as
\[
  \Sigma_C = \sum_{M \in 𝓕_C}' \weight(M)
    = (\beta J)\cdot \Xi_{\mathrm{int}}\cdot \Xi_{\mathrm{ext}}
    = (\beta J)\cdot
      \Bigl(\sum_{n \in 𝒜_{\mathrm{int}}}' w_{\mathrm{int}}(n)\Bigr)
      \cdot\Bigl(\sum_{n \in 𝒜_{\mathrm{ext}}}' w_{\mathrm{ext}}(n)\Bigr),
\]
with `Ξ_int`, `Ξ_ext` **ambient** block weight sums. Proof: reindex `Σ_C` along the
bijection `Φ` (`Equiv.tsum_eq`); the summand becomes `(βJ)·w_int·w_ext`
(`weight_glueBlocks_factor`); pull out `βJ` (`tsum_mul_left`) and split the product
`tsum` via `Summable.tsum_mul_tsum`, whose block-summability inputs are the part 2a
lemma `summable_block_weight_if_sourcesOn` (restricted by `Summable.subtype`). This
**completes SL-D₁ (range independence)**; it forms **no** subgraph current and does
**not** collapse `Ξ_ext` to a two-point function — that is the SL-D₂ core, which
**awaits explicit user authorisation and gates Lemma 5.1**. Part of ingredient
**SL-D₁** brick D1b part 2b (tracked ingredient, Group 1a); weight source FV (3.45). -/
theorem Current.pivotalNumerator_fiber_factor (β J : ℝ) (hβJ : 0 ≤ β * J)
    (e₀ : (inducedGraph G Λ).edgeSet) (C : Finset ↑Λ) (x y a b : ↑Λ)
    (hab : (e₀ : Sym2 ↑Λ) = s(a, b)) (haC : a ∈ C) (hbC : b ∉ C) :
    ∑' (M : ↥(Current.pivotalFiberSet G Λ e₀ C x y)),
        (M : Current G Λ).weight G Λ β J
      = (β * J)
        * (∑' (n : ↥(Current.interiorBlockSet G Λ C x a)),
            ∏ e ∈ Current.interiorEdges G Λ C,
              (β * J) ^ ((n : Current G Λ) e) / (((n : Current G Λ) e).factorial : ℝ))
        * ∑' (n : ↥(Current.exteriorBlockSet G Λ C b y)),
            ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
              (β * J) ^ ((n : Current G Λ) e) / (((n : Current G Λ) e).factorial : ℝ) := by
  classical
  have h_int : Summable (fun n : ↥(Current.interiorBlockSet G Λ C x a) =>
      ∏ e ∈ Current.interiorEdges G Λ C,
        (β * J) ^ ((n : Current G Λ) e) / (((n : Current G Λ) e).factorial : ℝ)) := by
    have hs := (Current.summable_block_weight_if_sourcesOn G Λ hβJ
      (Current.interiorEdges G Λ C) (({x} : Finset ↑Λ) ∆ {a})).subtype
      (Current.interiorBlockSet G Λ C x a)
    refine hs.congr ?_
    rintro ⟨n, hn⟩
    exact if_pos ⟨hn.1, hn.2.1⟩
  have h_ext : Summable (fun n : ↥(Current.exteriorBlockSet G Λ C b y) =>
      ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
        (β * J) ^ ((n : Current G Λ) e) / (((n : Current G Λ) e).factorial : ℝ)) := by
    have hs := (Current.summable_block_weight_if_sourcesOn G Λ hβJ
      (Current.interiorEdges G Λ Cᶜ) (({b} : Finset ↑Λ) ∆ {y})).subtype
      (Current.exteriorBlockSet G Λ C b y)
    refine hs.congr ?_
    rintro ⟨n, hn⟩
    exact if_pos ⟨hn.1, hn.2⟩
  have hnn_int : (0 : ↥(Current.interiorBlockSet G Λ C x a) → ℝ) ≤
      fun n : ↥(Current.interiorBlockSet G Λ C x a) => ∏ e ∈ Current.interiorEdges G Λ C,
        (β * J) ^ ((n : Current G Λ) e) / (((n : Current G Λ) e).factorial : ℝ) := by
    rw [Pi.le_def]
    intro n
    simp only [Pi.zero_apply]
    exact Finset.prod_nonneg
      (fun e _ => div_nonneg (pow_nonneg hβJ _) (Nat.cast_nonneg _))
  have hnn_ext : (0 : ↥(Current.exteriorBlockSet G Λ C b y) → ℝ) ≤
      fun n : ↥(Current.exteriorBlockSet G Λ C b y) => ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
        (β * J) ^ ((n : Current G Λ) e) / (((n : Current G Λ) e).factorial : ℝ) := by
    rw [Pi.le_def]
    intro n
    simp only [Pi.zero_apply]
    exact Finset.prod_nonneg
      (fun e _ => div_nonneg (pow_nonneg hβJ _) (Nat.cast_nonneg _))
  have hfg := h_int.mul_of_nonneg h_ext hnn_int hnn_ext
  rw [← Equiv.tsum_eq
    (Current.pivotalFiberEquiv G Λ e₀ C x y a b hab haC hbC).symm
    (fun M => (M : Current G Λ).weight G Λ β J)]
  have hpt : ∀ p : ↥(Current.interiorBlockSet G Λ C x a)
        × ↥(Current.exteriorBlockSet G Λ C b y),
      (((Current.pivotalFiberEquiv G Λ e₀ C x y a b hab haC hbC).symm p :
          ↥(Current.pivotalFiberSet G Λ e₀ C x y)) : Current G Λ).weight G Λ β J
        = (β * J) *
          ((∏ e ∈ Current.interiorEdges G Λ C,
              (β * J) ^ ((p.1 : Current G Λ) e)
                / (((p.1 : Current G Λ) e).factorial : ℝ))
            * ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
              (β * J) ^ ((p.2 : Current G Λ) e)
                / (((p.2 : Current G Λ) e).factorial : ℝ)) := by
    intro p
    have hval := Current.weight_glueBlocks_factor G Λ β J e₀ C x y a b hab haC hbC
      (p.1 : Current G Λ) (p.2 : Current G Λ) p.1.2 p.2.2
    rw [show (((Current.pivotalFiberEquiv G Λ e₀ C x y a b hab haC hbC).symm p :
          ↥(Current.pivotalFiberSet G Λ e₀ C x y)) : Current G Λ)
        = Current.glueBlocks G Λ e₀ (p.1 : Current G Λ) (p.2 : Current G Λ) from rfl,
      hval]
    ring
  rw [tsum_congr hpt, tsum_mul_left, ← Summable.tsum_mul_tsum h_int h_ext hfg]
  ring


end Ambient

end IsingModel
