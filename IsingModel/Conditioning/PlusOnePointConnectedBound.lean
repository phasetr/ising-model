import IsingModel.Conditioning.PlusOnePointRepresentation
import IsingModel.ClusterExpansion.Basic

/-!
# `+`-boundary one-point connected-component bound (FV §3.7.3, eqs. 3.47–3.48)

The decomposition of the high-temperature `+`-boundary one-point numerator by the
connected component of the origin, and the resulting bound

`⟨σ_0⟩⁺_Λ ≤ ∑_{E₀ : connected component of 0} (tanh βJ)^{|E₀|}`

(FV (3.48)), towards the high-temperature `m*(β)=0` (Issue #3613).

* `componentOfZero` — the edge-connected component of a vertex `z` inside an edge set.
* `componentOfZero_subset`, `mem_componentOfZero_of_incident` — basic structure.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, eqs. (3.47)–(3.48), pp. 117–118.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- **The edge-connected component of a vertex** `z` inside an edge set `X`: the union of
the edge-components of all `X`-edges incident to `z`. Since all edges at `z` share the
vertex `z` they are edge-adjacent, so this is a single connected component (or `∅` when no
edge of `X` is incident to `z`). -/
noncomputable def componentOfZero (X : Finset (Sym2 ι)) (z : ι) : Finset (Sym2 ι) :=
  (X.filter (z ∈ ·)).biUnion (fun e => edgeComponent X e)

/-- The vertex-component is a sub-finset of `X`. -/
theorem componentOfZero_subset (X : Finset (Sym2 ι)) (z : ι) :
    componentOfZero X z ⊆ X := by
  classical
  unfold componentOfZero
  intro e he
  rw [Finset.mem_biUnion] at he
  obtain ⟨f, _, hef⟩ := he
  exact edgeComponent_subset X f hef

/-- Every `X`-edge incident to `z` lies in the vertex-component of `z`. -/
theorem mem_componentOfZero_of_incident {X : Finset (Sym2 ι)} {z : ι} {e : Sym2 ι}
    (he : e ∈ X) (hz : z ∈ e) :
    e ∈ componentOfZero X z := by
  classical
  unfold componentOfZero
  rw [Finset.mem_biUnion]
  exact ⟨e, Finset.mem_filter.mpr ⟨he, hz⟩, self_mem_edgeComponent he⟩

/-- **Incidence closure**: if a vertex `v` lies on a component edge and on another
`X`-edge `e'`, then `e'` is in the component too. The component is closed under shared
vertices — the key to the vertex-disjointness of the complement. -/
theorem componentOfZero_absorbs_incident {X : Finset (Sym2 ι)} {z v : ι} {f : Sym2 ι}
    (hf : f ∈ componentOfZero X z) (hvf : v ∈ f) {e' : Sym2 ι} (he' : e' ∈ X)
    (hv' : v ∈ e') :
    e' ∈ componentOfZero X z := by
  classical
  unfold componentOfZero at hf ⊢
  rw [Finset.mem_biUnion] at hf ⊢
  obtain ⟨g, hg, hfg⟩ := hf
  exact ⟨g, hg, edgeComponent_absorbs_incident hfg hvf he' hv'⟩

/-- **No shared vertex with the complement**: a component edge and a complement edge
(`X \ componentOfZero X z`) never share a vertex. -/
theorem componentOfZero_sdiff_no_shared_vertex {X : Finset (Sym2 ι)} {z : ι}
    {e e' : Sym2 ι} (he : e ∈ componentOfZero X z)
    (he' : e' ∈ X \ componentOfZero X z) {v : ι} (hv : v ∈ e) : v ∉ e' := by
  intro hv'
  exact (Finset.mem_sdiff.mp he').2
    (componentOfZero_absorbs_incident he hv (Finset.mem_sdiff.mp he').1 hv')

/-- **Degree splits across the component / complement**: for any vertex `v`, the
`X`-degree equals the component-degree plus the complement-degree. -/
theorem filter_card_componentOfZero_add (X : Finset (Sym2 ι)) (z : ι) (v : ι) :
    (X.filter (v ∈ ·)).card
      = ((componentOfZero X z).filter (v ∈ ·)).card
        + ((X \ componentOfZero X z).filter (v ∈ ·)).card := by
  classical
  conv_lhs => rw [← Finset.union_sdiff_of_subset (componentOfZero_subset X z)]
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact (Finset.disjoint_sdiff).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- **Complement degree vanishes on the component support**: if some component edge is
incident to `v`, then no complement edge is, so the complement degree at `v` is `0`. -/
theorem filter_card_sdiff_eq_zero_of_mem_support {X : Finset (Sym2 ι)} {z v : ι}
    {f : Sym2 ι} (hf : f ∈ componentOfZero X z) (hvf : v ∈ f) :
    ((X \ componentOfZero X z).filter (v ∈ ·)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e' he'
  exact componentOfZero_sdiff_no_shared_vertex hf he' hvf

/-- **The origin lies in the component support**: if `X` has odd degree at `i` (the
`E⁺;0` condition at `i`), then some component edge is incident to `i`. -/
theorem exists_componentOfZero_mem_of_odd {X : Finset (Sym2 ι)} {i : ι}
    (hodd : Odd ((X.filter (i ∈ ·)).card)) :
    ∃ f ∈ componentOfZero X i, i ∈ f := by
  classical
  have hne : (X.filter (i ∈ ·)).Nonempty := by
    rw [← Finset.card_pos]
    exact hodd.pos
  obtain ⟨e, he⟩ := hne
  rw [Finset.mem_filter] at he
  exact ⟨e, mem_componentOfZero_of_incident he.1 he.2, he.2⟩

/-- **The complement is even on `Λ`** (FV (3.47)): for an edge set `X` with the `E⁺;0`
parity (odd at `i ∈ Λ`, even elsewhere on `Λ`), the complement `X \ componentOfZero X i`
of the origin's component has even degree at every vertex of `Λ`. -/
theorem sdiff_componentOfZero_even_on {X : Finset (Sym2 ι)} {Λ : Finset ι} {i : ι}
    (hi : i ∈ Λ)
    (hX : ∀ v ∈ Λ, Even ((if v = i then 1 else 0) + (X.filter (v ∈ ·)).card)) :
    ∀ v ∈ Λ, Even (((X \ componentOfZero X i).filter (v ∈ ·)).card) := by
  classical
  have hisupp : ∃ f ∈ componentOfZero X i, i ∈ f := by
    apply exists_componentOfZero_mem_of_odd
    have hev := hX i hi
    rw [if_pos rfl] at hev
    rcases Nat.even_or_odd ((X.filter (i ∈ ·)).card) with h | h
    · exact absurd hev (by rw [add_comm]; simpa [Nat.even_add_one] using h)
    · exact h
  intro v hv
  by_cases hvsupp : ∃ f ∈ componentOfZero X i, v ∈ f
  · obtain ⟨f, hf, hvf⟩ := hvsupp
    rw [filter_card_sdiff_eq_zero_of_mem_support hf hvf]
    exact ⟨0, by simp⟩
  · have hvC : ((componentOfZero X i).filter (v ∈ ·)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun e he hve => hvsupp ⟨e, he, hve⟩
    have hadd := filter_card_componentOfZero_add X i v
    rw [hvC, zero_add] at hadd
    have hvne : v ≠ i := by
      rintro rfl; obtain ⟨f, hf, hvf⟩ := hisupp; exact hvsupp ⟨f, hf, hvf⟩
    have hev := hX v hv
    rw [if_neg hvne, zero_add] at hev
    rwa [← hadd]

open Real in
/-- **Connected-component bound for the `+` one-point function** (FV (3.48)):
`⟨σ_i⟩⁺_Λ ≤ ∑_{C} (tanh βJ)^{|C|}`, the sum over the connected components `C` of the
origin arising from the `E⁺;0` subgraphs. Bounding the ratio of the `A`-shifted-even sum
to the even sum by `1` (each complement `X \ componentOfZero X i` is even on `Λ`, so the
restricted even sub-sum never exceeds the full even sum), only the origin's component
survives. Requires `0 ≤ tanh βJ` (high temperature / ferromagnetic). -/
theorem gibbsExpectationBC_plus_singleSpin_h_zero_le_connected [Fintype ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (Λ : Finset ι) {i : ι}
    (hi : i ∈ Λ) (ht : 0 ≤ Real.tanh (β * J)) :
    gibbsExpectationBC G β (fun _ => J) 0 Λ (plusConfig ι) (spinProduct {i})
      ≤ ∑ C ∈ (G.edgeFinset.powerset.filter
          (fun X => ∀ v ∈ Λ, Even ((if v = i then 1 else 0) + (X.filter (v ∈ ·)).card))).image
          (fun X => componentOfZero X i),
          Real.tanh (β * J) ^ C.card := by
  classical
  set t := Real.tanh (β * J) with ht_def
  set Snum := G.edgeFinset.powerset.filter
    (fun X => ∀ v ∈ Λ, Even ((if v = i then 1 else 0) + (X.filter (v ∈ ·)).card)) with hSnum
  set Sden := G.edgeFinset.powerset.filter
    (fun X => ∀ v ∈ Λ, Even ((X.filter (v ∈ ·)).card)) with hSden
  set Comp0s := Snum.image (fun X => componentOfZero X i) with hComp0s
  rw [gibbsExpectationBC_plus_singleSpin_h_zero_ratio G J β Λ i]
  rw [div_le_iff₀ (evenSubgraphSum_pos G J β Λ)]
  -- LHS = ∑_{X∈Snum} t^|X|; fiber over the origin's component
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun X => componentOfZero X i)
    (t := Comp0s) (fun X hX => Finset.mem_image_of_mem _ hX)]
  rw [Finset.sum_mul]
  -- bound each fiber by `t^|C| * den`
  refine Finset.sum_le_sum (fun C hC => ?_)
  -- on the fiber, `t^|X| = t^|C| * t^|X\C|`
  have hstep : ∀ X ∈ Snum.filter (fun X => componentOfZero X i = C),
      t ^ X.card = t ^ C.card * t ^ (X \ C).card := by
    intro X hX
    rw [Finset.mem_filter] at hX
    have hCsub : C ⊆ X := by
      rw [← hX.2]; exact componentOfZero_subset X i
    rw [← pow_add]
    congr 1
    rw [← Finset.card_sdiff_add_card_eq_card hCsub, Nat.add_comm]
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht _)
  -- ∑_{X∈fiber} t^|X\C| ≤ den, via the injective complement map into Sden
  have hinj : ∀ X ∈ Snum.filter (fun X => componentOfZero X i = C),
      ∀ X' ∈ Snum.filter (fun X => componentOfZero X i = C),
      X \ C = X' \ C → X = X' := by
    intro X hX X' hX' heq
    rw [Finset.mem_filter] at hX hX'
    have hCX : C ⊆ X := by rw [← hX.2]; exact componentOfZero_subset X i
    have hCX' : C ⊆ X' := by rw [← hX'.2]; exact componentOfZero_subset X' i
    rw [← Finset.union_sdiff_of_subset hCX, ← Finset.union_sdiff_of_subset hCX', heq]
  have himg : (∑ X ∈ Snum.filter (fun X => componentOfZero X i = C), t ^ (X \ C).card)
      = ∑ R ∈ (Snum.filter (fun X => componentOfZero X i = C)).image (fun X => X \ C),
          t ^ R.card := (Finset.sum_image (f := fun R => t ^ R.card) hinj).symm
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun R _ _ => pow_nonneg ht _)
  -- the complement images land in the even-on-Λ subgraphs `Sden`
  intro R hR
  rw [Finset.mem_image] at hR
  obtain ⟨X, hXfib, hRX⟩ := hR
  rw [Finset.mem_filter] at hXfib
  obtain ⟨hXSnum, hXC⟩ := hXfib
  rw [hSnum, Finset.mem_filter, Finset.mem_powerset] at hXSnum
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, ?_⟩
  · rw [← hRX, ← hXC]
    exact (Finset.sdiff_subset).trans hXSnum.1
  · rw [← hRX, ← hXC]
    exact sdiff_componentOfZero_even_on hi hXSnum.2

end IsingModel
