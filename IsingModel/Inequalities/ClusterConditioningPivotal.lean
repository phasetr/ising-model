import IsingModel.RandomCurrent.ClusterConditioning
import IsingModel.Inequalities.SourcefreeConnectionEdgePivotal

/-!
# SL-C: avoiding / bridge-uniqueness of the pivotal edge

This module implements ingredient **SL-C**: the pointwise-per-current geometric
fact that, on the pivotal fiber conditioned by the cluster value
`C = C_x(M − 1_{e₀})`, the dominant edge `e₀` is the *unique* active edge of `M`
crossing `C`–`Cᶜ`, together with the derived facts `M e₀ = 1` (F2) and "every
other crossing edge carries multiplicity `0`" (F3), which make the SL-A edge
partition `E = E_int ⊔ {e₀} ⊔ E_ext` *exact* on the fiber (Prop.
`Current.weight_pivotal_fiber_factor`). It rests on exactly two merged inputs:
the cut/closure property of the decremented cluster
(`Current.reachableCluster_closed`, SL-B) and the two-arms structure of a pivotal
edge (`Current.edgePivotal_arms`).

SL-C is the *bridge-uniqueness / avoiding constraint* prerequisite of SL-D
(the exterior → `Z`-ratio factorisation): SL-C does **not** perform the ensemble
Fubini / range-independence nor the exterior sum collapse to `Z_{x,y}/Z_∅` — that
genuine research core is SL-D (product-index Fubini + `Z`-ratio collapse), and
SL-E is the re-assembly; both are follow-ups. SL-C is a **tracked ingredient**
(Group 1a authorisation), buildable and axiom-free, with reference-count zero into
the live capstone until SL-D/SL-E land; its intended downstream position is the
(future) Lemma 5.1 → P2-ii → `hLogLip` → the explicitly-tracked
lower-semicontinuity half of GJ Theorem 17.5.1 (§17.5, issue #4386 / thread
#4418). The weight `Current.weight` is `∏_e (βJ)^{n_e}/n_e!`, the random-current
weight of FV, eq. (3.45). (Aizenman 1982 Lemma 4.1; FFS 1992 Ch. 12, pivotal
bridge / backbone.)

## Placement note

SL-C consumes both the SL-B cluster engine (`IsingModel.RandomCurrent.ClusterConditioning`)
and the pivotal-edge infrastructure `Current.EdgePivotal` / `Current.edgePivotal_arms`
/ `Current.not_edgePivotal_of_edge_eq_zero`
(`IsingModel.Inequalities.SourcefreeConnectionEdgePivotal`). Because the latter file
sits *above* the `IsingModel.RandomCurrent` aggregator in the import DAG (that
aggregator imports `ClusterConditioning`), the SL-C block cannot be appended to
`ClusterConditioning.lean` without an import cycle; it therefore lives in this
separate module, importing both dependencies.

## References

* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §3.7,
  eq. (3.45) (random-current weight).
* Glimm–Jaffe, *Quantum Physics*, §17.5 (intended downstream position:
  cluster-conditioning → lsc half of Theorem 17.5.1).
* Aizenman (1982), Lemma 4.1; Fernández–Fröhlich–Sokal (1992), Ch. 12.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **SL-C (F1): the two endpoints of `e₀` are separated by the cluster**
(endpoint split). If `e₀ = s(a, b)` is pivotal for `x, y` in `M`, then exactly
one endpoint of `e₀` lies in the decremented cluster
`C = reachableCluster (M − 1_{e₀}) x`:
\[
  (a \in C \wedge b \notin C) \quad\text{or}\quad (b \in C \wedge a \notin C).
\]
Proof: the two arms of `Current.edgePivotal_arms` place `a` (resp. `b`) in `C` via
`Current.mem_reachableCluster_iff`; were the opposite endpoint also in `C`, its
reachability would compose (`SimpleGraph.Reachable.trans`) into `x ⤳ y` in the
decremented graph, contradicting the second conjunct of `Current.EdgePivotal`.
Part of ingredient **SL-C** (bridge-uniqueness of the pivotal edge, the SL-D
avoiding prerequisite; tracked ingredient, Group 1a, aimed downstream at the
future Lemma 5.1 → `hLogLip` → lsc half of GJ Theorem 17.5.1, §17.5); weight
source FV (3.45). -/
theorem Current.edgePivotal_endpoint_split (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x y a b : ↑Λ)
    (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (hpiv : Current.EdgePivotal G Λ e₀ M x y) :
    (a ∈ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x ∧
       b ∉ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x) ∨
    (b ∈ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x ∧
       a ∉ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x) := by
  have hpiv2 := hpiv.2
  rcases Current.edgePivotal_arms G Λ e₀ M x y a b hab hpiv with
    ⟨hxa, hby⟩ | ⟨hxb, hay⟩
  · left
    refine ⟨(Current.mem_reachableCluster_iff G Λ _ x a).mpr hxa, ?_⟩
    intro hbC
    rw [Current.mem_reachableCluster_iff] at hbC
    exact hpiv2 (hbC.trans hby)
  · right
    refine ⟨(Current.mem_reachableCluster_iff G Λ _ x b).mpr hxb, ?_⟩
    intro haC
    rw [Current.mem_reachableCluster_iff] at haC
    exact hpiv2 (haC.trans hay)

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **SL-C (F2): the pivotal edge has multiplicity exactly one** (`M e₀ = 1`). If
`e₀ = s(a, b)` is pivotal for `x, y` in `M`, then `M e₀ = 1`. Proof: `M e₀ ≥ 1`
(else `M e₀ = 0` forces `M − 1_{e₀} = M`, collapsing `EdgePivotal` into
`Reachable x y ∧ ¬ Reachable x y`, `Current.not_edgePivotal_of_edge_eq_zero`).
If `M e₀ ≥ 2`, then `(M − 1_{e₀}) e₀ = M e₀ − 1 ≥ 1`, so `e₀` is active in
`M − 1_{e₀}` (`Current.Adj (M − 1_{e₀}) a b`); but F1 separates `a, b` across
`C = reachableCluster (M − 1_{e₀}) x`, contradicting the cut property
`Current.reachableCluster_closed`. Hence `M e₀ = 1` — the combinatorial fact
behind the `(βJ)^1/1! = βJ` factor of the SL-A split. Part of ingredient **SL-C**
(bridge-uniqueness; tracked ingredient, Group 1a, aimed downstream at the future
Lemma 5.1 → `hLogLip` → lsc half of GJ Theorem 17.5.1, §17.5); weight FV (3.45). -/
theorem Current.edgePivotal_dominant_edge_eq_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x y a b : ↑Λ)
    (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (hpiv : Current.EdgePivotal G Λ e₀ M x y) :
    M e₀ = 1 := by
  rcases Nat.lt_or_ge (M e₀) 2 with h2 | h2
  · have hne0 : M e₀ ≠ 0 := fun h =>
      Current.not_edgePivotal_of_edge_eq_zero G Λ e₀ M x y h hpiv
    omega
  · exfalso
    have hab_ne : a ≠ b := by
      have hmem := e₀.2
      rw [hab, SimpleGraph.mem_edgeSet] at hmem
      exact hmem.ne
    have hM'e0 : (M - Current.fromEdgeFinset G Λ {e₀}) e₀ = M e₀ - 1 := by
      rw [Current.sub_apply]; simp [Current.fromEdgeFinset]
    have hpos : (M - Current.fromEdgeFinset G Λ {e₀}) e₀ ≠ 0 := by rw [hM'e0]; omega
    have hamem : a ∈ (e₀ : Sym2 ↑Λ) := by rw [hab]; exact Sym2.mem_mk_left a b
    have hbmem : b ∈ (e₀ : Sym2 ↑Λ) := by rw [hab]; exact Sym2.mem_mk_right a b
    have hAdj : (M - Current.fromEdgeFinset G Λ {e₀}).Adj G Λ a b :=
      ⟨hab_ne, e₀,
        (Current.mem_support_iff G Λ (M - Current.fromEdgeFinset G Λ {e₀}) e₀).mpr hpos,
        hamem, hbmem⟩
    rcases Current.edgePivotal_endpoint_split G Λ e₀ M x y a b hab hpiv with
      ⟨haC, hbC⟩ | ⟨hbC, haC⟩
    · exact hbC (Current.reachableCluster_closed G Λ _ x haC hAdj)
    · exact haC (Current.reachableCluster_closed G Λ _ x hbC (Current.Adj_symm G Λ _ hAdj))

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **SL-C (F3): no other edge of `M` crosses the cluster** (no spectator
crossing). If `e ≠ e₀` has `(e : Sym2 ↑Λ) = s(w, w')` with `w` in and `w'` out of
`C = reachableCluster (M − 1_{e₀}) x`, then `M e = 0` (so `e` is not active in
`M`). Proof: since `e ≠ e₀`, `(M − 1_{e₀}) e = M e` (`Current.sub_apply` /
`Current.fromEdgeFinset`); were `M e > 0`, then `e` is active in `M − 1_{e₀}`, so
`Current.Adj (M − 1_{e₀}) w w'`, and the cut property
`Current.reachableCluster_closed` would force `w' ∈ C`, contradicting `w' ∉ C`.
The pivotal hypothesis is not needed (the fact is the elementary cut/closure at
`M − 1_{e₀}`), so this is the geometric strengthening consumed by F4. Part of
ingredient **SL-C** (bridge-uniqueness; tracked ingredient, Group 1a, aimed
downstream at the future Lemma 5.1 → `hLogLip` → lsc half of GJ Theorem 17.5.1,
§17.5); weight FV (3.45). -/
theorem Current.edgePivotal_no_spectator_crossing (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ e : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x w w' : ↑Λ)
    (hw : w ∈ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x)
    (hw' : w' ∉ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x)
    (he : (e : Sym2 ↑Λ) = s(w, w')) (hne : e ≠ e₀) :
    M e = 0 := by
  by_contra hMe
  have hM'e : (M - Current.fromEdgeFinset G Λ {e₀}) e = M e := by
    rw [Current.sub_apply]; simp [Current.fromEdgeFinset, if_neg hne]
  have hpos : (M - Current.fromEdgeFinset G Λ {e₀}) e ≠ 0 := by rw [hM'e]; exact hMe
  have hwne : w ≠ w' := by rintro rfl; exact hw' hw
  have hwmem : w ∈ (e : Sym2 ↑Λ) := by rw [he]; exact Sym2.mem_mk_left w w'
  have hw'mem : w' ∈ (e : Sym2 ↑Λ) := by rw [he]; exact Sym2.mem_mk_right w w'
  have hAdj : (M - Current.fromEdgeFinset G Λ {e₀}).Adj G Λ w w' :=
    ⟨hwne, e,
      (Current.mem_support_iff G Λ (M - Current.fromEdgeFinset G Λ {e₀}) e).mpr hpos,
      hwmem, hw'mem⟩
  exact hw' (Current.reachableCluster_closed G Λ _ x hw hAdj)

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **SL-C (F4): `e₀` is the unique active crossing edge** (bridge-uniqueness). If
`e₀ = s(a, b)` is pivotal for `x, y` in `M`, then in `M` the edge `e₀` is the
unique active edge crossing `C = reachableCluster (M − 1_{e₀}) x`: (i) `e₀` is
active in `M` (`Current.Adj M a b`) with its endpoints separated by `C` (F1); and
(ii) for any `w ∈ C`, `w' ∉ C` with `Current.Adj M w w'`, the witnessing support
pair equals `e₀`, i.e. `s(w, w') = (e₀ : Sym2 ↑Λ)`. Proof: (i) from `M e₀ = 1`
(F2) and F1; (ii) a witnessing active edge `e` of the adjacency has
`(e : Sym2 ↑Λ) = s(w, w')` (`Sym2.mem_and_mem_iff`); if `e ≠ e₀` it crosses `C`
and is active, contradicting F3, so `e = e₀`. This is the load-bearing geometric
content SL-D requires, holding on the *undecremented* `M`. Part of ingredient
**SL-C** (bridge-uniqueness; tracked ingredient, Group 1a, aimed downstream at the
future Lemma 5.1 → `hLogLip` → lsc half of GJ Theorem 17.5.1, §17.5); weight
FV (3.45). -/
theorem Current.edgePivotal_bridge_unique (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x y a b : ↑Λ)
    (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (hpiv : Current.EdgePivotal G Λ e₀ M x y) :
    M.Adj G Λ a b ∧
    ((a ∈ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x ∧
        b ∉ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x) ∨
     (b ∈ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x ∧
        a ∉ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x)) ∧
    (∀ w w' : ↑Λ,
      w ∈ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x →
      w' ∉ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x →
      M.Adj G Λ w w' → s(w, w') = (e₀ : Sym2 ↑Λ)) := by
  have hMe0 : M e₀ = 1 :=
    Current.edgePivotal_dominant_edge_eq_one G Λ e₀ M x y a b hab hpiv
  have hab_ne : a ≠ b := by
    have hmem := e₀.2
    rw [hab, SimpleGraph.mem_edgeSet] at hmem
    exact hmem.ne
  have hamem : a ∈ (e₀ : Sym2 ↑Λ) := by rw [hab]; exact Sym2.mem_mk_left a b
  have hbmem : b ∈ (e₀ : Sym2 ↑Λ) := by rw [hab]; exact Sym2.mem_mk_right a b
  have hMe0ne : M e₀ ≠ 0 := by rw [hMe0]; omega
  have hAdjab : M.Adj G Λ a b :=
    ⟨hab_ne, e₀, (Current.mem_support_iff G Λ M e₀).mpr hMe0ne, hamem, hbmem⟩
  refine ⟨hAdjab,
    Current.edgePivotal_endpoint_split G Λ e₀ M x y a b hab hpiv, ?_⟩
  intro w w' hw hw' hAdj
  obtain ⟨hwne, e, he, hwe, hw'e⟩ := hAdj
  have hesym : (e : Sym2 ↑Λ) = s(w, w') := (Sym2.mem_and_mem_iff hwne).mp ⟨hwe, hw'e⟩
  by_cases hee : e = e₀
  · rw [hee] at hesym; exact hesym.symm
  · exfalso
    have hMe : M e = 0 :=
      Current.edgePivotal_no_spectator_crossing G Λ e₀ e M x w w' hw hw' hesym hee
    rw [Current.mem_support_iff] at he
    exact he hMe

set_option linter.unusedDecidableInType false in
/-- **Membership in `Current.interiorEdges`**: `e ∈ interiorEdges G Λ C` iff both
endpoints of `e` lie in the vertex set `C`, `∀ w ∈ (e : Sym2 ↑Λ), w ∈ C`. Unfolds
the interior-edge filter. Support lemma for the SL-C exact edge partition. -/
theorem Current.mem_interiorEdges_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (C : Finset ↑Λ) (e : (inducedGraph G Λ).edgeSet) :
    e ∈ Current.interiorEdges G Λ C ↔ ∀ w ∈ (e : Sym2 ↑Λ), w ∈ C := by
  classical
  simp [Current.interiorEdges, Finset.mem_filter]

set_option linter.unusedDecidableInType false in
/-- **Interior edge sets of complementary vertex sets are disjoint**: no edge has
both endpoints in `C` and both endpoints in `Cᶜ`, since a `Sym2` always has a
member (`Sym2.ind`) which cannot lie in both `C` and `Cᶜ`. Support lemma for the
SL-C exact edge partition (the exterior block `interiorEdges Cᶜ` is disjoint from
the interior block `interiorEdges C`). -/
theorem Current.interiorEdges_disjoint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (C : Finset ↑Λ) :
    Disjoint (Current.interiorEdges G Λ C) (Current.interiorEdges G Λ Cᶜ) := by
  rw [Finset.disjoint_left]
  intro e heC heCc
  rw [Current.mem_interiorEdges_iff] at heC heCc
  obtain ⟨w, hw⟩ : ∃ w, w ∈ (e : Sym2 ↑Λ) :=
    Sym2.inductionOn (e : Sym2 ↑Λ) (fun p q => ⟨p, Sym2.mem_mk_left p q⟩)
  exact (Finset.mem_compl.mp (heCc w hw)) (heC w hw)

set_option linter.unusedDecidableInType false in
/-- **SL-C avoiding form: the exact SL-A weight split on the pivotal fiber**
(Prop.). For `M` on the pivotal fiber with cluster value `C`, i.e.
`Current.EdgePivotal G Λ e₀ M x y` and
`reachableCluster (M − 1_{e₀}) x = C`, and `e₀ = s(a, b)`, the FV (3.45) weight
`Current.weight` factorises as
\[
  w(M)
  = \Bigl(\textstyle\prod_{e \in E_{\mathrm{int}}} (\beta J)^{M e}/M e!\Bigr)
    \cdot (\beta J)
    \cdot \Bigl(\textstyle\prod_{e \in E_{\mathrm{ext}}} (\beta J)^{M e}/M e!\Bigr),
\]
with `E_int = interiorEdges C`, `E_ext = interiorEdges Cᶜ`, the interior factor a
function of `M|_{E_int}` and the exterior factor a function of `M|_{E_ext}` only.
Proof: from the SL-A cluster split `Current.weight_cluster_interior_factor` at
`E_int`, split off `e₀ ∈ (E_int)ᶜ` (it crosses `C` by F1, so `e₀ ∉ E_int`),
contributing `(βJ)^{M e₀}/M e₀! = βJ` (F2); the remaining product over
`(E_int)ᶜ \ {e₀}` equals the product over `E_ext` because every crossing edge
`≠ e₀` has `M e = 0` (F3), factor `(βJ)^0/0! = 1`
(`Finset.prod_subset` + `Current.interiorEdges_disjoint`). This is the precise
SL-C deliverable that SL-D consumes; the genuine research core SL-D
(product-index Fubini + exterior → `Z_{x,y}/Z_∅` collapse) and SL-E (re-assembly)
are follow-ups. Part of ingredient **SL-C** (tracked ingredient, Group 1a, aimed
downstream at the future Lemma 5.1 → `hLogLip` → lsc half of GJ Theorem 17.5.1,
§17.5); weight source FV (3.45). -/
theorem Current.weight_pivotal_fiber_factor (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ)
    (e₀ : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x y a b : ↑Λ)
    (C : Finset ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (hpiv : Current.EdgePivotal G Λ e₀ M x y)
    (hC : Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x = C) :
    M.weight G Λ β J
      = (∏ e ∈ Current.interiorEdges G Λ C,
            (β * J) ^ (M e) / ((M e).factorial : ℝ))
        * (β * J)
        * ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
            (β * J) ^ (M e) / ((M e).factorial : ℝ) := by
  have hMe0 : M e₀ = 1 :=
    Current.edgePivotal_dominant_edge_eq_one G Λ e₀ M x y a b hab hpiv
  have hamem : a ∈ (e₀ : Sym2 ↑Λ) := by rw [hab]; exact Sym2.mem_mk_left a b
  have hbmem : b ∈ (e₀ : Sym2 ↑Λ) := by rw [hab]; exact Sym2.mem_mk_right a b
  -- F1 (endpoints separated), rewritten to membership in the fixed cluster value `C`.
  have hsplitC : (a ∈ C ∧ b ∉ C) ∨ (b ∈ C ∧ a ∉ C) := by
    have h := Current.edgePivotal_endpoint_split G Λ e₀ M x y a b hab hpiv
    rw [hC] at h; exact h
  -- `e₀` is not an interior edge (one endpoint escapes `C`)…
  have he0_int : e₀ ∉ Current.interiorEdges G Λ C := by
    rw [Current.mem_interiorEdges_iff]; push Not
    rcases hsplitC with ⟨_, hbC⟩ | ⟨_, haC⟩
    · exact ⟨b, hbmem, hbC⟩
    · exact ⟨a, hamem, haC⟩
  -- …nor an exterior edge (one endpoint stays in `C`).
  have he0_ext : e₀ ∉ Current.interiorEdges G Λ Cᶜ := by
    rw [Current.mem_interiorEdges_iff]; push Not
    rcases hsplitC with ⟨haC, _⟩ | ⟨hbC, _⟩
    · exact ⟨a, hamem, fun h => (Finset.mem_compl.mp h) haC⟩
    · exact ⟨b, hbmem, fun h => (Finset.mem_compl.mp h) hbC⟩
  have he0_mem_compl : e₀ ∈ (Current.interiorEdges G Λ C)ᶜ :=
    Finset.mem_compl.mpr he0_int
  have hdisj := Current.interiorEdges_disjoint G Λ C
  -- The exterior block sits inside `(E_int)ᶜ \ {e₀}`.
  have hsub : Current.interiorEdges G Λ Cᶜ
      ⊆ (Current.interiorEdges G Λ C)ᶜ \ {e₀} := by
    intro e he
    rw [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_singleton]
    refine ⟨Finset.disjoint_right.mp hdisj he, ?_⟩
    rintro rfl; exact he0_ext he
  -- Every edge of `(E_int)ᶜ \ {e₀}` outside `E_ext` crosses `C`, hence `M e = 0`.
  have hone : ∀ e ∈ (Current.interiorEdges G Λ C)ᶜ \ {e₀},
      e ∉ Current.interiorEdges G Λ Cᶜ →
      (β * J) ^ (M e) / ((M e).factorial : ℝ) = 1 := by
    intro e he_t he_notext
    rw [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_singleton] at he_t
    obtain ⟨he_notint, he_ne0⟩ := he_t
    rw [Current.mem_interiorEdges_iff] at he_notint
    push Not at he_notint
    obtain ⟨w', hw'e, hw'C⟩ := he_notint
    rw [Current.mem_interiorEdges_iff] at he_notext
    push Not at he_notext
    obtain ⟨w, hwe, hwCc⟩ := he_notext
    have hwC : w ∈ C := by
      by_contra h; exact hwCc (Finset.mem_compl.mpr h)
    have hwne : w ≠ w' := by rintro rfl; exact hw'C hwC
    have hesym : (e : Sym2 ↑Λ) = s(w, w') :=
      (Sym2.mem_and_mem_iff hwne).mp ⟨hwe, hw'e⟩
    have hwmem :
        w ∈ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x := by
      rw [hC]; exact hwC
    have hw'notmem :
        w' ∉ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x := by
      rw [hC]; exact hw'C
    have hMe : M e = 0 :=
      Current.edgePivotal_no_spectator_crossing G Λ e₀ e M x w w'
        hwmem hw'notmem hesym he_ne0
    rw [hMe]; simp
  -- Assemble: the `(E_int)ᶜ` factor collapses to `βJ · (E_ext factor)`.
  have hstep : (∏ e ∈ (Current.interiorEdges G Λ C)ᶜ,
        (β * J) ^ (M e) / ((M e).factorial : ℝ))
      = (β * J) * ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
          (β * J) ^ (M e) / ((M e).factorial : ℝ) := by
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem he0_mem_compl]
    have hfe0 : (β * J) ^ (M e₀) / ((M e₀).factorial : ℝ) = β * J := by
      rw [hMe0]; simp
    rw [hfe0]
    congr 1
    exact (Finset.prod_subset hsub hone).symm
  calc M.weight G Λ β J
      = (∏ e ∈ Current.interiorEdges G Λ C,
            (β * J) ^ (M e) / ((M e).factorial : ℝ))
          * ∏ e ∈ (Current.interiorEdges G Λ C)ᶜ,
              (β * J) ^ (M e) / ((M e).factorial : ℝ) :=
        Current.weight_cluster_interior_factor G Λ β J M C
    _ = (∏ e ∈ Current.interiorEdges G Λ C,
            (β * J) ^ (M e) / ((M e).factorial : ℝ))
          * ((β * J) * ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
              (β * J) ^ (M e) / ((M e).factorial : ℝ)) := by rw [hstep]
    _ = _ := by ring

end Ambient

end IsingModel
