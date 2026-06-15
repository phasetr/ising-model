import IsingModel.ClusterExpansion.MayerCore.LogTaylor
import IsingModel.ClusterExpansion.MayerCore.UrsellMajorant
import IsingModel.ClusterExpansion.MayerCore.SurjectiveLogWeight

/-!
# Mayer–Montroll identity `log Ξ = ∑ₙ mayerExpansionTerm` (GJ §18.4, Issue #1499 Phase C)

The §18.4 capstone: the general-`t` Mayer expansion identity
`polymerFreeEnergy G t = ∑' n, mayerExpansionTerm G n t` at finite volume.

Phase A (the `log(1 + ε)` Taylor series, `polymerFreeEnergy_hasSum_via_log`) and
Phase B (the `K_n` closed form) are complete; the general absolute convergence of
the Mayer terms (#3996) is also in place.  The remaining content is the
Mayer–Montroll combinatorial identity matching the log-Taylor `ε`-series
`∑' n, (-1)^n · ε^(n+1)/(n+1)` term-by-term with `∑' n, mayerExpansionTerm G n t`.

This file builds that identity.  The first brick re-expresses each log-Taylor term
as a sum over vertex-disjoint compatible polymer-family tuples
(`logTaylor_eps_term_eq_sum_vdFamilyTuples`), the form that the cluster/Ursell side
reads.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (p. 332) – §18.5 (p. 335).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7.3 (Mayer–Cayley).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Log-Taylor term as a polymer-family-tuple sum**:
the `n`-th term `(-1)^n · ε^(n+1)/(n+1)` of the `log(1+ε)` Taylor series
(`polymerFreeEnergy_hasSum_via_log`) expands, via `vdPolymerFamilies_sum_minus_one_pow`,
into a sum over `(n+1)`-tuples of nonempty vertex-disjoint compatible polymer families,
with the scalar coefficient `(-1)^n/(n+1)` pulled inside.  This is the form the
cluster/Ursell side of the Mayer–Montroll identity consumes. -/
theorem logTaylor_eps_term_eq_sum_vdFamilyTuples
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n *
        (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) / (n + 1) =
      ∑ Ω ∈ Fintype.piFinset
            (fun _ : Fin (n + 1) => (vdCompatiblePolymerFamilies G).erase ∅),
        ((-1 : ℝ) ^ n / (n + 1)) * ∏ i : Fin (n + 1), ∏ P ∈ Ω i, t ^ P.card := by
  rw [vdPolymerFamilies_sum_minus_one_pow G t (n + 1), Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun Ω _ => ?_)
  ring

/-! ### Proper surjective colorings of a finite graph

The Mayer–Montroll regrouping reorganises a tuple of nonempty vertex-disjoint
compatible polymer families (the log-Taylor side) into a polymer *sequence*
`ω : Fin r → allPolymers G` together with a **proper surjective coloring** of the
sequence's incompatibility graph: the colour classes are exactly the families.
We build the coloring universe locally (avoiding mathlib's `Coloring` API). -/

/-- **Proper coloring predicate**: `c : Fin r → Fin k` is proper for `H` when
adjacent vertices get distinct colours.  Colour classes are then independent sets,
i.e. (for an incompatibility graph) compatible polymer families. -/
def IsProperColoring {r : ℕ} (H : SimpleGraph (Fin r)) (k : ℕ) (c : Fin r → Fin k) : Prop :=
  ∀ i j : Fin r, H.Adj i j → c i ≠ c j

/-- **Decidability of properness** (finite domain): used to form the real-valued proper
indicator in the edge inclusion–exclusion expansion. -/
instance {r : ℕ} (H : SimpleGraph (Fin r)) [DecidableRel H.Adj] (k : ℕ) (c : Fin r → Fin k) :
    Decidable (IsProperColoring H k c) := by
  unfold IsProperColoring; infer_instance

/-- **Proper surjective colorings**: the finite set of colourings `Fin r → Fin k`
that are proper for `H` and use every colour.  Surjectivity records that all `k`
families are nonempty; properness that each colour class is a compatible family. -/
noncomputable def properSurjectiveColorings {r : ℕ} (H : SimpleGraph (Fin r))
    [DecidableRel H.Adj] (k : ℕ) : Finset (Fin r → Fin k) := by
  classical
  exact Finset.univ.filter (fun c => IsProperColoring H k c ∧ Function.Surjective c)

/-- **Membership in `properSurjectiveColorings`**. -/
theorem mem_properSurjectiveColorings {r : ℕ} (H : SimpleGraph (Fin r))
    [DecidableRel H.Adj] {k : ℕ} {c : Fin r → Fin k} :
    c ∈ properSurjectiveColorings H k ↔ IsProperColoring H k c ∧ Function.Surjective c := by
  classical
  rw [properSurjectiveColorings, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **No surjective colouring with more colours than vertices**:
`properSurjectiveColorings H k = ∅` when `r < k`, since a surjection
`Fin r → Fin k` forces `k ≤ r`. -/
theorem properSurjectiveColorings_eq_empty_of_card_lt {r : ℕ} (H : SimpleGraph (Fin r))
    [DecidableRel H.Adj] {k : ℕ} (h : r < k) :
    properSurjectiveColorings H k = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c hc
  have hsurj := (mem_properSurjectiveColorings H).mp hc |>.2
  have hle : k ≤ r := by
    have := Fintype.card_le_of_surjective c hsurj
    simpa using this
  omega

/-- **Colour class**: for a polymer sequence `ω : Fin r → polymers` and a colouring
`c : Fin r → Fin k`, the colour class of `a : Fin k` is the family of polymers
`{ω i : c i = a}`.  For a proper colouring of the incompatibility graph this is a
vertex-disjoint compatible polymer family. -/
noncomputable def colorClass {r : ℕ} (ω : Fin r → Finset (Sym2 ι)) {k : ℕ}
    (c : Fin r → Fin k) (a : Fin k) : Finset (Finset (Sym2 ι)) := by
  classical
  exact (Finset.univ.filter (fun i => c i = a)).image ω

omit [Fintype ι] in
/-- **Membership in a colour class**: `Q ∈ colorClass ω c a` iff `Q = ω i` for some
index `i` coloured `a`. -/
theorem mem_colorClass {r : ℕ} {ω : Fin r → Finset (Sym2 ι)} {k : ℕ}
    {c : Fin r → Fin k} {a : Fin k} {Q : Finset (Sym2 ι)} :
    Q ∈ colorClass ω c a ↔ ∃ i : Fin r, c i = a ∧ ω i = Q := by
  classical
  simp only [colorClass, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype ι] in
/-- **Colour classes of a surjective colouring are nonempty**: every colour is used,
so its class contains a polymer. -/
theorem colorClass_nonempty {r : ℕ} {ω : Fin r → Finset (Sym2 ι)} {k : ℕ}
    {c : Fin r → Fin k} (hc : Function.Surjective c) (a : Fin k) :
    (colorClass ω c a).Nonempty := by
  obtain ⟨i, hi⟩ := hc a
  exact ⟨ω i, mem_colorClass.mpr ⟨i, hi, rfl⟩⟩

/-- **Colour classes of a proper surjective colouring are nonempty vertex-disjoint
compatible polymer families**: for a polymer sequence `ω` valued in `allPolymers G`
and a proper colouring of its incompatibility graph, each colour class lies in
`(vdCompatiblePolymerFamilies G).erase ∅`.  Properness forces same-colour polymers
to be compatible (vertex-disjoint); surjectivity forces the class nonempty. -/
theorem colorClass_mem_vdCompatiblePolymerFamilies
    (G : SimpleGraph ι) [Fintype G.edgeSet] {r : ℕ} {ω : Fin r → Finset (Sym2 ι)}
    (hω : ∀ i, ω i ∈ allPolymers G) {k : ℕ} {c : Fin r → Fin k}
    (hproper : IsProperColoring (polymerSeqIncompatibilityGraph ω) k c)
    (hsurj : Function.Surjective c) (a : Fin k) :
    colorClass ω c a ∈ (vdCompatiblePolymerFamilies G).erase ∅ := by
  rw [Finset.mem_erase]
  refine ⟨(colorClass_nonempty hsurj a).ne_empty, ?_⟩
  rw [mem_vdCompatiblePolymerFamilies]
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨i, _, rfl⟩ := mem_colorClass.mp hQ
    exact hω i
  · intro P hP
    obtain ⟨i, _, rfl⟩ := mem_colorClass.mp hP
    exact mem_allPolymers.mp (hω i)
  · intro P hP Q hQ hPQ
    obtain ⟨i, hi, rfl⟩ := mem_colorClass.mp (Finset.mem_coe.mp hP)
    obtain ⟨j, hj, rfl⟩ := mem_colorClass.mp (Finset.mem_coe.mp hQ)
    have hij : i ≠ j := fun h => hPQ (by rw [h])
    have hnotadj : ¬ (polymerSeqIncompatibilityGraph ω).Adj i j := fun hadj =>
      hproper i j hadj (hi.trans hj.symm)
    rw [polymerSeqIncompatibilityGraph_adj] at hnotadj
    have hcompat : ¬ PolymersIncompatible (ω i) (ω j) := fun hinc => hnotadj ⟨hij, hinc⟩
    rwa [PolymersIncompatible.iff_not_isPolymerVertexDisjoint, not_not] at hcompat

/-! ### Edge inclusion–exclusion for proper colourings

The Mayer–Montroll proper-colouring weighted count is expanded edge-by-edge: the proper
indicator of a colouring `c` is the signed sum over subsets of its *bad edges* (the
`H`-edges joining equal-coloured endpoints).  Summing over `c` and swapping the order of
summation reduces the colour count to a surjection count on connected components, which the
`surjective_logWeight_eq_connected_indicator` identity collapses. -/

/-- **Bad edges of a colouring**: the `H`-edges whose two endpoints receive the same
colour under `c`.  A colouring is proper exactly when this set is empty. -/
noncomputable def badColorEdges {r k : ℕ} (H : SimpleGraph (Fin r)) [DecidableRel H.Adj]
    (c : Fin r → Fin k) : Finset (Sym2 (Fin r)) := by
  classical
  exact H.edgeFinset.filter
    (fun e => Sym2.lift ⟨fun a b => c a = c b, fun a b => by simp [eq_comm]⟩ e)

/-- **Properness via bad edges**: `c` is a proper colouring of `H` iff it has no bad edge. -/
theorem isProperColoring_iff_badColorEdges_eq_empty {r k : ℕ} (H : SimpleGraph (Fin r))
    [DecidableRel H.Adj] (c : Fin r → Fin k) :
    IsProperColoring H k c ↔ badColorEdges H c = ∅ := by
  classical
  rw [badColorEdges, Finset.filter_eq_empty_iff]
  constructor
  · intro hproper e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      simpa using hproper a b he
  · intro h i j hadj
    have he : s(i, j) ∈ H.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hadj
    simpa using h he

/-- **Proper indicator as a signed bad-edge sum**: the real-valued proper indicator of `c`
equals `∑_{S ⊆ badColorEdges} (-1)^|S|` (Boolean inclusion–exclusion: the powerset signed
sum is `1` when the bad-edge set is empty and `0` otherwise). -/
theorem proper_indicator_eq_signed_bad_edges {r k : ℕ} (H : SimpleGraph (Fin r))
    [DecidableRel H.Adj] (c : Fin r → Fin k) :
    (if IsProperColoring H k c then (1 : ℝ) else 0) =
      ∑ S ∈ (badColorEdges H c).powerset, (-1 : ℝ) ^ S.card := by
  classical
  by_cases hp : IsProperColoring H k c
  · rw [if_pos hp, (isProperColoring_iff_badColorEdges_eq_empty H c).mp hp]
    simp
  · rw [if_neg hp]
    have hne : (badColorEdges H c).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      exact fun h => hp ((isProperColoring_iff_badColorEdges_eq_empty H c).mpr h)
    rw [show (∑ S ∈ (badColorEdges H c).powerset, (-1 : ℝ) ^ S.card)
        = ((∑ S ∈ (badColorEdges H c).powerset, (-1 : ℤ) ^ S.card : ℤ) : ℝ) from by
          push_cast; rfl,
      Finset.sum_powerset_neg_one_pow_card_of_nonempty hne, Int.cast_zero]

/-- **Constant on an edge set**: `c` assigns equal colours to the two endpoints of every
edge in `S`.  For the bad-edge inclusion–exclusion this is the constraint defining the inner
colour count attached to a chosen edge subset `S`. -/
def ConstantOnEdgeSet {r k : ℕ} (S : Finset (Sym2 (Fin r))) (c : Fin r → Fin k) : Prop :=
  ∀ e ∈ S, Sym2.lift ⟨fun a b => c a = c b, fun a b => by simp [eq_comm]⟩ e

/-- **Constant on edges = constant on components**: `c` is constant along every edge of `S`
iff it is constant on every connected component of the graph `fromEdgeSet ↑S` (i.e. constant
on every `Reachable` pair).  Edge-constancy propagates along walks; conversely each edge is a
single reachable step. -/
theorem constantOnEdgeSet_iff_constant_on_components {r k : ℕ}
    (S : Finset (Sym2 (Fin r))) (c : Fin r → Fin k) :
    ConstantOnEdgeSet S c ↔
      ∀ i j, (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin r)))).Reachable i j → c i = c j := by
  constructor
  · intro hconst i j hreach
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    induction hreach with
    | refl => rfl
    | tail hib hstep ih =>
      rw [SimpleGraph.fromEdgeSet_adj] at hstep
      refine ih.trans ?_
      simpa using hconst _ (Finset.mem_coe.mp hstep.1)
  · intro h e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Sym2.lift_mk]
      by_cases hab : a = b
      · rw [hab]
      · refine h a b (SimpleGraph.Adj.reachable ?_)
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨Finset.mem_coe.mpr he, hab⟩

/-- **Constant-on-components colourings = colourings of the component set**: surjective
colourings of `Fin r` constant on every edge of `S` correspond bijectively to surjective
colourings of the connected-component set of `fromEdgeSet ↑S` (descend through the quotient
`connectedComponentMk`).  This turns the inner colour count of the edge inclusion–exclusion
into a surjection count on the component set, ready for
`surjective_logWeight_eq_connected_indicator`. -/
noncomputable def colorings_constant_on_components_equiv {r k : ℕ}
    (S : Finset (Sym2 (Fin r))) :
    {c : Fin r → Fin k // ConstantOnEdgeSet S c ∧ Function.Surjective c} ≃
      {d : (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin r)))).ConnectedComponent → Fin k //
        Function.Surjective d} where
  toFun c :=
    ⟨SimpleGraph.ConnectedComponent.lift c.1
        (fun v w p _ =>
          ((constantOnEdgeSet_iff_constant_on_components S c.1).mp c.2.1) v w ⟨p⟩),
      by
        intro a
        obtain ⟨v, hv⟩ := c.2.2 a
        exact ⟨_, SimpleGraph.ConnectedComponent.lift_mk.trans hv⟩⟩
  invFun d :=
    ⟨fun v => d.1 ((SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin r)))).connectedComponentMk v),
      by
        refine ⟨?_, ?_⟩
        · rw [constantOnEdgeSet_iff_constant_on_components]
          intro i j hreach
          exact congrArg d.1 (SimpleGraph.ConnectedComponent.sound hreach)
        · intro a
          obtain ⟨comp, hcomp⟩ := d.2 a
          induction comp using SimpleGraph.ConnectedComponent.ind with
          | _ v => exact ⟨v, hcomp⟩⟩
  left_inv c := by
    apply Subtype.ext
    funext v
    simp only [SimpleGraph.ConnectedComponent.lift_mk]
  right_inv d := by
    apply Subtype.ext
    funext comp
    induction comp using SimpleGraph.ConnectedComponent.ind with
    | _ v => simp only [SimpleGraph.ConnectedComponent.lift_mk]

/-- **Connectivity = single component**: `fromEdgeSet ↑S` is connected iff its component set
is a singleton (`Fintype.card … = 1`).  This identifies the surviving terms of the surjective
log-weight collapse (`#components = 1`) with the connected (spanning) edge subsets. -/
theorem connected_iff_card_connectedComponent_eq_one {r : ℕ}
    (S : Finset (Sym2 (Fin r))) :
    (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin r)))).Connected ↔
      Fintype.card (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin r)))).ConnectedComponent = 1 := by
  set G := SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin r))) with hG
  rw [SimpleGraph.connected_iff_exists_forall_reachable, Fintype.card_eq_one_iff]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨G.connectedComponentMk v, fun y => ?_⟩
    induction y using SimpleGraph.ConnectedComponent.ind with
    | _ w => exact (SimpleGraph.ConnectedComponent.sound (hv w)).symm
  · rintro ⟨c₀, hc₀⟩
    induction c₀ using SimpleGraph.ConnectedComponent.ind with
    | _ v =>
      exact ⟨v, fun w =>
        SimpleGraph.ConnectedComponent.exact (hc₀ (G.connectedComponentMk w)).symm⟩

open Classical in
/-- **Constant-on-`T` surjective colour count = component surjection count**: the number of
surjective colourings `Fin r → Fin k` constant on every edge of `T` equals
`surjCount (#components of fromEdgeSet ↑T) k`.  Combines
`colorings_constant_on_components_equiv` with `card_surjective_eq_surjCount`; this is the
inner colour count attached to an edge subset `T` in the Mayer–Montroll edge expansion. -/
theorem card_constantOnEdgeSet_surjective {r k : ℕ} (T : Finset (Sym2 (Fin r))) :
    (Finset.univ.filter
        (fun c : Fin r → Fin k => ConstantOnEdgeSet T c ∧ Function.Surjective c)).card =
      surjCount (Fintype.card
        (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin r)))).ConnectedComponent) k := by
  classical
  rw [← Fintype.card_subtype, Fintype.card_congr (colorings_constant_on_components_equiv T),
    Fintype.card_subtype, card_surjective_eq_surjCount]

/-- **Bad-edge subsets are constant-on-`T` constraints**: for `T ⊆ H.edgeFinset`, `T` is a
subset of `c`'s bad edges iff `c` is constant on every edge of `T`.  This rewrites the inner
`∑_{T ⊆ badColorEdges c}` of the proper indicator as a constraint on a fixed edge subset `T`,
the form consumed by the edge-expansion sum swap. -/
theorem subset_badColorEdges_iff_constantOnEdgeSet {r k : ℕ} (H : SimpleGraph (Fin r))
    [DecidableRel H.Adj] (c : Fin r → Fin k) {T : Finset (Sym2 (Fin r))}
    (hT : T ⊆ H.edgeFinset) :
    T ⊆ badColorEdges H c ↔ ConstantOnEdgeSet T c := by
  classical
  constructor
  · intro hsub e he
    have hmem := hsub he
    rw [badColorEdges, Finset.mem_filter] at hmem
    exact hmem.2
  · intro hconst e he
    rw [badColorEdges, Finset.mem_filter]
    exact ⟨hT he, hconst e he⟩

open Classical in
/-- **Edge expansion of the proper surjective colour count**: expanding the proper indicator
edge-by-edge and swapping the order of summation,
`#properSurjectiveColorings H k = ∑_{T ⊆ E(H)} (-1)^|T| · #{c surjective, constant on T}`. -/
theorem properSurjectiveColorings_card_eq_sum_edges {r k : ℕ} (H : SimpleGraph (Fin r))
    [DecidableRel H.Adj] :
    ((properSurjectiveColorings H k).card : ℝ) =
      ∑ T ∈ H.edgeFinset.powerset, (-1 : ℝ) ^ T.card *
        ((Finset.univ.filter
          (fun c : Fin r → Fin k => ConstantOnEdgeSet T c ∧ Function.Surjective c)).card : ℝ) := by
  classical
  -- card = ∑ over surjective colourings of the proper indicator
  have h1 : ((properSurjectiveColorings H k).card : ℝ) =
      ∑ c ∈ Finset.univ.filter (fun c : Fin r → Fin k => Function.Surjective c),
        (if IsProperColoring H k c then (1 : ℝ) else 0) := by
    rw [properSurjectiveColorings]
    have hreorder : (Finset.univ.filter
          (fun c : Fin r → Fin k => IsProperColoring H k c ∧ Function.Surjective c)) =
        (Finset.univ.filter (fun c : Fin r → Fin k => Function.Surjective c)).filter
          (fun c => IsProperColoring H k c) := by
      rw [Finset.filter_filter]
      exact Finset.filter_congr (fun c _ => and_comm)
    rw [hreorder, Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun c _ => by by_cases hp : IsProperColoring H k c <;> simp [hp])
  rw [h1]
  simp_rw [proper_indicator_eq_signed_bad_edges]
  -- rewrite each inner powerset sum over E(H).powerset with an indicator
  have h2 : ∀ c : Fin r → Fin k,
      (∑ T ∈ (badColorEdges H c).powerset, (-1 : ℝ) ^ T.card) =
        ∑ T ∈ H.edgeFinset.powerset, (if T ⊆ badColorEdges H c then (-1 : ℝ) ^ T.card else 0) := by
    intro c
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext T
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun hT => ⟨hT.trans (Finset.filter_subset _ _), hT⟩, fun h => h.2⟩
  simp_rw [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  rw [Finset.mem_powerset] at hT
  have hcard : (Finset.univ.filter (fun c : Fin r → Fin k => Function.Surjective c)).filter
        (fun c => T ⊆ badColorEdges H c) =
      Finset.univ.filter
        (fun c : Fin r → Fin k => ConstantOnEdgeSet T c ∧ Function.Surjective c) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun c _ => by
      rw [subset_badColorEdges_iff_constantOnEdgeSet H c hT]; exact and_comm)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hcard,
    mul_comm]

/-- **Surjective log-weight over an extended range**: for `m ≤ N`, the alternating
`surjCount m`-weighted sum over `Icc 1 N` still collapses to `[m = 1]`, the extra terms
`k > m` vanishing since `surjCount m k = 0`. -/
theorem surjLogWeight_sum_Icc_of_le {m N : ℕ} (hmN : m ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) * (surjCount m k : ℝ) =
      if m = 1 then 1 else 0 := by
  rw [← surjLogWeight_eq m]
  refine (Finset.sum_subset (fun k hk => ?_) (fun k hkN hkm => ?_)).symm
  · rw [Finset.mem_Icc] at hk ⊢; omega
  · rw [Finset.mem_Icc] at hkN hkm
    rw [surjCount_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

/-- **Mayer–Montroll colouring identity** (GJ §18.4): for any finite graph `H` on `Fin r`,
the alternating proper-surjective-colouring weighted sum equals the alternating
connected-spanning-subgraph sum,
`∑_{k=1}^r (-1)^(k-1)/k · #properSurjectiveColorings H k = alternatingConnectedSubgraphSum H`.
This is the combinatorial heart of the cluster-expansion identity: the edge inclusion–exclusion
collapses to exactly the connected (single-component) edge subsets via the surjective
log-weight identity. -/
theorem mayerMontroll_coloring_identity {r : ℕ} (H : SimpleGraph (Fin r)) [DecidableRel H.Adj] :
    ∑ k ∈ Finset.Icc 1 r, ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
        ((properSurjectiveColorings H k).card : ℝ) =
      alternatingConnectedSubgraphSum H := by
  classical
  simp_rw [properSurjectiveColorings_card_eq_sum_edges H, Finset.mul_sum]
  rw [Finset.sum_comm, alternatingConnectedSubgraphSum, connectedSpanningEdgeSubsets,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  rw [Finset.mem_powerset] at hT
  -- every component count `surjCount (#ConnComp T) k`, factor `(-1)^|T|`, collapse via log-weight
  simp_rw [card_constantOnEdgeSet_surjective T,
    mul_left_comm ((-1 : ℝ) ^ (_ - 1) / _) ((-1 : ℝ) ^ T.card)]
  rw [← Finset.mul_sum]
  have hle : Fintype.card (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin r)))).ConnectedComponent
      ≤ r := by
    have : Fintype.card (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin r)))).ConnectedComponent
        ≤ Fintype.card (Fin r) :=
      Fintype.card_le_of_surjective _ Quot.mk_surjective
    simpa using this
  rw [surjLogWeight_sum_Icc_of_le hle]
  by_cases hconn : (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin r)))).Connected
  · rw [if_pos hconn, if_pos ((connected_iff_card_connectedComponent_eq_one T).mp hconn), mul_one]
  · rw [if_neg hconn,
      if_neg (fun h => hconn ((connected_iff_card_connectedComponent_eq_one T).mpr h)), mul_zero]

/-- **Ursell coefficient as a colouring sum**: combining the definition
`ϕ^T(ω) = alternatingConnectedSubgraphSum (G(ω)) / n!` with the Mayer–Montroll colouring
identity, the Ursell coefficient of a length-`n` polymer sequence is the alternating
proper-surjective-colouring count of its incompatibility graph, normalised by `n!`.  This is
the bridge from the colouring identity to `mayerExpansionTerm`. -/
theorem ursellCoefficient_eq_coloring_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    ursellCoefficient ω =
      (∑ k ∈ Finset.Icc 1 n, ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ)) /
        (n.factorial : ℝ) := by
  rw [ursellCoefficient_eq_alternatingConnectedSubgraphSum_div,
    mayerMontroll_coloring_identity (polymerSeqIncompatibilityGraph ω)]

end IsingModel
