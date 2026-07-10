import IsingModel.ClusterExpansion.FieldSourcePeel
import IsingModel.ClusterExpansion.Families.CompatibleProperties
import IsingModel.Combinatorics.AntidiagonalTupleCard

/-!
# Source-configuration root assignment and injectivity (GJ §17.6.1, brick F5a-2b-i)

Stage 1 of the source-configuration fiber count for the field cluster expansion
toward Glimm–Jaffe (GJ) Theorem 17.6.1 (existence of `∂/∂h` in the
infinite-volume limit).  See the math-before-code note
`.self-local/tex/field-ce-F5a-2b-sourceconfig-fibercount.tex`, §Stage 1.

A *source configuration* `S ∈ fieldSourceConfigs G A` (`FieldSourcePeel.lean`) is
an edge subset every connected component of which meets the observable vertex set
`A`.  Since a component `C` may touch `A` at several vertices, we assign to each
component a **single** root vertex `fieldSourceRoot A C ∈ A ∩ polymerSupport C`
(chosen once via `Classical.choice`), rather than indexing by "the component
containing the `i`-th vertex of `A`" (which would multiply-count a component and
break the `∑`-card identity used downstream).

The brick delivers:

* `fieldSourceRoot A C` — the chosen root vertex of a component;
* `fieldSourceRoot_mem` — on a source configuration, the root lies in
  `A ∩ polymerSupport C`;
* `fieldSourceRoot_injOn` — the root map is injective on the components of a
  source configuration (distinct components are vertex-disjoint, so their roots
  differ);
* `polymerDecomposition_card_le_of_fieldSourceConfigs` — hence a source
  configuration has at most `|A|` components.

Root injectivity uses **only** vertex-disjointness
(`polymerDecomposition_pairwise_vertexDisjoint`); no order on `ι` and no
uniqueness of `Classical.choose` is needed.

Building on the root assignment, brick F5a-2b-ii (§Stage 2–3 of the same note)
adds the **component tuple** map that reconstructs `S` from its per-root
components indexed by `Fin A.card` (via the fixed enumeration `A.equivFin`):

* `fieldSourceComp A S i` — the component of `S` whose root is the `i`-th vertex
  of `A` (or `∅`);
* `fieldSourceComp_biUnion` — the tuple covers `S` (`⋃ᵢ = S`);
* `fieldSourceComp_pairwiseDisjoint` — distinct indices give edge-disjoint
  components (via `IsPolymerVertexDisjoint.toEdgeDisjoint`);
* `fieldSourceComp_card_sum` — hence `∑ᵢ |compᵢ| = |S|`;
* `fieldSourceConfigs_comp_injOn` — the tuple map is injective on the fiber;
* `fieldSourceCardVec` / `fieldSourceCardVec_mem_antidiagonalTuple` — the
  cardinality vector `i ↦ |compᵢ|` lands in `antidiagonalTuple A.card ℓ`
  (Stage 3, the arithmetic hand-off into the F5a-2a composition count).

The per-factor closed-walk count and the capstone fiber bound `(2^{|A|} Δ²)^ℓ`
(brick F5a-2b-iii) are a separate sub-brick.

## Literature

Friedli–Velenik (2017) §3.7.3, Lemma 3.38, pp.116–118 (closed-walk component
counting); Glimm–Jaffe *Quantum Physics* (2nd ed.) Theorem 17.6.1, p.312, and
Chapter 18 §18.4–18.7, pp.378–386 (cluster expansion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {G : SimpleGraph ι} [Fintype G.edgeSet]

omit [Nonempty ι] in
/-- **Each component of a source configuration meets `A`** (GJ §17.6.1, brick
F5a-2b-i; TeX Lemma "component meets `A`").  For `S ∈ fieldSourceConfigs G A` and
`C ∈ polymerDecomposition S`, the intersection `A ∩ polymerSupport C` is nonempty.
This is the filter condition `¬ Disjoint (polymerSupport C) A` rephrased through
`Finset.not_disjoint_iff_nonempty_inter`. -/
theorem fieldSourceConfigs_component_inter_nonempty
    {A : Finset ι} {S C : Finset (Sym2 ι)} (hS : S ∈ fieldSourceConfigs G A)
    (hC : C ∈ polymerDecomposition S) : (A ∩ polymerSupport C).Nonempty := by
  rw [fieldSourceConfigs, Finset.mem_filter] at hS
  have hnd : ¬ Disjoint (polymerSupport C) A := hS.2 C hC
  have h := Finset.not_disjoint_iff_nonempty_inter.mp hnd
  rwa [Finset.inter_comm] at h

/-- **Single root vertex of a component** (GJ §17.6.1, brick F5a-2b-i; TeX
Definition "single root").  When `A ∩ polymerSupport C` is nonempty, pick one of
its elements via `Classical.choice`; otherwise return a default vertex (this
`dite`-totalization value is never used in the source-configuration context,
where the intersection is nonempty by
`fieldSourceConfigs_component_inter_nonempty`).  No order on `ι` is required. -/
noncomputable def fieldSourceRoot (A : Finset ι) (C : Finset (Sym2 ι)) : ι :=
  if h : (A ∩ polymerSupport C).Nonempty then h.choose else Classical.arbitrary ι

/-- **The root lies in `A ∩ polymerSupport C`** (GJ §17.6.1, brick F5a-2b-i; TeX
`fieldSourceRoot ∈ supp C ∩ A`).  On a source configuration `S` with component
`C ∈ polymerDecomposition S`, the intersection is nonempty
(`fieldSourceConfigs_component_inter_nonempty`), so the chosen root satisfies its
defining membership. -/
theorem fieldSourceRoot_mem {A : Finset ι} {S C : Finset (Sym2 ι)}
    (hS : S ∈ fieldSourceConfigs G A) (hC : C ∈ polymerDecomposition S) :
    fieldSourceRoot A C ∈ A ∩ polymerSupport C := by
  have hne : (A ∩ polymerSupport C).Nonempty :=
    fieldSourceConfigs_component_inter_nonempty hS hC
  rw [fieldSourceRoot, dif_pos hne]
  exact hne.choose_spec

/-- **Root injectivity on the components of a source configuration** (GJ §17.6.1,
brick F5a-2b-i capstone; TeX Lemma "root injectivity").  For
`S ∈ fieldSourceConfigs G A`, the map `fieldSourceRoot A` is injective on
`polymerDecomposition S`.  Distinct components are vertex-disjoint
(`polymerDecomposition_pairwise_vertexDisjoint`), and each root lies in its own
component's support (`fieldSourceRoot_mem`); a shared root would therefore lie in
both supports, contradicting disjointness.  Only vertex-disjointness is used. -/
theorem fieldSourceRoot_injOn {A : Finset ι} {S : Finset (Sym2 ι)}
    (hS : S ∈ fieldSourceConfigs G A) :
    Set.InjOn (fieldSourceRoot A) ↑(polymerDecomposition S) := by
  intro C hC C' hC' heq
  by_contra hne
  have hCf : C ∈ polymerDecomposition S := Finset.mem_coe.mp hC
  have hC'f : C' ∈ polymerDecomposition S := Finset.mem_coe.mp hC'
  have h1 : fieldSourceRoot A C ∈ polymerSupport C :=
    (Finset.mem_inter.mp (fieldSourceRoot_mem hS hCf)).2
  have h2 : fieldSourceRoot A C ∈ polymerSupport C' := by
    rw [heq]
    exact (Finset.mem_inter.mp (fieldSourceRoot_mem hS hC'f)).2
  have hdisj : Disjoint (polymerSupport C) (polymerSupport C') :=
    polymerDecomposition_pairwise_vertexDisjoint hC hC' hne
  exact (Finset.disjoint_left.mp hdisj h1) h2

/-- **A source configuration has at most `|A|` components** (GJ §17.6.1, brick
F5a-2b-i; TeX Corollary "`|Γ(S)| ≤ |A|`").  The root map sends the components of
`S ∈ fieldSourceConfigs G A` injectively into `A` (image in `A` by
`fieldSourceRoot_mem`, injective by `fieldSourceRoot_injOn`), so
`(polymerDecomposition S).card ≤ A.card`. -/
theorem polymerDecomposition_card_le_of_fieldSourceConfigs {A : Finset ι}
    {S : Finset (Sym2 ι)} (hS : S ∈ fieldSourceConfigs G A) :
    (polymerDecomposition S).card ≤ A.card := by
  apply Finset.card_le_card_of_injOn (fieldSourceRoot A)
  · intro C hC
    exact (Finset.mem_inter.mp (fieldSourceRoot_mem hS hC)).1
  · exact fieldSourceRoot_injOn hS

/-! ## Component tuple, reconstruction and the cardinality vector (brick F5a-2b-ii) -/

/-- **Per-root component of a source configuration** (GJ §17.6.1, brick F5a-2b-ii;
TeX Definition "component tuple").  Using the fixed enumeration
`A.equivFin.symm : Fin A.card ≃ {x // x ∈ A}`, `fieldSourceComp A S i` is a
component `C ∈ polymerDecomposition S` whose root `fieldSourceRoot A C` is the
`i`-th vertex `↑(A.equivFin.symm i)` of `A` (unique when
`S ∈ fieldSourceConfigs G A`, by `fieldSourceRoot_injOn`; otherwise an arbitrary
such component, since `def` uses `choose` without that hypothesis), and `∅` when
no such component exists.  Indexing by the chosen root (rather than "the
component containing the `i`-th vertex") counts each component at exactly one
index, which is what makes the `∑`-card identity hold. -/
noncomputable def fieldSourceComp (A : Finset ι) (S : Finset (Sym2 ι))
    (i : Fin A.card) : Finset (Sym2 ι) :=
  if h : ∃ C ∈ polymerDecomposition S,
      fieldSourceRoot A C = (↑(A.equivFin.symm i) : ι) then h.choose else ∅

/-- **Each component tuple entry is a subset of `S`** (GJ §17.6.1, brick
F5a-2b-ii).  A genuine entry is a member of `polymerDecomposition S`, hence an
`edgeComponent S e ⊆ S`; the `∅` entry is trivially a subset. -/
theorem fieldSourceComp_subset (A : Finset ι) (S : Finset (Sym2 ι))
    (i : Fin A.card) : fieldSourceComp A S i ⊆ S := by
  unfold fieldSourceComp
  split
  · rename_i h
    have hmem := h.choose_spec.1
    rw [mem_polymerDecomposition] at hmem
    obtain ⟨e, _he, hEq⟩ := hmem
    rw [← hEq]
    exact edgeComponent_subset S e
  · exact Finset.empty_subset S

/-- **The component tuple reconstructs `S`** (GJ §17.6.1, brick F5a-2b-ii crux;
TeX Lemma "reconstruction / ⋃-recovery").  For `S ∈ fieldSourceConfigs G A`,
`⋃_{i : Fin A.card} fieldSourceComp A S i = S`.  Forward: each entry is a subset
of `S` (`fieldSourceComp_subset`).  Backward: an edge `f ∈ S` lies in its own
component `C := edgeComponent S f ∈ polymerDecomposition S`; its root `r ∈ A`
determines the index `i := A.equivFin ⟨r, _⟩`, and `fieldSourceRoot_injOn` forces
the chosen component at `i` to equal `C`, so `f ∈ fieldSourceComp A S i`. -/
theorem fieldSourceComp_biUnion {A : Finset ι} {S : Finset (Sym2 ι)}
    (hS : S ∈ fieldSourceConfigs G A) :
    (Finset.univ : Finset (Fin A.card)).biUnion (fieldSourceComp A S) = S := by
  apply Finset.Subset.antisymm
  · intro f hf
    rw [Finset.mem_biUnion] at hf
    obtain ⟨i, _, hfi⟩ := hf
    exact fieldSourceComp_subset A S i hfi
  · intro f hf
    have hC : edgeComponent S f ∈ polymerDecomposition S :=
      mem_polymerDecomposition.mpr ⟨f, hf, rfl⟩
    have hfC : f ∈ edgeComponent S f := self_mem_edgeComponent hf
    have hrmem : fieldSourceRoot A (edgeComponent S f) ∈ A :=
      (Finset.mem_inter.mp (fieldSourceRoot_mem hS hC)).1
    set i : Fin A.card := A.equivFin ⟨fieldSourceRoot A (edgeComponent S f), hrmem⟩
      with hi
    have hround : (↑(A.equivFin.symm i) : ι) = fieldSourceRoot A (edgeComponent S f) := by
      rw [hi, Equiv.symm_apply_apply]
    have hex : ∃ C ∈ polymerDecomposition S,
        fieldSourceRoot A C = (↑(A.equivFin.symm i) : ι) := by
      exact ⟨edgeComponent S f, hC, hround.symm⟩
    have hspec := hex.choose_spec
    have hchooseEq : hex.choose = edgeComponent S f := by
      apply fieldSourceRoot_injOn hS (Finset.mem_coe.mpr hspec.1) (Finset.mem_coe.mpr hC)
      rw [hspec.2, hround]
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have hval : fieldSourceComp A S i = hex.choose := by
      unfold fieldSourceComp; rw [dif_pos hex]
    rw [hval, hchooseEq]
    exact hfC

/-- **Distinct component tuple entries are edge-disjoint** (GJ §17.6.1, brick
F5a-2b-ii; TeX Lemma "pairwise edge-disjoint").  If either entry is `∅` the
disjointness is trivial; otherwise both are components with distinct roots
(`A.equivFin.symm` and the subtype coercion are injective), hence distinct
components, hence vertex-disjoint
(`polymerDecomposition_pairwise_vertexDisjoint`) and therefore edge-disjoint
(`IsPolymerVertexDisjoint.toEdgeDisjoint`).  No source-configuration hypothesis is
needed: distinct-root injectivity is `polymerDecomposition`-level. -/
theorem fieldSourceComp_pairwiseDisjoint (A : Finset ι) (S : Finset (Sym2 ι)) :
    (↑(Finset.univ : Finset (Fin A.card)) : Set (Fin A.card)).PairwiseDisjoint
      (fieldSourceComp A S) := by
  intro i _ j _ hij
  change Disjoint (fieldSourceComp A S i) (fieldSourceComp A S j)
  by_cases hi : ∃ C ∈ polymerDecomposition S,
      fieldSourceRoot A C = (↑(A.equivFin.symm i) : ι)
  · by_cases hj : ∃ C ∈ polymerDecomposition S,
        fieldSourceRoot A C = (↑(A.equivFin.symm j) : ι)
    · have hvalI : fieldSourceComp A S i = hi.choose := by
        unfold fieldSourceComp; rw [dif_pos hi]
      have hvalJ : fieldSourceComp A S j = hj.choose := by
        unfold fieldSourceComp; rw [dif_pos hj]
      rw [hvalI, hvalJ]
      have hspecI := hi.choose_spec
      have hspecJ := hj.choose_spec
      have hne : hi.choose ≠ hj.choose := by
        intro heq
        have hroot : fieldSourceRoot A hi.choose = fieldSourceRoot A hj.choose := by
          rw [heq]
        rw [hspecI.2, hspecJ.2] at hroot
        have h2 : A.equivFin.symm i = A.equivFin.symm j := Subtype.coe_injective hroot
        exact hij (A.equivFin.symm.injective h2)
      exact (polymerDecomposition_pairwise_vertexDisjoint
        (Finset.mem_coe.mpr hspecI.1) (Finset.mem_coe.mpr hspecJ.1) hne).toEdgeDisjoint
    · have hvalJ : fieldSourceComp A S j = ∅ := by
        unfold fieldSourceComp; rw [dif_neg hj]
      rw [hvalJ]; exact Finset.disjoint_empty_right _
  · have hvalI : fieldSourceComp A S i = ∅ := by
      unfold fieldSourceComp; rw [dif_neg hi]
    rw [hvalI]; exact Finset.disjoint_empty_left _

/-- **The component cardinalities sum to `|S|`** (GJ §17.6.1, brick F5a-2b-ii;
TeX Lemma "card sum").  `∑_{i : Fin A.card} |fieldSourceComp A S i| = |S|`.  The
family is pairwise edge-disjoint (`fieldSourceComp_pairwiseDisjoint`), so
`Finset.card_biUnion` turns the cardinality of the (covering,
`fieldSourceComp_biUnion`) biUnion into the sum of cardinalities. -/
theorem fieldSourceComp_card_sum {A : Finset ι} {S : Finset (Sym2 ι)}
    (hS : S ∈ fieldSourceConfigs G A) :
    ∑ i : Fin A.card, (fieldSourceComp A S i).card = S.card := by
  have hbi := Finset.card_biUnion (fieldSourceComp_pairwiseDisjoint A S)
  rw [fieldSourceComp_biUnion hS] at hbi
  exact hbi.symm

/-- **The component tuple map is injective on the fiber** (GJ §17.6.1, brick
F5a-2b-ii; TeX Lemma "φ is injective on the fiber").  On the fiber of source
configurations of a fixed cardinality `ℓ`, `fieldSourceComp A` is injective: two
source configurations with the same tuple both reconstruct (via
`fieldSourceComp_biUnion`) to the same biUnion, hence are equal. -/
theorem fieldSourceConfigs_comp_injOn {A : Finset ι} (ℓ : ℕ) :
    Set.InjOn (fieldSourceComp A)
      ↑((fieldSourceConfigs G A).filter (fun S => S.card = ℓ)) := by
  intro S hS S' hS' heq
  rw [Finset.mem_coe, Finset.mem_filter] at hS hS'
  have hbi : (Finset.univ : Finset (Fin A.card)).biUnion (fieldSourceComp A S)
      = (Finset.univ : Finset (Fin A.card)).biUnion (fieldSourceComp A S') :=
    congrArg (fun t => (Finset.univ : Finset (Fin A.card)).biUnion t) heq
  rw [fieldSourceComp_biUnion hS.1, fieldSourceComp_biUnion hS'.1] at hbi
  exact hbi

/-- **Cardinality vector of the component tuple** (GJ §17.6.1, brick F5a-2b-ii;
TeX Stage 3).  `fieldSourceCardVec A S i := |fieldSourceComp A S i|`, the
`Fin A.card → ℕ` vector fed into the arithmetic composition count F5a-2a. -/
noncomputable def fieldSourceCardVec (A : Finset ι) (S : Finset (Sym2 ι)) :
    Fin A.card → ℕ := fun i => (fieldSourceComp A S i).card

/-- **The cardinality vector lands in the antidiagonal tuple set** (GJ §17.6.1,
brick F5a-2b-ii; TeX Stage 3).  For `S ∈ fieldSourceConfigs G A` with `|S| = ℓ`,
the vector `fieldSourceCardVec A S` sums to `ℓ` (`fieldSourceComp_card_sum`),
hence lies in `Finset.Nat.antidiagonalTuple A.card ℓ`.  This is the hand-off into
the F5a-2a composition-count factor `(ℓ+1)^{|A|}`. -/
theorem fieldSourceCardVec_mem_antidiagonalTuple {A : Finset ι}
    {S : Finset (Sym2 ι)} {ℓ : ℕ} (hS : S ∈ fieldSourceConfigs G A)
    (hcard : S.card = ℓ) :
    fieldSourceCardVec A S ∈ Finset.Nat.antidiagonalTuple A.card ℓ := by
  rw [Finset.Nat.mem_antidiagonalTuple]
  simp only [fieldSourceCardVec]
  rw [fieldSourceComp_card_sum hS]
  exact hcard

end IsingModel
