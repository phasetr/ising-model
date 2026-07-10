import IsingModel.ClusterExpansion.FieldSourcePeel
import IsingModel.ClusterExpansion.Families.CompatibleProperties

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
uniqueness of `Classical.choose` is needed.  The tuple reconstruction / `∑`-card
identity (2b-ii) and the per-factor closed-walk count / capstone (2b-iii) are
separate sub-bricks.

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

end IsingModel
