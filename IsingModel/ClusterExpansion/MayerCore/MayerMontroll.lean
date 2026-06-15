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

end IsingModel
