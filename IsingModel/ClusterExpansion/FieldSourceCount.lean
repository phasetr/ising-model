import IsingModel.ClusterExpansion.FieldSourceRoot
import IsingModel.ClusterExpansion.AnchoredPeel
import IsingModel.Conditioning.EdgeWalkCounting
import IsingModel.Conditioning.WalkCountDegreeBound

/-!
# Source-configuration fiber count: closed-walk factor and capstone (GJ §17.6.1, F5a-2b-iii)

Stages 4–5 of the source-configuration fiber count for the field cluster expansion
toward Glimm–Jaffe (GJ) Theorem 17.6.1 (existence of `∂/∂h` in the infinite-volume
limit).  See the math-before-code note
`.self-local/tex/field-ce-F5a-2b-sourceconfig-fibercount.tex`, §Stage 4–5.

Building on the root assignment and component tuple of brick F5a-2b-i/ii
(`FieldSourceRoot.lean`), this brick supplies the volume-independent fiber bound
`|{S ∈ fieldSourceConfigs G A : |S| = ℓ}| ≤ (2^{|A|} Δ²)^ℓ`, where
`Δ = G.maxDegree`.  The proof injects the fiber into a set of integer-indexed
tuples of edge sets (via the component tuple `fieldSourceComp`), stratifies by the
composition of `ℓ` (the antidiagonal, F5a-2a `antidiagonalTuple_card_le`), and
multiplies the per-index closed-walk counts (FV Lemma 3.38 via
`card_connected_edge_sets_le` + `walksFromCount_le_pow`).

The brick delivers:

* `rootedComponentFiber G z m` — the size-`m` rooted connected edge sets at `z`
  (with the empty set carried by the `m = 0` disjunct);
* `mem_rootedComponentFiber` — the membership unfolding;
* `rootedComponentFiber_card_le` — the per-factor bound `≤ Δ^{2m}`;
* `fieldSourceTarget A ℓ` — the antidiagonal-stratified tuple target;
* `fieldSourceComp_mem_target` — the component tuple lands in the target;
* `fieldSourceTarget_card_le` — the target count `≤ (ℓ+1)^{|A|} Δ^{2ℓ}`;
* `fieldSourceConfigsOfCard_card_le` — the capstone `≤ (2^{|A|} Δ²)^ℓ`.

Every ingredient is independent of the vertex count `|ι|` / volume: the per-factor
closed-walk count is local to its root and bounded by `Δ = G.maxDegree`, and the
constant `2^{|A|}` depends only on the observable support `A`.

## Literature

Friedli–Velenik (2017) §3.7.3, Lemma 3.38 and eqs. (3.47)–(3.49), pp.116–118
(closed-walk component counting and the `(2d)^{2ℓ}` bound) is the `h = 0`
template. The field source-fiber count is a project extension. Glimm–Jaffe
Theorem 17.6.1, p. 313, is retained for project comparison and motivation only,
not as a direct source for this counting argument.
-/

namespace IsingModel

open Finset SimpleGraph

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {G : SimpleGraph ι} [DecidableRel G.Adj] [Fintype G.edgeSet]

/-! ## Stage 4 — the per-factor rooted component fiber and its closed-walk count -/

/-- **Rooted component fiber** (GJ §17.6.1, brick F5a-2b-iii; TeX Definition "rooted
component fiber").  For a root vertex `z` and size `m`, `rootedComponentFiber G z m`
collects the edge subsets `C ⊆ G.edgeFinset` with `|C| = m` that are either empty
(the `m = 0` disjunct, needed because `∅` is neither edge-connected nor has
`z ∈ polymerSupport ∅`) or edge-connected with `z` in their support.  Both branches
inject into the length-`2m` closed walks from `z`, giving the uniform bound
`≤ Δ^{2m}`. -/
noncomputable def rootedComponentFiber (G : SimpleGraph ι) [Fintype G.edgeSet]
    (z : ι) (m : ℕ) : Finset (Finset (Sym2 ι)) := by
  classical
  exact G.edgeFinset.powerset.filter
    (fun C => C.card = m ∧ (m = 0 ∨ (IsEdgeConnected C ∧ z ∈ polymerSupport C)))

omit [DecidableRel G.Adj] [Nonempty ι] in
/-- **Membership in the rooted component fiber** (GJ §17.6.1, brick F5a-2b-iii).
Unfolds `rootedComponentFiber` through `Finset.mem_filter`/`Finset.mem_powerset`. -/
theorem mem_rootedComponentFiber {z : ι} {m : ℕ} {C : Finset (Sym2 ι)} :
    C ∈ rootedComponentFiber G z m ↔
      C ⊆ G.edgeFinset ∧ C.card = m ∧
        (m = 0 ∨ (IsEdgeConnected C ∧ z ∈ polymerSupport C)) := by
  classical
  rw [rootedComponentFiber, Finset.mem_filter, Finset.mem_powerset]

omit [Nonempty ι] in
/-- **Per-factor closed-walk count** (GJ §17.6.1, brick F5a-2b-iii; TeX Lemma
"per-factor bound").  `|rootedComponentFiber G z m| ≤ Δ^{2m}`, `Δ = G.maxDegree`.
For `m = 0` the fiber is contained in `{∅}`, of cardinality `≤ 1 = Δ^0`.  For
`m > 0` every member is an edge-connected subset of `G.edgeFinset` of size `m`
through `z`, so it injects into the length-`2m` closed walks from `z`
(`card_connected_edge_sets_le`, FV Lemma 3.38), whose number is
`≤ walksFromCount G z (2m) ≤ Δ^{2m}` (`walksFromCount_le_pow`,
`G.degree_le_maxDegree`).  Both branches deliver the uniform bound. -/
theorem rootedComponentFiber_card_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (z : ι) (m : ℕ) :
    (rootedComponentFiber G z m).card ≤ G.maxDegree ^ (2 * m) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hsub : rootedComponentFiber G z 0 ⊆ {∅} := by
      intro C hC
      rw [mem_rootedComponentFiber] at hC
      rw [Finset.mem_singleton, ← Finset.card_eq_zero]
      exact hC.2.1
    calc (rootedComponentFiber G z 0).card
        ≤ ({∅} : Finset (Finset (Sym2 ι))).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
      _ = G.maxDegree ^ (2 * 0) := by rw [Nat.mul_zero, pow_zero]
  · refine le_trans (card_connected_edge_sets_le (G := G) z m _ (fun C hC => ?_)) ?_
    · rw [mem_rootedComponentFiber] at hC
      obtain ⟨hCsub, hCcard, hdisj⟩ := hC
      obtain ⟨hconn, hsupp⟩ := hdisj.resolve_left hm.ne'
      exact ⟨hCsub, hconn, hCcard, mem_polymerSupport.mp hsupp⟩
    · refine le_trans ?_ (walksFromCount_le_pow G (fun w => G.degree_le_maxDegree w) (2 * m) z)
      rw [walksFromCount]
      exact Finset.single_le_sum (f := fun u => (G.finsetWalkLength (2 * m) z u).card)
        (fun u _ => Nat.zero_le _) (Finset.mem_univ z)

/-! ## Stage 5 — the antidiagonal-stratified target and the capstone fiber bound -/

/-- **Target tuple set** (GJ §17.6.1, brick F5a-2b-iii; TeX Definition "target set").
The image bound for the component tuple map: over every composition
`t ∈ antidiagonalTuple |A| ℓ` of `ℓ`, take the product of the per-root fibers
`rootedComponentFiber G (↑(A.equivFin.symm i)) (t i)`.  The roots use the same
enumeration `A.equivFin.symm` as `fieldSourceComp`. -/
noncomputable def fieldSourceTarget (A : Finset ι) (ℓ : ℕ) :
    Finset (Fin A.card → Finset (Sym2 ι)) := by
  classical
  exact (Finset.Nat.antidiagonalTuple A.card ℓ).biUnion
    (fun t => Fintype.piFinset
      (fun i => rootedComponentFiber G (↑(A.equivFin.symm i) : ι) (t i)))

omit [DecidableRel G.Adj] in
/-- **The component tuple lands in the target** (GJ §17.6.1, brick F5a-2b-iii; TeX
Lemma "φ lands in the target").  For `S ∈ fieldSourceConfigs G A` with `|S| = ℓ`,
`fieldSourceComp A S ∈ fieldSourceTarget A ℓ`.  Take the cardinality vector
`fieldSourceCardVec A S`, which lies in the antidiagonal
(`fieldSourceCardVec_mem_antidiagonalTuple`).  For each index a genuine component
is edge-connected (`isEdgeConnected_of_mem_polymerDecomposition`) with the root in
its support (`fieldSourceRoot_mem`), landing in the `m > 0` disjunct; an empty
entry has size `0` and lands in the `m = 0` disjunct. -/
theorem fieldSourceComp_mem_target {A : Finset ι} {S : Finset (Sym2 ι)} {ℓ : ℕ}
    (hS : S ∈ fieldSourceConfigs G A) (hcard : S.card = ℓ) :
    fieldSourceComp A S ∈ fieldSourceTarget (G := G) A ℓ := by
  classical
  rw [fieldSourceTarget, Finset.mem_biUnion]
  refine ⟨fieldSourceCardVec A S, fieldSourceCardVec_mem_antidiagonalTuple hS hcard, ?_⟩
  rw [Fintype.mem_piFinset]
  intro i
  rw [mem_rootedComponentFiber]
  refine ⟨?_, rfl, ?_⟩
  · -- each entry is a subset of `S ⊆ G.edgeFinset`
    refine (fieldSourceComp_subset A S i).trans ?_
    rw [fieldSourceConfigs, Finset.mem_filter] at hS
    exact Finset.mem_powerset.mp hS.1
  · by_cases h : ∃ C ∈ polymerDecomposition S,
        fieldSourceRoot A C = (↑(A.equivFin.symm i) : ι)
    · right
      have hval : fieldSourceComp A S i = h.choose := by
        unfold fieldSourceComp; rw [dif_pos h]
      have hmem : h.choose ∈ polymerDecomposition S := h.choose_spec.1
      have hroot : fieldSourceRoot A h.choose = (↑(A.equivFin.symm i) : ι) :=
        h.choose_spec.2
      refine ⟨?_, ?_⟩
      · rw [hval]; exact isEdgeConnected_of_mem_polymerDecomposition hmem
      · rw [hval]
        have hrm := fieldSourceRoot_mem hS hmem
        rw [hroot] at hrm
        exact (Finset.mem_inter.mp hrm).2
    · left
      have hval : fieldSourceComp A S i = ∅ := by
        unfold fieldSourceComp; rw [dif_neg h]
      change fieldSourceCardVec A S i = 0
      simp [fieldSourceCardVec, hval]

omit [Nonempty ι] in
/-- **Target cardinality** (GJ §17.6.1, brick F5a-2b-iii; TeX Lemma "target
cardinality").  `|fieldSourceTarget A ℓ| ≤ (ℓ+1)^{|A|} Δ^{2ℓ}`.  `Finset.card_biUnion_le`
and `Fintype.card_piFinset` reduce to `∑_t ∏_i |rootedComponentFiber …|`; the
per-factor bound (`rootedComponentFiber_card_le`) and `Finset.prod_pow_eq_pow_sum`
turn each product into `Δ^{2∑_i t_i} = Δ^{2ℓ}` on the antidiagonal; the number of
compositions is `≤ (ℓ+1)^{|A|}` (F5a-2a `antidiagonalTuple_card_le`). -/
theorem fieldSourceTarget_card_le (A : Finset ι) (ℓ : ℕ) :
    (fieldSourceTarget (G := G) A ℓ).card
      ≤ (ℓ + 1) ^ A.card * G.maxDegree ^ (2 * ℓ) := by
  classical
  rw [fieldSourceTarget]
  refine le_trans (Finset.card_biUnion_le) ?_
  have hterm : ∀ t ∈ Finset.Nat.antidiagonalTuple A.card ℓ,
      (Fintype.piFinset
        (fun i => rootedComponentFiber G (↑(A.equivFin.symm i) : ι) (t i))).card
        ≤ G.maxDegree ^ (2 * ℓ) := by
    intro t ht
    rw [Fintype.card_piFinset]
    calc ∏ i, (rootedComponentFiber G (↑(A.equivFin.symm i) : ι) (t i)).card
        ≤ ∏ i : Fin A.card, G.maxDegree ^ (2 * t i) :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
            (fun i _ => rootedComponentFiber_card_le G _ (t i))
      _ = G.maxDegree ^ (∑ i : Fin A.card, 2 * t i) :=
          Finset.prod_pow_eq_pow_sum _ _ _
      _ = G.maxDegree ^ (2 * ℓ) := by
          congr 1
          rw [← Finset.mul_sum]
          rw [Finset.Nat.mem_antidiagonalTuple] at ht
          rw [ht]
  calc ∑ t ∈ Finset.Nat.antidiagonalTuple A.card ℓ,
        (Fintype.piFinset
          (fun i => rootedComponentFiber G (↑(A.equivFin.symm i) : ι) (t i))).card
      ≤ ∑ _t ∈ Finset.Nat.antidiagonalTuple A.card ℓ, G.maxDegree ^ (2 * ℓ) :=
        Finset.sum_le_sum hterm
    _ = (Finset.Nat.antidiagonalTuple A.card ℓ).card * G.maxDegree ^ (2 * ℓ) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (ℓ + 1) ^ A.card * G.maxDegree ^ (2 * ℓ) :=
        Nat.mul_le_mul_right _ (antidiagonalTuple_card_le A.card ℓ)

/-- **Capstone source-configuration fiber bound** (GJ §17.6.1, brick F5a-2b-iii
capstone; TeX Proposition "capstone fiber bound").  The number of source
configurations of a fixed size `ℓ` is bounded, volume-independently, by
`(2^{|A|} Δ²)^ℓ`, `Δ = G.maxDegree`.  The component tuple map `fieldSourceComp A`
is injective on the fiber (`fieldSourceConfigs_comp_injOn`) and lands in
`fieldSourceTarget A ℓ` (`fieldSourceComp_mem_target`), so
`Finset.card_le_card_of_injOn` gives `≤ (ℓ+1)^{|A|} Δ^{2ℓ}`
(`fieldSourceTarget_card_le`); the arithmetic `ℓ+1 ≤ 2^ℓ` (`Nat.lt_two_pow_self`)
folds the composition count `(ℓ+1)^{|A|}` into the per-`ℓ` base `(2^{|A|})^ℓ`,
and `Δ^{2ℓ} = (Δ²)^ℓ`.  This is the combinatorial input feeding the geometric
aggregation F5a-3. -/
theorem fieldSourceConfigsOfCard_card_le (A : Finset ι) (ℓ : ℕ) :
    ((fieldSourceConfigs G A).filter (fun S => S.card = ℓ)).card
      ≤ (2 ^ A.card * G.maxDegree ^ 2) ^ ℓ := by
  classical
  have hmapsto : ∀ S ∈ (fieldSourceConfigs G A).filter (fun S => S.card = ℓ),
      fieldSourceComp A S ∈ fieldSourceTarget (G := G) A ℓ := by
    intro S hS
    rw [Finset.mem_filter] at hS
    exact fieldSourceComp_mem_target hS.1 hS.2
  have hle : ((fieldSourceConfigs G A).filter (fun S => S.card = ℓ)).card
      ≤ (fieldSourceTarget (G := G) A ℓ).card :=
    Finset.card_le_card_of_injOn (fieldSourceComp A) hmapsto
      (fieldSourceConfigs_comp_injOn (G := G) (A := A) ℓ)
  refine le_trans hle (le_trans (fieldSourceTarget_card_le A ℓ) ?_)
  -- arithmetic: `(ℓ+1)^{|A|} Δ^{2ℓ} ≤ (2^{|A|} Δ²)^ℓ`
  have hR : (2 ^ A.card * G.maxDegree ^ 2) ^ ℓ
      = 2 ^ (A.card * ℓ) * G.maxDegree ^ (2 * ℓ) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [hR]
  refine Nat.mul_le_mul_right _ ?_
  calc (ℓ + 1) ^ A.card
      ≤ (2 ^ ℓ) ^ A.card :=
        Nat.pow_le_pow_left (Nat.succ_le_of_lt Nat.lt_two_pow_self) _
    _ = 2 ^ (ℓ * A.card) := (pow_mul 2 ℓ A.card).symm
    _ = 2 ^ (A.card * ℓ) := by rw [Nat.mul_comm]

end IsingModel
