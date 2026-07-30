import IsingModel.Conditioning.CorrelationClosed.GeneralFieldClosedComplex
import IsingModel.ClusterExpansion.AnchoredPeel

/-!
# Complex field numerator source/avoid weight factorization (GJ §17.6.1, brick F5-pre 1)

Brick F5-pre-1 of the on-book programme toward Glimm–Jaffe (GJ) Theorem 17.6.1
(`∂/∂h` infinite-volume differentiability / `h`-analyticity of the two-point
function in the high-temperature window).  Brick F4b
(`GeneralFieldClosedComplex.lean`) supplied the complex-`h` numerator
\[
\mathrm{Num}^{\mathbb C}(A,a,b)
  = \sum_{X\subseteq E}(\tanh a : \mathbb C)^{|X|}\,
    (\tanh_{\mathbb C} b)^{|\partial X\,\triangle\,A|},
\]
with `∂X = oddBoundary X` and `△ = symmDiff`.  Toward the F5 volume-uniform
geometric ratio bound, one needs to split each subgraph `X` into a part `S`
carrying the observable `A` and an `A`-avoiding remainder `Y`.  This file records
the purely combinatorial **weight factorization** underlying that split: for a
vertex-disjoint union `X = S ∪ Y` in which `Y` avoids `A`,
\[
(\tanh a)^{|X|}\,(\tanh b)^{|\partial X\,\triangle\,A|}
  = \bigl[(\tanh a)^{|S|}\,(\tanh b)^{|\partial S\,\triangle\,A|}\bigr]\cdot
    \bigl[(\tanh a)^{|Y|}\,(\tanh b)^{|\partial Y|}\bigr]
  = w^{\mathbb C}_{A}(S)\cdot w^{\mathbb C}(Y),
\]
where `w^{\mathbb C}_{A}(S) = fieldSourceWeightℂ A a b S` is the `A`-marked source
weight introduced here and `w^{\mathbb C}(Y) = fieldPolymerWeightℂ a b Y` is the
already-existing (field-neutral) polymer weight.

The core boundary-cardinality identity is `symmDiff_card_union_of_disjoint`: when
`Q` is disjoint from both `P` and `A`,
`|(P ∪ Q) △ A| = |P △ A| + |Q|` (proved by direct `sdiff` expansion, no
`Finset.card_symmDiff` dependency).  Everything here is elementary `Finset`
`symmDiff`/cardinality bookkeeping; no new analysis.

Scope of F5-pre-1: the `fieldSourceWeightℂ` definition, the boundary-cardinality
identity, the multiplicative factorization `fieldSourceWeightℂ_union_avoiding`,
two degenerate sanity checks, and the numerator rewrite
`fieldTwoPointNumℂ_eq_sum_fieldSourceWeightℂ` that F5's source peel will consume.
The complete source peel bijection (choosing the source index / `Gavoid` deletion
target) is brick 2, deferred; the volume-uniform geometric ratio bound is F5.

## References
- Friedli–Velenik §3.7.3, eqs. (3.41)–(3.46), pp. 116–117, gives the `h = 0`
  parity template. Exercise 5.8, p. 238, with its Appendix C solution, p. 531,
  gives the exact field factor. The complex source/avoid factor is a project extension.
-/

namespace IsingModel

open Finset
open scoped symmDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`A`-marked complex source weight** (GJ §17.6.1, brick F5-pre-1): for an
observable `A : Finset ι`, coupling `a : ℝ`, complex field `b : ℂ` and a source
edge set `S : Finset (Sym2 ι)`,
\[
w^{\mathbb C}_{A}(S)
  = (\tanh a : \mathbb C)^{|S|}\,(\tanh_{\mathbb C} b)^{|\partial S\,\triangle\,A|},
\]
the per-source summand of the field two-point numerator
`fieldTwoPointNumℂ G A a b`.  It is the field polymer weight `fieldPolymerWeightℂ`
with the odd boundary `∂S` replaced by its symmetric difference with the
observable `A`; specializing `A = ∅` recovers `fieldPolymerWeightℂ`
(`fieldSourceWeightℂ_empty_eq_fieldPolymerWeightℂ`). -/
noncomputable def fieldSourceWeightℂ (A : Finset ι) (a : ℝ) (b : ℂ)
    (S : Finset (Sym2 ι)) : ℂ :=
  (Real.tanh a : ℂ) ^ S.card * (Complex.tanh b) ^ (oddBoundary S ∆ A).card

omit [Fintype ι] in
/-- **Additivity of the marked-boundary cardinality under an avoiding union**: if
`Q` is disjoint from `P` and from the observable `A`, then
`|(P ∪ Q) △ A| = |P △ A| + |Q|`.  Proved by the direct `sdiff` computation
`(P ∪ Q) △ A = (P △ A) ⊔ Q` (using `Q ∩ A = ∅` for both `sdiff` blocks and
`Q ∩ P = ∅` for the disjointness of the union), then cardinality additivity of a
disjoint union — no `Finset.card_symmDiff` dependency.  The combinatorial core of
`fieldSourceWeightℂ_union_avoiding`. -/
private theorem symmDiff_card_union_of_disjoint {P Q A : Finset ι}
    (hQP : Disjoint Q P) (hQA : Disjoint Q A) :
    ((P ∪ Q) ∆ A).card = (P ∆ A).card + Q.card := by
  classical
  have hdisj : Disjoint (P ∆ A) Q := by
    rw [Finset.disjoint_right]
    intro v hvQ hv
    rw [Finset.mem_symmDiff] at hv
    rcases hv with ⟨hvP, _⟩ | ⟨hvA, _⟩
    · exact Finset.disjoint_left.mp hQP hvQ hvP
    · exact Finset.disjoint_left.mp hQA hvQ hvA
  have hset : (P ∪ Q) ∆ A = (P ∆ A) ∪ Q := by
    ext v
    simp only [Finset.mem_symmDiff, Finset.mem_union]
    by_cases hvQ : v ∈ Q
    · have hvP := Finset.disjoint_left.mp hQP hvQ
      have hvA := Finset.disjoint_left.mp hQA hvQ
      tauto
    · tauto
  rw [hset, Finset.card_union_of_disjoint hdisj]

/-- **Source/avoid weight factorization** (GJ §17.6.1, brick F5-pre-1): if `S` and
`Y` are vertex-disjoint (`IsPolymerVertexDisjoint S Y`) and `Y` avoids the
observable `A` (`Disjoint (polymerSupport Y) A`), then the marked source weight of
the union factors as
\[
w^{\mathbb C}_{A}(S \cup Y) = w^{\mathbb C}_{A}(S)\cdot w^{\mathbb C}(Y),
\]
i.e. `fieldSourceWeightℂ A a b (S ∪ Y)
  = fieldSourceWeightℂ A a b S * fieldPolymerWeightℂ a b Y`.  The `tanh(a)^|·|`
factor uses edge-disjoint cardinality additivity
(`IsPolymerVertexDisjoint.toEdgeDisjoint`); the `(tanh b)^{|·|}` factor uses
`oddBoundary_union_of_vertexDisjoint` to split `∂(S ∪ Y) = ∂S ∪ ∂Y` and the core
`symmDiff_card_union_of_disjoint` (with `∂Y` disjoint from `∂S`, via
`oddBoundary_disjoint_of_vertexDisjoint`, and from `A`, via
`oddBoundary_subset_polymerSupport` composed with the avoidance hypothesis).  This
is the field two-point analogue of the neutral factorization
`fieldPolymerWeightℂ_biUnion_of_vd`, specialized to the binary touch/avoid split
of the F5 source peel. -/
theorem fieldSourceWeightℂ_union_avoiding {S Y : Finset (Sym2 ι)}
    (hVD : IsPolymerVertexDisjoint S Y) (A : Finset ι)
    (havoid : Disjoint (polymerSupport Y) A) (a : ℝ) (b : ℂ) :
    fieldSourceWeightℂ A a b (S ∪ Y)
      = fieldSourceWeightℂ A a b S * fieldPolymerWeightℂ a b Y := by
  have hQP : Disjoint (oddBoundary Y) (oddBoundary S) :=
    (oddBoundary_disjoint_of_vertexDisjoint hVD).symm
  have hQA : Disjoint (oddBoundary Y) A :=
    Finset.disjoint_of_subset_left (oddBoundary_subset_polymerSupport Y) havoid
  unfold fieldSourceWeightℂ fieldPolymerWeightℂ
  rw [Finset.card_union_of_disjoint hVD.toEdgeDisjoint,
      oddBoundary_union_of_vertexDisjoint hVD,
      symmDiff_card_union_of_disjoint hQP hQA, pow_add, pow_add]
  ring

/-- **Empty-observable degeneracy** (sanity): with `A = ∅` the marked source
weight `fieldSourceWeightℂ ∅ a b P` reduces to the field polymer weight
`fieldPolymerWeightℂ a b P`, since `∂P △ ∅ = ∂P`. -/
theorem fieldSourceWeightℂ_empty_eq_fieldPolymerWeightℂ (a : ℝ) (b : ℂ)
    (P : Finset (Sym2 ι)) :
    fieldSourceWeightℂ ∅ a b P = fieldPolymerWeightℂ a b P := by
  unfold fieldSourceWeightℂ fieldPolymerWeightℂ
  rw [← Finset.bot_eq_empty, symmDiff_bot]

/-- **Empty-source degeneracy** (sanity): with `S = ∅` the marked source weight
collapses to the pure observable factor
`fieldSourceWeightℂ A a b ∅ = (Complex.tanh b) ^ A.card`, since `∂∅ = ∅` and
`∅ △ A = A`. -/
theorem fieldSourceWeightℂ_empty_source (A : Finset ι) (a : ℝ) (b : ℂ) :
    fieldSourceWeightℂ A a b ∅ = (Complex.tanh b) ^ A.card := by
  have hob : oddBoundary (∅ : Finset (Sym2 ι)) = ∅ := by simp [oddBoundary]
  unfold fieldSourceWeightℂ
  rw [hob, Finset.card_empty, pow_zero, one_mul, ← Finset.bot_eq_empty, bot_symmDiff]

/-- **Field numerator as a source-weight sum** (GJ §17.6.1, brick F5-pre-1): the
complex field two-point numerator is the sum of the marked source weights over all
subgraphs,
`fieldTwoPointNumℂ G A a b = ∑_{X ⊆ E} fieldSourceWeightℂ A a b X`.  Definitional:
each summand `(tanh a)^{|X|}·(tanh b)^{|∂X △ A|}` of `fieldTwoPointNumℂ` is exactly
`fieldSourceWeightℂ A a b X`.  This is the connection point consumed by the F5
source peel (which regroups this sum by the `A`-touching source component). -/
theorem fieldTwoPointNumℂ_eq_sum_fieldSourceWeightℂ (G : SimpleGraph ι)
    [Fintype G.edgeSet] (A : Finset ι) (a : ℝ) (b : ℂ) :
    fieldTwoPointNumℂ G A a b
      = ∑ X ∈ G.edgeFinset.powerset, fieldSourceWeightℂ A a b X := by
  simp only [fieldTwoPointNumℂ, fieldSourceWeightℂ]

end IsingModel
