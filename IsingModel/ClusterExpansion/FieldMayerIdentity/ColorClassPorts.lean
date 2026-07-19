import IsingModel.ClusterExpansion.FieldMayerTerm
import IsingModel.ClusterExpansion.Families.FieldConnectedPolymers
import IsingModel.ClusterExpansion.MayerCore.LogTaylor
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre

/-!
# Field Mayer–Montroll identity: colour-class ports (connected species)
(GJ §17.6.1, brick 4 — child 2 of 4)

The L2 species / colour-class ports for the field-dependent connected polymer gas:
colour-class membership, injectivity on colour classes, fibre-cardinality `r!`, and
the family-tuple / colouring-sum identities.  See `FieldMayerIdentity.lean` for the
full module overview.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## L2: species / colour-class ports (connected species) -/

/-- **Colour classes of a proper surjective colouring are nonempty vertex-disjoint
connected families**: for `ω` valued in `allConnectedPolymers G` and a proper
colouring of its incompatibility graph, each colour class lies in
`(vdConnectedPolymerFamilies G).erase ∅`.  Field mirror of
`colorClass_mem_vdCompatiblePolymerFamilies`; simpler since the connected
membership carries no `IsPolymer` clause. -/
theorem fieldColorClass_mem_vdConnectedPolymerFamilies
    (G : SimpleGraph ι) [Fintype G.edgeSet] {r : ℕ} {ω : Fin r → Finset (Sym2 ι)}
    (hω : ∀ i, ω i ∈ allConnectedPolymers G) {k : ℕ} {c : Fin r → Fin k}
    (hproper : IsProperColoring (polymerSeqIncompatibilityGraph ω) k c)
    (hsurj : Function.Surjective c) (x : Fin k) :
    colorClass ω c x ∈ (vdConnectedPolymerFamilies G).erase ∅ := by
  rw [Finset.mem_erase]
  refine ⟨(colorClass_nonempty hsurj x).ne_empty, ?_⟩
  rw [mem_vdConnectedPolymerFamilies]
  refine ⟨?_, ?_⟩
  · intro Q hQ
    obtain ⟨i, _, rfl⟩ := mem_colorClass.mp hQ
    exact hω i
  · intro P hP Q hQ hPQ
    obtain ⟨i, hi, rfl⟩ := mem_colorClass.mp (Finset.mem_coe.mp hP)
    obtain ⟨j, hj, rfl⟩ := mem_colorClass.mp (Finset.mem_coe.mp hQ)
    have hij : i ≠ j := fun h => hPQ (by rw [h])
    have hnotadj : ¬ (polymerSeqIncompatibilityGraph ω).Adj i j := fun hadj =>
      hproper i j hadj (hi.trans hj.symm)
    rw [polymerSeqIncompatibilityGraph_adj] at hnotadj
    have hcompat : ¬ PolymersIncompatible (ω i) (ω j) := fun hinc => hnotadj ⟨hij, hinc⟩
    rwa [PolymersIncompatible.iff_not_isPolymerVertexDisjoint, not_not] at hcompat

/-- **A polymer sequence over `allConnectedPolymers` is injective on each colour
class**: two equal-coloured indices with equal polymers coincide (same-colour
indices are non-adjacent, hence vertex-disjoint, and a nonempty polymer is not
vertex-disjoint from itself).  Field mirror of `seq_injective_on_colorClass`. -/
theorem fieldSeq_injective_on_colorClass
    (G : SimpleGraph ι) [Fintype G.edgeSet] {r : ℕ} {ω : Fin r → Finset (Sym2 ι)}
    (hω : ∀ i, ω i ∈ allConnectedPolymers G) {m : ℕ} {c : Fin r → Fin m}
    (hproper : IsProperColoring (polymerSeqIncompatibilityGraph ω) m c)
    {i j : Fin r} (hc : c i = c j) (hωij : ω i = ω j) : i = j := by
  by_contra hij
  have hnotadj : ¬ (polymerSeqIncompatibilityGraph ω).Adj i j := fun hadj => hproper i j hadj hc
  rw [polymerSeqIncompatibilityGraph_adj] at hnotadj
  have hvd : IsPolymerVertexDisjoint (ω i) (ω j) := by
    by_contra hinc
    exact hnotadj ⟨hij, (PolymersIncompatible.iff_not_isPolymerVertexDisjoint).mpr hinc⟩
  rw [hωij] at hvd
  exact not_isPolymerVertexDisjoint_self_of_nonempty
    (mem_allConnectedPolymers.mp (hω j)).nonempty hvd

/-- **Field activity factor as a product over colour classes**: for `ω` valued in
`allConnectedPolymers G` and a proper colouring `c` of its incompatibility graph,
`fieldClusterSeqActivity a b ω = ∏_x ∏_{P ∈ colorClass ω c x} w_{a,b}(P)`.  Group
the sequence indices by colour and use injectivity of `ω` on each class (the field
weight is a per-polymer multiplicative label).  Field mirror of
`clusterSeqActivity_eq_prod_colorClass`. -/
theorem fieldClusterSeqActivity_eq_prod_colorClass
    (G : SimpleGraph ι) [Fintype G.edgeSet] (a b : ℝ) {r : ℕ}
    {ω : Fin r → Finset (Sym2 ι)}
    (hω : ∀ i, ω i ∈ allConnectedPolymers G) {m : ℕ} {c : Fin r → Fin m}
    (hproper : IsProperColoring (polymerSeqIncompatibilityGraph ω) m c) :
    fieldClusterSeqActivity a b ω =
      ∏ x : Fin m, ∏ P ∈ colorClass ω c x, fieldPolymerWeight a b P := by
  classical
  rw [fieldClusterSeqActivity,
    ← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := c)
      (f := fun i => fieldPolymerWeight a b (ω i)) (fun i _ => Finset.mem_univ (c i))]
  refine Finset.prod_congr rfl (fun x _ => ?_)
  have hinj : ∀ i ∈ Finset.univ.filter (fun i => c i = x),
      ∀ j ∈ Finset.univ.filter (fun i => c i = x), ω i = ω j → i = j := by
    intro i hi j hj hij
    rw [Finset.mem_filter] at hi hj
    exact fieldSeq_injective_on_colorClass G hω hproper (hi.2.trans hj.2.symm) hij
  have hcc : colorClass ω c x = (Finset.univ.filter (fun i => c i = x)).image ω := rfl
  rw [hcc, Finset.prod_image hinj]

/-- **Forward map is injective** (connected species): distinct indices give
distinct labelled polymers, via `fieldSeq_injective_on_colorClass`.  Field mirror
of `seqColoringForward_injective` (`seqColoringForward` itself is species-agnostic
and reused verbatim). -/
theorem fieldSeqColoringForward_injective {r m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] {Ω : Fin m → Finset (Finset (Sym2 ι))}
    {ω : Fin r → Finset (Sym2 ι)} {c : Fin r → Fin m}
    (hω : ∀ i, ω i ∈ allConnectedPolymers G)
    (hproper : IsProperColoring (polymerSeqIncompatibilityGraph ω) m c)
    (hcolor : ∀ x, colorClass ω c x = Ω x) :
    Function.Injective (seqColoringForward hcolor) := by
  intro i j hij
  simp only [seqColoringForward, Subtype.mk.injEq, Sigma.mk.injEq, heq_eq_eq] at hij
  exact fieldSeq_injective_on_colorClass G hω hproper hij.1 hij.2

/-- **Inverse colouring is proper** (connected species): the colouring induced by
a bijection `e : Fin r ≃ labelledPolymers Ω` is proper for the incompatibility
graph, using pairwise vertex-disjointness of each family `Ω x`.  Field mirror of
`invProper` with the `IsCompatiblePolymerFamilyVertexDisjoint` hypothesis replaced
by the bare pairwise clause carried by connected families. -/
theorem fieldInvProper {r m : ℕ}
    {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ x, (↑(Ω x) : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint)
    (e : Fin r ≃ ↥(labelledPolymers Ω)) :
    IsProperColoring (polymerSeqIncompatibilityGraph (fun i => (e i).val.2)) m
      (fun i => (e i).val.1) := by
  intro i j hadj hc
  rw [polymerSeqIncompatibilityGraph_adj] at hadj
  dsimp only at hc
  have hne : (e i).val.2 ≠ (e j).val.2 := by
    intro hP
    apply hadj.1
    apply e.injective
    apply Subtype.ext
    apply Sigma.ext hc
    rw [heq_eq_eq]; exact hP
  have hmi := mem_labelledPolymers.mp (e i).property
  have hmj := mem_labelledPolymers.mp (e j).property
  have hmj' : (e j).val.2 ∈ Ω ((e i).val.1) := by rw [hc]; exact hmj
  have hvd : IsPolymerVertexDisjoint (e i).val.2 (e j).val.2 :=
    (hΩ ((e i).val.1)) (Finset.mem_coe.mpr hmi) (Finset.mem_coe.mpr hmj') hne
  exact (PolymersIncompatible.iff_not_isPolymerVertexDisjoint.mp hadj.2) hvd

/-- **Colour-class fibre cardinality is `r!`** (connected species): the pairs
`(ω, c)` — a polymer sequence over `allConnectedPolymers G` and a proper colouring
whose colour classes are exactly `Ω` — number `r!` (they biject with the orderings
`Fin r ≃ labelledPolymers Ω`).  Field mirror of `card_proper_colorClass_fiber`. -/
theorem fieldCard_proper_colorClass_fiber {r m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ x, Ω x ∈ vdConnectedPolymerFamilies G)
    (hr : r = (labelledPolymers Ω).card) :
    Fintype.card {p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) //
        (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ x, colorClass p.1 p.2 x = Ω x)} = r.factorial := by
  classical
  have hsub : ∀ x, Ω x ⊆ allConnectedPolymers G :=
    fun x => (mem_vdConnectedPolymerFamilies.mp (hΩ x)).1
  have hvd : ∀ x, (↑(Ω x) : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint :=
    fun x => (mem_vdConnectedPolymerFamilies.mp (hΩ x)).2
  have E : {p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) //
        (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ x, colorClass p.1 p.2 x = Ω x)} ≃ (Fin r ≃ ↥(labelledPolymers Ω)) :=
    { toFun := fun q => Equiv.ofBijective (seqColoringForward q.2.2.2)
        ⟨fieldSeqColoringForward_injective G q.2.1 q.2.2.1 q.2.2.2,
          seqColoringForward_surjective q.2.2.2⟩
      invFun := fun e => ⟨(fun i => (e i).val.2, fun i => (e i).val.1),
        fun i => hsub _ (mem_labelledPolymers.mp (e i).property), fieldInvProper hvd e,
        invColorClass e⟩
      left_inv := fun q => by apply Subtype.ext; rfl
      right_inv := fun e => by
        apply Equiv.ext; intro i; apply Subtype.ext; rfl }
  rw [Fintype.card_congr E]
  have hcard : Fintype.card (Fin r) = Fintype.card ↥(labelledPolymers Ω) := by
    rw [Fintype.card_fin, Fintype.card_coe, ← hr]
  rw [Fintype.card_equiv (Fintype.equivOfCardEq hcard), Fintype.card_fin]

/-- **Fibre activity sum is `r! · W_{a,b}(Ω)`**: summing the field activity over all
`(ω, c)` whose colour classes are `Ω` gives `r!` copies of the family field weight
`∏_x ∏_{P ∈ Ω x} w_{a,b}(P)`.  Field mirror of `fiber_sum_clusterSeqActivity`. -/
theorem fieldFiber_sum_fieldClusterSeqActivity {r m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] (a b : ℝ) {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ x, Ω x ∈ vdConnectedPolymerFamilies G)
    (hr : r = (labelledPolymers Ω).card) :
    ∑ q : {p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) //
        (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ x, colorClass p.1 p.2 x = Ω x)}, fieldClusterSeqActivity a b q.1.1 =
      (r.factorial : ℝ) * ∏ x : Fin m, ∏ P ∈ Ω x, fieldPolymerWeight a b P := by
  classical
  have hconst : ∀ q : {p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) //
        (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ x, colorClass p.1 p.2 x = Ω x)},
      fieldClusterSeqActivity a b q.1.1 =
        ∏ x : Fin m, ∏ P ∈ Ω x, fieldPolymerWeight a b P := by
    intro q
    rw [fieldClusterSeqActivity_eq_prod_colorClass G a b q.2.1 q.2.2.1]
    exact Finset.prod_congr rfl (fun x _ => by rw [q.2.2.2 x])
  rw [Finset.sum_congr rfl (fun q _ => hconst q), Finset.sum_const, Finset.card_univ,
    fieldCard_proper_colorClass_fiber G hΩ hr, nsmul_eq_mul]

open Classical in
/-- **Fibre activity sum as a `Finset`-filter sum**: the product-subtype fibre sum
rewritten as a sum over the `Finset` of `(ω, c)` satisfying the fibre predicate.
Field mirror of `fiber_filter_sum`. -/
theorem fieldFiber_filter_sum {r m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ x, Ω x ∈ vdConnectedPolymerFamilies G)
    (hr : r = (labelledPolymers Ω).card) :
    ∑ p ∈ (Finset.univ : Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
        (fun p => (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
          IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
          (∀ x, colorClass p.1 p.2 x = Ω x)), fieldClusterSeqActivity a b p.1 =
      (r.factorial : ℝ) * ∏ x : Fin m, ∏ P ∈ Ω x, fieldPolymerWeight a b P := by
  classical
  rw [Finset.sum_subtype (Finset.univ.filter
        (fun p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) =>
          (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
            IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
            (∀ x, colorClass p.1 p.2 x = Ω x)))
      (p := fun p => (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ x, colorClass p.1 p.2 x = Ω x))
      (fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      (fun p => fieldClusterSeqActivity a b p.1)]
  exact fieldFiber_sum_fieldClusterSeqActivity G a b hΩ hr

open Classical in
/-- **Colour-count sum as a product-`Finset` sum**: the field activity weighted by
the proper-surjective-colouring count over polymer sequences equals the field
activity summed over the `Finset` of `(ω, c)` pairs with `ω` valued in
`allConnectedPolymers` and `c` a proper surjective colouring.  Field mirror of
`seq_count_eq_product_sum`. -/
theorem fieldSeq_count_eq_product_sum {r m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] (a b : ℝ) :
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
          fieldClusterSeqActivity a b ω =
      ∑ p ∈ (Finset.univ : Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
          (fun p => (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
            IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
            Function.Surjective p.2), fieldClusterSeqActivity a b p.1 := by
  classical
  have hps : ∀ ω : Fin r → Finset (Sym2 ι),
      properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m =
      Finset.univ.filter (fun c : Fin r → Fin m =>
        IsProperColoring (polymerSeqIncompatibilityGraph ω) m c ∧ Function.Surjective c) := by
    intro ω
    ext c
    simp only [mem_properSurjectiveColorings, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcount : ∀ ω : Fin r → Finset (Sym2 ι),
      ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
        fieldClusterSeqActivity a b ω =
      ∑ _c ∈ properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m,
        fieldClusterSeqActivity a b ω := by
    intro ω
    rw [Finset.sum_const, nsmul_eq_mul]
  simp_rw [hcount, hps]
  refine (Finset.sum_finset_product
    (Finset.univ.filter (fun p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) =>
      (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧ Function.Surjective p.2))
    (Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G))
    (fun ω => Finset.univ.filter (fun c : Fin r → Fin m =>
      IsProperColoring (polymerSeqIncompatibilityGraph ω) m c ∧ Function.Surjective c))
    (fun p => ?_) (f := fun p => fieldClusterSeqActivity a b p.1)).symm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]

open Classical in
/-- **Colour-count sum regrouped by colour classes** (fixed `r`): the field
activity-weighted proper-surjective-colouring count over length-`r` sequences
equals, summed over connected family-tuples `Ω`, the field activity over the fibre
of `(ω, c)` with colour classes `Ω`.  Field mirror of `seq_count_eq_fiberwise`. -/
theorem fieldSeq_count_eq_fiberwise {r m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) :
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
          fieldClusterSeqActivity a b ω =
      ∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdConnectedPolymerFamilies G).erase ∅),
        ∑ p ∈ (Finset.univ : Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
            (fun p => (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
              IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
              (∀ x, colorClass p.1 p.2 x = Ω x)), fieldClusterSeqActivity a b p.1 := by
  classical
  rw [fieldSeq_count_eq_product_sum]
  have hmaps : ∀ p ∈ (Finset.univ :
        Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
      (fun p => (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧ Function.Surjective p.2),
      (fun x => colorClass p.1 p.2 x) ∈
        Fintype.piFinset (fun _ : Fin m => (vdConnectedPolymerFamilies G).erase ∅) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [Fintype.mem_piFinset]
    exact fun x => fieldColorClass_mem_vdConnectedPolymerFamilies G hp.1 hp.2.1 hp.2.2 x
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => fieldClusterSeqActivity a b p.1)]
  refine Finset.sum_congr rfl (fun Ω hΩ => ?_)
  rw [Fintype.mem_piFinset] at hΩ
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff]
  constructor
  · rintro ⟨⟨hap, hpr, _⟩, hcol⟩; exact ⟨hap, hpr, hcol⟩
  · rintro ⟨hap, hpr, hcol⟩
    refine ⟨⟨hap, hpr, fun x => ?_⟩, hcol⟩
    obtain ⟨P, hPmem⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp (hΩ x)).1
    rw [← hcol x] at hPmem
    obtain ⟨i, hci, _⟩ := mem_colorClass.mp hPmem
    exact ⟨i, hci⟩

open Classical in
/-- **Inner fibre sum evaluated**: for a connected family-tuple `Ω` of nonempty
vertex-disjoint families, the field activity over the `(ω, c)` fibre with colour
classes `Ω` is `r!·∏_x∏_{P∈Ω x} w_{a,b}(P)` when the total polymer count is `r`,
and `0` otherwise.  Field mirror of `fiber_filter_sum_eval`. -/
theorem fieldFiber_filter_sum_eval {r m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ x, Ω x ∈ (vdConnectedPolymerFamilies G).erase ∅) :
    ∑ p ∈ (Finset.univ : Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
        (fun p => (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
          IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
          (∀ x, colorClass p.1 p.2 x = Ω x)), fieldClusterSeqActivity a b p.1 =
      if (labelledPolymers Ω).card = r then
        (r.factorial : ℝ) * ∏ x : Fin m, ∏ P ∈ Ω x, fieldPolymerWeight a b P else 0 := by
  classical
  have hΩ' : ∀ x, Ω x ∈ vdConnectedPolymerFamilies G :=
    fun x => (Finset.mem_erase.mp (hΩ x)).2
  by_cases hcard : (labelledPolymers Ω).card = r
  · rw [if_pos hcard]
    exact fieldFiber_filter_sum G a b hΩ' hcard.symm
  · rw [if_neg hcard]
    refine Finset.sum_eq_zero (fun p hp => ?_)
    exfalso
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hap, hpr, hcol⟩ := hp
    apply hcard
    have e : Fin r ≃ ↥(labelledPolymers Ω) :=
      Equiv.ofBijective (seqColoringForward hcol)
        ⟨fieldSeqColoringForward_injective G hap hpr hcol, seqColoringForward_surjective hcol⟩
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin, Fintype.card_coe] at hc
    exact hc.symm

open Classical in
/-- **Field family-tuple sum as a polymer-sequence colouring sum** (per-`m`
Mayer–Montroll identity): the connected family-tuple field-weight sum equals the
field activity-weighted proper-surjective-colouring count over polymer sequences
of all lengths, normalised by `1/r!`.  Field mirror of
`vdFamilyTuple_sum_eq_seq_coloring_sum`. -/
theorem fieldVdFamilyTuple_sum_eq_seq_coloring_sum {m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] (a b : ℝ) :
    (∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdConnectedPolymerFamilies G).erase ∅),
        ∏ i : Fin m, ∏ P ∈ Ω i, fieldPolymerWeight a b P) =
      ∑ r ∈ Finset.range (m * (allConnectedPolymers G).card + 1),
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) /
            (r.factorial : ℝ) * fieldClusterSeqActivity a b ω := by
  classical
  have hr : ∀ r : ℕ,
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) /
            (r.factorial : ℝ) * fieldClusterSeqActivity a b ω =
      ∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdConnectedPolymerFamilies G).erase ∅),
        (if (labelledPolymers Ω).card = r then
          ∏ x : Fin m, ∏ P ∈ Ω x, fieldPolymerWeight a b P else 0) := by
    intro r
    have key : ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
          fieldClusterSeqActivity a b ω =
        ∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdConnectedPolymerFamilies G).erase ∅),
          (if (labelledPolymers Ω).card = r then
            (r.factorial : ℝ) *
              ∏ x : Fin m, ∏ P ∈ Ω x, fieldPolymerWeight a b P else 0) := by
      rw [fieldSeq_count_eq_fiberwise]
      refine Finset.sum_congr rfl (fun Ω hΩ => ?_)
      rw [Fintype.mem_piFinset] at hΩ
      exact fieldFiber_filter_sum_eval G a b hΩ
    rw [show (∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) /
            (r.factorial : ℝ) * fieldClusterSeqActivity a b ω) =
        (∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
            fieldClusterSeqActivity a b ω) / (r.factorial : ℝ) from by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun ω _ => by ring),
      key, Finset.sum_div]
    refine Finset.sum_congr rfl (fun Ω _ => ?_)
    split_ifs with h
    · rw [mul_div_cancel_left₀ _ (by positivity : (r.factorial : ℝ) ≠ 0)]
    · rw [zero_div]
  simp_rw [hr]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun Ω hΩ => ?_)
  rw [Fintype.mem_piFinset] at hΩ
  have hsub : ∀ x, Ω x ⊆ allConnectedPolymers G :=
    fun x => (mem_vdConnectedPolymerFamilies.mp (Finset.mem_erase.mp (hΩ x)).2).1
  have hlt : (labelledPolymers Ω).card < m * (allConnectedPolymers G).card + 1 := by
    rw [card_labelledPolymers]
    calc ∑ x : Fin m, (Ω x).card
        ≤ ∑ _x : Fin m, (allConnectedPolymers G).card :=
          Finset.sum_le_sum (fun x _ => Finset.card_le_card (hsub x))
      _ = m * (allConnectedPolymers G).card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ < m * (allConnectedPolymers G).card + 1 := Nat.lt_succ_self _
  rw [Finset.sum_eq_single_of_mem ((labelledPolymers Ω).card) (Finset.mem_range.mpr hlt)
      (fun r _ hr => if_neg (fun h => hr h.symm)), if_pos rfl]

/-- **No proper surjective colouring of an over-long connected sequence**: for `ω`
valued in `allConnectedPolymers G`, if `r > m·|allConnectedPolymers G|` there is
no proper surjective `m`-colouring of its incompatibility graph.  Field mirror of
`properSurjectiveColorings_empty_of_card_lt`. -/
theorem fieldProperSurjectiveColorings_empty_of_card_lt {r m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] {ω : Fin r → Finset (Sym2 ι)}
    (hω : ∀ i, ω i ∈ allConnectedPolymers G)
    (hr : m * (allConnectedPolymers G).card < r) :
    properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c hc
  obtain ⟨hproper, hsurj⟩ := (mem_properSurjectiveColorings _).mp hc
  have e : Fin r ≃ ↥(labelledPolymers (colorClass ω c)) :=
    Equiv.ofBijective (seqColoringForward (fun x => rfl))
      ⟨fieldSeqColoringForward_injective G hω hproper (fun x => rfl),
        seqColoringForward_surjective (fun x => rfl)⟩
  have hcard : r = ∑ x : Fin m, (colorClass ω c x).card := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin, Fintype.card_coe, card_labelledPolymers] at hc
    exact hc
  have hsub : ∀ x, colorClass ω c x ⊆ allConnectedPolymers G := by
    intro x P hP
    obtain ⟨i, _, rfl⟩ := mem_colorClass.mp hP
    exact hω i
  have hle : (∑ x : Fin m, (colorClass ω c x).card) ≤ m * (allConnectedPolymers G).card := by
    calc ∑ x : Fin m, (colorClass ω c x).card
        ≤ ∑ _x : Fin m, (allConnectedPolymers G).card :=
          Finset.sum_le_sum (fun x _ => Finset.card_le_card (hsub x))
      _ = m * (allConnectedPolymers G).card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

end IsingModel
