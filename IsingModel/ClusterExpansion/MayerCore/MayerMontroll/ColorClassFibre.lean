import IsingModel.ClusterExpansion.MayerCore.LogTaylor
import IsingModel.ClusterExpansion.MayerCore.UrsellMajorant
import IsingModel.ClusterExpansion.MayerCore.SurjectiveLogWeight
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.EdgeInclusionExclusion

/-!
# The `r!`-to-one colour-class fibre (GJ §18.4)

The final stage of the Mayer–Montroll regrouping.  A family-tuple is recovered
as the colour classes of `r!` distinct sequence/colouring pairs
(`card_proper_colorClass_fiber`), so the fibre activity sum is `r! · W(Ω)`
(`fiber_sum_clusterSeqActivity`).  Assembling the fibre factor with the
colouring form of the Mayer terms yields the Mayer–Montroll identity
`log Ξ = ∑ₙ mayerExpansionTerm` at finite volume
(`mayer_identity_general_t`, `mayer_identity_general_t_eventually`).  Part of the
`MayerMontroll` identity split.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (p. 332) – §18.5 (p. 335).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7.3 (Mayer–Cayley).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The `r!`-to-one colour-class fibre

A family-tuple `Ω : Fin m → families` is recovered as the colour classes of `r!` distinct
pairs `(ω, c)`: a polymer sequence `ω : Fin r → polymers` and a colouring `c : Fin r → Fin m`
satisfy `colorClass ω c = Ω` iff `i ↦ ⟨c i, ω i⟩` is a bijection `Fin r ≃ labelledPolymers Ω`,
the labelled-polymer set `Σ a, Ω a` (whose cardinality is the total polymer count `r`). -/

/-- **Labelled polymers of a family-tuple**: the dependent sum `Σ a : Fin m, Ω a` collecting
each polymer of each colour class tagged with its colour.  Its cardinality is the total
polymer count `∑_a |Ω a|`. -/
noncomputable def labelledPolymers {m : ℕ} (Ω : Fin m → Finset (Finset (Sym2 ι))) :
    Finset ((_ : Fin m) × Finset (Sym2 ι)) :=
  Finset.univ.sigma Ω

omit [Fintype ι] [DecidableEq ι] in
/-- **Cardinality of the labelled-polymer set**: `#(labelledPolymers Ω) = ∑_a |Ω a|`. -/
theorem card_labelledPolymers {m : ℕ} (Ω : Fin m → Finset (Finset (Sym2 ι))) :
    (labelledPolymers Ω).card = ∑ a : Fin m, (Ω a).card := by
  rw [labelledPolymers, Finset.card_sigma]

omit [Fintype ι] in
/-- **Forward map well-definedness**: when the colour classes of `(ω, c)` are exactly `Ω`, the
labelled pair `⟨c i, ω i⟩` lies in `labelledPolymers Ω`.  This is the value map of the fibre
bijection `(ω, c) ↦ (i ↦ ⟨c i, ω i⟩) : Fin r → labelledPolymers Ω`. -/
theorem labelledPair_mem_labelledPolymers {r m : ℕ} {ω : Fin r → Finset (Sym2 ι)}
    {c : Fin r → Fin m} {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hcolor : ∀ a, colorClass ω c a = Ω a) (i : Fin r) :
    (⟨c i, ω i⟩ : (_ : Fin m) × Finset (Sym2 ι)) ∈ labelledPolymers Ω := by
  rw [labelledPolymers, Finset.mem_sigma]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← hcolor (c i)]
  exact mem_colorClass.mpr ⟨i, rfl, rfl⟩

/-- **Forward map of the fibre bijection**: `(ω, c)` with colour classes `Ω` is sent to the
function `i ↦ ⟨c i, ω i⟩ : Fin r → labelledPolymers Ω`. -/
noncomputable def seqColoringForward {r m : ℕ} {Ω : Fin m → Finset (Finset (Sym2 ι))}
    {ω : Fin r → Finset (Sym2 ι)} {c : Fin r → Fin m}
    (hcolor : ∀ a, colorClass ω c a = Ω a) : Fin r → ↥(labelledPolymers Ω) :=
  fun i => ⟨⟨c i, ω i⟩, labelledPair_mem_labelledPolymers hcolor i⟩

/-- **Forward map is injective** (proper colouring): distinct indices give distinct labelled
polymers, since `ω` is injective on each colour class. -/
theorem seqColoringForward_injective {r m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet]
    {Ω : Fin m → Finset (Finset (Sym2 ι))} {ω : Fin r → Finset (Sym2 ι)} {c : Fin r → Fin m}
    (hω : ∀ i, ω i ∈ allPolymers G)
    (hproper : IsProperColoring (polymerSeqIncompatibilityGraph ω) m c)
    (hcolor : ∀ a, colorClass ω c a = Ω a) :
    Function.Injective (seqColoringForward hcolor) := by
  intro i j hij
  simp only [seqColoringForward, Subtype.mk.injEq, Sigma.mk.injEq, heq_eq_eq] at hij
  exact seq_injective_on_colorClass G hω hproper hij.1 hij.2

omit [Fintype ι] in
/-- **Forward map is surjective**: every labelled polymer `⟨a, P⟩` (with `P ∈ Ω a`) is hit,
since `colorClass ω c a = Ω a` means `P = ω i` for some `i` coloured `a`. -/
theorem seqColoringForward_surjective {r m : ℕ} {Ω : Fin m → Finset (Finset (Sym2 ι))}
    {ω : Fin r → Finset (Sym2 ι)} {c : Fin r → Fin m}
    (hcolor : ∀ a, colorClass ω c a = Ω a) :
    Function.Surjective (seqColoringForward hcolor) := by
  rintro ⟨⟨a, P⟩, hmem⟩
  rw [labelledPolymers, Finset.mem_sigma] at hmem
  rw [← hcolor a] at hmem
  obtain ⟨i, hci, hωi⟩ := mem_colorClass.mp hmem.2
  exact ⟨i, by simp only [seqColoringForward, hci, hωi]⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **Membership in `labelledPolymers`**: `x ∈ labelledPolymers Ω ↔ x.2 ∈ Ω x.1`. -/
theorem mem_labelledPolymers {m : ℕ} {Ω : Fin m → Finset (Finset (Sym2 ι))}
    {x : (_ : Fin m) × Finset (Sym2 ι)} :
    x ∈ labelledPolymers Ω ↔ x.2 ∈ Ω x.1 := by
  unfold labelledPolymers
  rw [Finset.mem_sigma]
  simp only [Finset.mem_univ, true_and]

omit [Fintype ι] in
/-- **Inverse colour classes**: for a bijection `e : Fin r ≃ labelledPolymers Ω`, the colour
classes of the sequence/colouring it induces (`ω i = (e i).2`, `c i = (e i).1`) are exactly
`Ω`. -/
theorem invColorClass {r m : ℕ} {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (e : Fin r ≃ ↥(labelledPolymers Ω)) (a : Fin m) :
    colorClass (fun i => (e i).val.2) (fun i => (e i).val.1) a = Ω a := by
  ext P
  rw [mem_colorClass]
  constructor
  · rintro ⟨i, hci, hPi⟩
    have hmem := mem_labelledPolymers.mp (e i).property
    rw [← hPi, ← hci]
    exact hmem
  · intro hP
    have hmem : (⟨a, P⟩ : (_ : Fin m) × Finset (Sym2 ι)) ∈ labelledPolymers Ω :=
      mem_labelledPolymers.mpr hP
    refine ⟨e.symm ⟨⟨a, P⟩, hmem⟩, ?_, ?_⟩
    · rw [Equiv.apply_symm_apply]
    · rw [Equiv.apply_symm_apply]

/-- **Inverse colouring is proper**: the colouring induced by a bijection
`e : Fin r ≃ labelledPolymers Ω` is proper for the incompatibility graph, since two
equal-coloured indices give distinct polymers of the same vertex-disjoint colour class. -/
theorem invProper {r m : ℕ} {G : SimpleGraph ι} [Fintype G.edgeSet]
    {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ a, IsCompatiblePolymerFamilyVertexDisjoint G (Ω a))
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
    (hΩ ((e i).val.1)).2 (Finset.mem_coe.mpr hmi) (Finset.mem_coe.mpr hmj') hne
  exact (PolymersIncompatible.iff_not_isPolymerVertexDisjoint.mp hadj.2) hvd

/-- **Colour-class fibre cardinality is `r!`**: for a family-tuple `Ω` of vertex-disjoint
compatible families with total polymer count `r`, the pairs `(ω, c)` consisting of a polymer
sequence and a proper colouring whose colour classes are exactly `Ω` number `r!` — they
biject with the orderings `Fin r ≃ labelledPolymers Ω`. -/
theorem card_proper_colorClass_fiber {r m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet]
    {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ a, Ω a ∈ vdCompatiblePolymerFamilies G)
    (hr : r = (labelledPolymers Ω).card) :
    Fintype.card {p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) //
        (∀ i, p.1 i ∈ allPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ a, colorClass p.1 p.2 a = Ω a)} = r.factorial := by
  classical
  have hsub : ∀ a, Ω a ⊆ allPolymers G := fun a => (mem_vdCompatiblePolymerFamilies.mp (hΩ a)).1
  have hvd : ∀ a, IsCompatiblePolymerFamilyVertexDisjoint G (Ω a) :=
    fun a => (mem_vdCompatiblePolymerFamilies.mp (hΩ a)).2
  have E : {p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) //
        (∀ i, p.1 i ∈ allPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ a, colorClass p.1 p.2 a = Ω a)} ≃ (Fin r ≃ ↥(labelledPolymers Ω)) :=
    { toFun := fun q => Equiv.ofBijective (seqColoringForward q.2.2.2)
        ⟨seqColoringForward_injective G q.2.1 q.2.2.1 q.2.2.2,
          seqColoringForward_surjective q.2.2.2⟩
      invFun := fun e => ⟨(fun i => (e i).val.2, fun i => (e i).val.1),
        fun i => hsub _ (mem_labelledPolymers.mp (e i).property), invProper hvd e, invColorClass e⟩
      left_inv := fun q => by apply Subtype.ext; rfl
      right_inv := fun e => by
        apply Equiv.ext; intro i; apply Subtype.ext; rfl }
  rw [Fintype.card_congr E]
  have hcard : Fintype.card (Fin r) = Fintype.card ↥(labelledPolymers Ω) := by
    rw [Fintype.card_fin, Fintype.card_coe, ← hr]
  rw [Fintype.card_equiv (Fintype.equivOfCardEq hcard), Fintype.card_fin]

/-- **Fibre activity sum is `r! · W(Ω)`**: summing the sequence activity over all `(ω, c)`
whose colour classes are `Ω` gives `r!` copies of the family weight `W(Ω) = ∏_a ∏_{P∈Ω a} t^|P|`
(each fibre element has the same activity by `clusterSeqActivity_eq_prod_colorClass`, and there
are `r!` of them by `card_proper_colorClass_fiber`). -/
theorem fiber_sum_clusterSeqActivity {r m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ)
    {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ a, Ω a ∈ vdCompatiblePolymerFamilies G)
    (hr : r = (labelledPolymers Ω).card) :
    ∑ q : {p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) //
        (∀ i, p.1 i ∈ allPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ a, colorClass p.1 p.2 a = Ω a)}, clusterSeqActivity t q.1.1 =
      (r.factorial : ℝ) * ∏ a : Fin m, ∏ P ∈ Ω a, t ^ P.card := by
  classical
  have hconst : ∀ q : {p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) //
        (∀ i, p.1 i ∈ allPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ a, colorClass p.1 p.2 a = Ω a)},
      clusterSeqActivity t q.1.1 = ∏ a : Fin m, ∏ P ∈ Ω a, t ^ P.card := by
    intro q
    rw [clusterSeqActivity_eq_prod_colorClass G t q.2.1 q.2.2.1]
    exact Finset.prod_congr rfl (fun a _ => by rw [q.2.2.2 a])
  rw [Finset.sum_congr rfl (fun q _ => hconst q), Finset.sum_const, Finset.card_univ,
    card_proper_colorClass_fiber G hΩ hr, nsmul_eq_mul]

open Classical in
/-- **Fibre activity sum as a `Finset`-filter sum**: the product-subtype fibre sum
`fiber_sum_clusterSeqActivity` rewritten as a sum over the `Finset` of `(ω, c)` (a product of
a polymer sequence and a colouring) satisfying the fibre predicate.  Bridges the subtype sum
to the `Finset`-filter form consumed by the fibrewise regrouping (`Finset.sum_subtype`). -/
theorem fiber_filter_sum {r m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ)
    {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ a, Ω a ∈ vdCompatiblePolymerFamilies G)
    (hr : r = (labelledPolymers Ω).card) :
    ∑ p ∈ (Finset.univ : Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
        (fun p => (∀ i, p.1 i ∈ allPolymers G) ∧
          IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
          (∀ a, colorClass p.1 p.2 a = Ω a)), clusterSeqActivity t p.1 =
      (r.factorial : ℝ) * ∏ a : Fin m, ∏ P ∈ Ω a, t ^ P.card := by
  classical
  rw [Finset.sum_subtype (Finset.univ.filter
        (fun p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) =>
          (∀ i, p.1 i ∈ allPolymers G) ∧
            IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
            (∀ a, colorClass p.1 p.2 a = Ω a)))
      (p := fun p => (∀ i, p.1 i ∈ allPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ a, colorClass p.1 p.2 a = Ω a))
      (fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      (fun p => clusterSeqActivity t p.1)]
  exact fiber_sum_clusterSeqActivity G t hΩ hr

open Classical in
/-- **Colour-count sum as a product-`Finset` sum**: the activity weighted by the
proper-surjective-colouring count over polymer sequences equals the activity summed over the
`Finset` of `(ω, c)` pairs with `ω` valued in `allPolymers` and `c` a proper surjective
colouring.  Expand the count as `∑_c 1` and reindex the `(ω, c)` double sum as a product. -/
theorem seq_count_eq_product_sum {r m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
          clusterSeqActivity t ω =
      ∑ p ∈ (Finset.univ : Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
          (fun p => (∀ i, p.1 i ∈ allPolymers G) ∧
            IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
            Function.Surjective p.2), clusterSeqActivity t p.1 := by
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
        clusterSeqActivity t ω =
      ∑ _c ∈ properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m,
        clusterSeqActivity t ω := by
    intro ω
    rw [Finset.sum_const, nsmul_eq_mul]
  simp_rw [hcount, hps]
  refine (Finset.sum_finset_product
    (Finset.univ.filter (fun p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) =>
      (∀ i, p.1 i ∈ allPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧ Function.Surjective p.2))
    (Fintype.piFinset (fun _ : Fin r => allPolymers G))
    (fun ω => Finset.univ.filter (fun c : Fin r → Fin m =>
      IsProperColoring (polymerSeqIncompatibilityGraph ω) m c ∧ Function.Surjective c))
    (fun p => ?_) (f := fun p => clusterSeqActivity t p.1)).symm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]

open Classical in
/-- **Colour-count sum regrouped by colour classes** (fixed `r`): the activity-weighted
proper-surjective-colouring count over length-`r` sequences equals, summed over family-tuples
`Ω`, the activity over the fibre of `(ω, c)` with colour classes `Ω`.  Regroup the
product-`Finset` sum (`seq_count_eq_product_sum`) by the colour-class map
(`Finset.sum_fiberwise_of_maps_to`); the surjectivity constraint is implied by each colour
class being nonempty. -/
theorem seq_count_eq_fiberwise {r m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
          clusterSeqActivity t ω =
      ∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdCompatiblePolymerFamilies G).erase ∅),
        ∑ p ∈ (Finset.univ : Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
            (fun p => (∀ i, p.1 i ∈ allPolymers G) ∧
              IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
              (∀ a, colorClass p.1 p.2 a = Ω a)), clusterSeqActivity t p.1 := by
  classical
  rw [seq_count_eq_product_sum]
  have hmaps : ∀ p ∈ (Finset.univ : Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
      (fun p => (∀ i, p.1 i ∈ allPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧ Function.Surjective p.2),
      (fun a => colorClass p.1 p.2 a) ∈
        Fintype.piFinset (fun _ : Fin m => (vdCompatiblePolymerFamilies G).erase ∅) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [Fintype.mem_piFinset]
    exact fun a => colorClass_mem_vdCompatiblePolymerFamilies G hp.1 hp.2.1 hp.2.2 a
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => clusterSeqActivity t p.1)]
  refine Finset.sum_congr rfl (fun Ω hΩ => ?_)
  rw [Fintype.mem_piFinset] at hΩ
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff]
  constructor
  · rintro ⟨⟨hap, hpr, _⟩, hcol⟩; exact ⟨hap, hpr, hcol⟩
  · rintro ⟨hap, hpr, hcol⟩
    refine ⟨⟨hap, hpr, fun a => ?_⟩, hcol⟩
    obtain ⟨P, hPmem⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp (hΩ a)).1
    rw [← hcol a] at hPmem
    obtain ⟨i, hci, _⟩ := mem_colorClass.mp hPmem
    exact ⟨i, hci⟩

open Classical in
/-- **Inner fibre sum evaluated**: for a family-tuple `Ω` of nonempty vertex-disjoint
compatible families, the activity over the `(ω, c)` fibre with colour classes `Ω` is
`r!·∏_a∏_{P∈Ω a} t^|P|` when the total polymer count of `Ω` is `r`, and `0` otherwise (the
fibre is empty, as any such `(ω, c)` would force `(labelledPolymers Ω).card = r`). -/
theorem fiber_filter_sum_eval {r m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ)
    {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ a, Ω a ∈ (vdCompatiblePolymerFamilies G).erase ∅) :
    ∑ p ∈ (Finset.univ : Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
        (fun p => (∀ i, p.1 i ∈ allPolymers G) ∧
          IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
          (∀ a, colorClass p.1 p.2 a = Ω a)), clusterSeqActivity t p.1 =
      if (labelledPolymers Ω).card = r then
        (r.factorial : ℝ) * ∏ a : Fin m, ∏ P ∈ Ω a, t ^ P.card else 0 := by
  classical
  have hΩ' : ∀ a, Ω a ∈ vdCompatiblePolymerFamilies G :=
    fun a => (Finset.mem_erase.mp (hΩ a)).2
  by_cases hcard : (labelledPolymers Ω).card = r
  · rw [if_pos hcard]
    exact fiber_filter_sum G t hΩ' hcard.symm
  · rw [if_neg hcard]
    refine Finset.sum_eq_zero (fun p hp => ?_)
    exfalso
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hap, hpr, hcol⟩ := hp
    apply hcard
    have e : Fin r ≃ ↥(labelledPolymers Ω) :=
      Equiv.ofBijective (seqColoringForward hcol)
        ⟨seqColoringForward_injective G hap hpr hcol, seqColoringForward_surjective hcol⟩
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin, Fintype.card_coe] at hc
    exact hc.symm

open Classical in
/-- **Family-tuple sum as a polymer-sequence colouring sum** (per-`m` Mayer–Montroll identity):
the family-tuple weight sum equals the activity-weighted proper-surjective-colouring count over
polymer sequences of all lengths, normalised by `1/r!`.  Each family-tuple `Ω` is recovered `r!`
times (one per ordering of its labelled polymers), so the `1/r!` cancels and exactly `W(Ω)`
survives. -/
theorem vdFamilyTuple_sum_eq_seq_coloring_sum {m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet]
    (t : ℝ) :
    (∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdCompatiblePolymerFamilies G).erase ∅),
        ∏ i : Fin m, ∏ P ∈ Ω i, t ^ P.card) =
      ∑ r ∈ Finset.range (m * (allPolymers G).card + 1),
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) /
            (r.factorial : ℝ) * clusterSeqActivity t ω := by
  classical
  have hr : ∀ r : ℕ,
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) /
            (r.factorial : ℝ) * clusterSeqActivity t ω =
      ∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdCompatiblePolymerFamilies G).erase ∅),
        (if (labelledPolymers Ω).card = r then ∏ a : Fin m, ∏ P ∈ Ω a, t ^ P.card else 0) := by
    intro r
    have key : ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
          clusterSeqActivity t ω =
        ∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdCompatiblePolymerFamilies G).erase ∅),
          (if (labelledPolymers Ω).card = r then
            (r.factorial : ℝ) * ∏ a : Fin m, ∏ P ∈ Ω a, t ^ P.card else 0) := by
      rw [seq_count_eq_fiberwise]
      refine Finset.sum_congr rfl (fun Ω hΩ => ?_)
      rw [Fintype.mem_piFinset] at hΩ
      exact fiber_filter_sum_eval G t hΩ
    rw [show (∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) /
            (r.factorial : ℝ) * clusterSeqActivity t ω) =
        (∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
            clusterSeqActivity t ω) / (r.factorial : ℝ) from by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun ω _ => by ring), key, Finset.sum_div]
    refine Finset.sum_congr rfl (fun Ω _ => ?_)
    split_ifs with h
    · rw [mul_div_cancel_left₀ _ (by positivity : (r.factorial : ℝ) ≠ 0)]
    · rw [zero_div]
  simp_rw [hr]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun Ω hΩ => ?_)
  rw [Fintype.mem_piFinset] at hΩ
  have hsub : ∀ a, Ω a ⊆ allPolymers G :=
    fun a => (mem_vdCompatiblePolymerFamilies.mp (Finset.mem_erase.mp (hΩ a)).2).1
  have hlt : (labelledPolymers Ω).card < m * (allPolymers G).card + 1 := by
    rw [card_labelledPolymers]
    calc ∑ a : Fin m, (Ω a).card
        ≤ ∑ _a : Fin m, (allPolymers G).card :=
          Finset.sum_le_sum (fun a _ => Finset.card_le_card (hsub a))
      _ = m * (allPolymers G).card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ < m * (allPolymers G).card + 1 := Nat.lt_succ_self _
  rw [Finset.sum_eq_single_of_mem ((labelledPolymers Ω).card) (Finset.mem_range.mpr hlt)
      (fun r _ hr => if_neg (fun h => hr h.symm)), if_pos rfl]

/-- **No proper surjective colouring of an over-long sequence**: for `ω` valued in
`allPolymers G`, if the sequence length `r` exceeds `m·|allPolymers G|` then there is no
proper surjective `m`-colouring of its incompatibility graph (the `m` colour classes each lie
in `allPolymers`, of total size `r ≤ m·|allPolymers|`). -/
theorem properSurjectiveColorings_empty_of_card_lt {r m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] {ω : Fin r → Finset (Sym2 ι)} (hω : ∀ i, ω i ∈ allPolymers G)
    (hr : m * (allPolymers G).card < r) :
    properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c hc
  obtain ⟨hproper, hsurj⟩ := (mem_properSurjectiveColorings _).mp hc
  have e : Fin r ≃ ↥(labelledPolymers (colorClass ω c)) :=
    Equiv.ofBijective (seqColoringForward (fun a => rfl))
      ⟨seqColoringForward_injective G hω hproper (fun a => rfl),
        seqColoringForward_surjective (fun a => rfl)⟩
  have hcard : r = ∑ a : Fin m, (colorClass ω c a).card := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin, Fintype.card_coe, card_labelledPolymers] at hc
    exact hc
  have hsub : ∀ a, colorClass ω c a ⊆ allPolymers G := by
    intro a P hP
    obtain ⟨i, _, rfl⟩ := mem_colorClass.mp hP
    exact hω i
  have hle : (∑ a : Fin m, (colorClass ω c a).card) ≤ m * (allPolymers G).card := by
    calc ∑ a : Fin m, (colorClass ω c a).card
        ≤ ∑ _a : Fin m, (allPolymers G).card :=
          Finset.sum_le_sum (fun a _ => Finset.card_le_card (hsub a))
      _ = m * (allPolymers G).card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- **Mayer term as a colour-degree double sum**: distributing the colour-degree sum out of the
sequence sum, the `r`-th Mayer term is
`∑_{k=1}^r (-1)^(k-1)/k · ∑_ω #properSurjectiveColorings(G(ω),k)/r! · clusterSeqActivity`.
The inner sum is the per-`(r,k)` colouring contribution feeding the capstone Fubini swap. -/
theorem mayerExpansionTerm_eq_double_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (r : ℕ) (t : ℝ) :
    mayerExpansionTerm G r t =
      ∑ k ∈ Finset.Icc 1 r, ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
            (r.factorial : ℝ) * clusterSeqActivity t ω := by
  rw [mayerExpansionTerm_eq_coloring_form]
  simp_rw [Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

/-- **Log-Taylor term as a colouring sum**: combining the log-Taylor expansion
(`logTaylor_eps_term_eq_sum_vdFamilyTuples`, family-tuple form) with the per-`m` identity
(`vdFamilyTuple_sum_eq_seq_coloring_sum`, `m = n+1`), the `n`-th log-Taylor term equals the
`m=n+1` colouring contribution summed over sequence lengths `r ≤ (n+1)·|allPolymers G|`. -/
theorem logTaylor_term_eq_coloring {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n *
        (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅, ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
        (n + 1) =
      ∑ r ∈ Finset.range ((n + 1) * (allPolymers G).card + 1),
        ((-1 : ℝ) ^ n / (n + 1)) *
          ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
            ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) (n + 1)).card : ℝ) /
              (r.factorial : ℝ) * clusterSeqActivity t ω := by
  rw [logTaylor_eps_term_eq_sum_vdFamilyTuples, ← Finset.mul_sum,
    vdFamilyTuple_sum_eq_seq_coloring_sum, Finset.mul_sum]

/-- **Proper surjective colourings are bounded by all colourings**: at most `k^r` proper
surjective `k`-colourings of a graph on `Fin r` (they are a subset of all functions
`Fin r → Fin k`).  Used for the double-summability majorant in the capstone. -/
theorem card_properSurjectiveColorings_le {r : ℕ} (H : SimpleGraph (Fin r)) [DecidableRel H.Adj]
    (k : ℕ) : (properSurjectiveColorings H k).card ≤ k ^ r := by
  classical
  calc (properSurjectiveColorings H k).card
      ≤ (Finset.univ : Finset (Fin r → Fin k)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = k ^ r := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **Per-`(r,k)` colour-degree term bound**: the absolute value of the `(r,k)` colour-degree
contribution is bounded by `(k^(r-1)/r!)·A^r`, where `A = ∑_{P∈allPolymers G} |t|^|P|`.  Combines
`card_properSurjectiveColorings_le` (`#colourings ≤ k^r`) and `sum_clusterSeqActivity_abs_piFinset`
(`∑_ω |activity| = A^r`).  The brick of the capstone double-summability majorant. -/
theorem abs_colorDegreeTerm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (t : ℝ) (r k : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    |((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
            (r.factorial : ℝ) * clusterSeqActivity t ω| ≤
      ((k : ℝ) ^ (r - 1) / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
  classical
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hkpos, one_div]
  have hsum : |∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
          (r.factorial : ℝ) * clusterSeqActivity t ω| ≤
      ((k : ℝ) ^ r / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
    calc |∑ ω ∈ _, _| ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
            |((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
              (r.factorial : ℝ) * clusterSeqActivity t ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
            ((k : ℝ) ^ r / (r.factorial : ℝ)) * |clusterSeqActivity t ω| := by
          refine Finset.sum_le_sum (fun ω _ => ?_)
          rw [abs_mul, abs_div, Nat.abs_cast, Nat.abs_cast]
          gcongr
          exact_mod_cast card_properSurjectiveColorings_le (polymerSeqIncompatibilityGraph ω) k
      _ = ((k : ℝ) ^ r / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
          rw [← Finset.mul_sum, sum_clusterSeqActivity_abs_piFinset]
  have hkr : (k : ℝ)⁻¹ * (k : ℝ) ^ r = (k : ℝ) ^ (r - 1) := by
    have h1 : (k : ℝ) ^ r = (k : ℝ) * (k : ℝ) ^ (r - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hr]
    rw [h1, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hkpos), one_mul]
  calc (k : ℝ)⁻¹ * |∑ ω ∈ _, _|
      ≤ (k : ℝ)⁻¹ *
          (((k : ℝ) ^ r / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r) := by
        gcongr
    _ = ((k : ℝ) ^ (r - 1) / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
        rw [← mul_assoc, ← mul_div_assoc, hkr]

/-- **Colour-degree row bound**: `∑_{k=1}^r |C(r,k)| ≤ (r^r/r!)·A^r`, the per-row majorant
of the capstone double sum, summing `abs_colorDegreeTerm_le` over `k ∈ Icc 1 r` (each
`k^(r-1) ≤ r^(r-1)`, and `Icc 1 r` has `r` elements so `r·r^(r-1) = r^r`). -/
theorem sum_abs_colorDegreeTerm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (t : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ Finset.Icc 1 r, |((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
            (r.factorial : ℝ) * clusterSeqActivity t ω| ≤
      ((r : ℝ) ^ r / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
  calc ∑ k ∈ Finset.Icc 1 r, |((-1 : ℝ) ^ (k - 1) / (k : ℝ)) * _|
      ≤ ∑ k ∈ Finset.Icc 1 r,
          ((r : ℝ) ^ (r - 1) / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_Icc] at hk
        refine (abs_colorDegreeTerm_le G t r k hk.1 hr).trans ?_
        gcongr
        exact_mod_cast hk.2
    _ = ((r : ℝ) ^ r / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        have hrr : (r : ℝ) * (r : ℝ) ^ (r - 1) = (r : ℝ) ^ r := by
          rw [← pow_succ', Nat.sub_add_cancel hr]
        rw [← mul_assoc, ← mul_div_assoc, hrr]

/-- **Summable self-power factorial majorant**: `∑_r (r^r/r!)·|A|^r` converges for `e·|A| < 1`
(ratio test: the ratio `(1+1/(r+1))^(r+1)·|A| → e·|A| < 1`, bounded via `Real.add_one_le_exp`).
The row-majorant series for the capstone double-summability. -/
theorem summable_pow_self_div_factorial_mul_abs_pow (A : ℝ) (hA : Real.exp 1 * |A| < 1) :
    Summable fun r : ℕ => ((r : ℝ) ^ r / (r.factorial : ℝ)) * |A| ^ r := by
  refine summable_of_ratio_norm_eventually_le hA ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hnnA : (0 : ℝ) ≤ ((↑(m + 1) : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ)) * |A| ^ (m + 1) := by
    positivity
  have hnnB : (0 : ℝ) ≤
      ((↑(m + 1 + 1) : ℝ) ^ (m + 1 + 1) / ((m + 1 + 1).factorial : ℝ)) * |A| ^ (m + 1 + 1) := by
    positivity
  rw [Real.norm_of_nonneg hnnB, Real.norm_of_nonneg hnnA]
  have hratio : (↑(m + 1 + 1) : ℝ) / (↑(m + 1) : ℝ) = 1 + 1 / (↑(m + 1) : ℝ) := by
    push_cast; field_simp
  have hle : (1 + 1 / (↑(m + 1) : ℝ)) ^ (m + 1) ≤ Real.exp 1 := by
    calc (1 + 1 / (↑(m + 1) : ℝ)) ^ (m + 1)
        ≤ (Real.exp (1 / (↑(m + 1) : ℝ))) ^ (m + 1) := by
          gcongr
          rw [add_comm]
          exact Real.add_one_le_exp _
      _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  have hkey : (↑(m + 1 + 1) : ℝ) ^ (m + 1) ≤ Real.exp 1 * (↑(m + 1) : ℝ) ^ (m + 1) := by
    have h := mul_le_mul_of_nonneg_right hle
      (by positivity : (0 : ℝ) ≤ (↑(m + 1) : ℝ) ^ (m + 1))
    rwa [← mul_pow,
      show (1 + 1 / (↑(m + 1) : ℝ)) * (↑(m + 1) : ℝ) = (↑(m + 1 + 1) : ℝ) from by
        push_cast; field_simp] at h
  have e_fac : ((m + 1 + 1).factorial : ℝ) = (↑(m + 1 + 1) : ℝ) * ((m + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ (m + 1), Nat.cast_mul]
  have e_pow : (↑(m + 1 + 1) : ℝ) ^ (m + 1 + 1) =
      (↑(m + 1 + 1) : ℝ) * (↑(m + 1 + 1) : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
  have e_R : |A| ^ (m + 1 + 1) = |A| ^ (m + 1) * |A| := by rw [pow_succ]
  rw [e_fac, e_pow, e_R, mul_div_mul_left _ _ (by positivity : (↑(m + 1 + 1) : ℝ) ≠ 0)]
  calc (↑(m + 1 + 1) : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ) * (|A| ^ (m + 1) * |A|)
      = (↑(m + 1 + 1) : ℝ) ^ (m + 1) *
          (|A| ^ (m + 1) * |A| / ((m + 1).factorial : ℝ)) := by ring
    _ ≤ (Real.exp 1 * (↑(m + 1) : ℝ) ^ (m + 1)) *
          (|A| ^ (m + 1) * |A| / ((m + 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = Real.exp 1 * |A| *
          ((↑(m + 1) : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ) * |A| ^ (m + 1)) := by ring

/-- **Colour-degree term** `C(r,k)`: the `(r,k)` contribution of the Mayer expansion,
`(-1)^(k-1)/k · ∑_ω #properSurjectiveColorings(G(ω),k)/r! · clusterSeqActivity`.  Summing over
`k ∈ Icc 1 r` gives `mayerExpansionTerm G r t`; over `r ≤ k·N` gives the `k`-th log-Taylor term. -/
noncomputable def colorDegreeTerm {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (t : ℝ) (r k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
      ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
        (r.factorial : ℝ) * clusterSeqActivity t ω

/-- **`colorDegreeTerm` vanishes for `k > r`**: no surjective `k`-colouring of `Fin r` when
`r < k`, so every colour count is `0`. -/
theorem colorDegreeTerm_eq_zero_of_lt {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (t : ℝ) {r k : ℕ} (hrk : r < k) : colorDegreeTerm G t r k = 0 := by
  rw [colorDegreeTerm]
  refine mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun ω _ => ?_)))
  rw [properSurjectiveColorings_eq_empty_of_card_lt _ hrk, Finset.card_empty, Nat.cast_zero,
    zero_div, zero_mul]

/-- **`colorDegreeTerm` vanishes at `k = 0`**: the `1/k` factor is `1/0 = 0`. -/
theorem colorDegreeTerm_zero_right {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (t : ℝ) (r : ℕ) : colorDegreeTerm G t r 0 = 0 := by
  rw [colorDegreeTerm, Nat.cast_zero, div_zero, zero_mul]

/-- **Row absolute sum bound**: `∑'_k |colorDegreeTerm G t r k| ≤ (r^r/r!)·A^r`.  Each row is
finitely supported (`colorDegreeTerm = 0` for `k > r` and `k = 0`), so the tsum reduces to the
finite `Icc 1 r` sum bounded by `sum_abs_colorDegreeTerm_le`. -/
theorem tsum_abs_colorDegreeTerm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (t : ℝ) (r : ℕ) :
    ∑' k, |colorDegreeTerm G t r k| ≤
      ((r : ℝ) ^ r / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
  classical
  rw [tsum_eq_sum (s := Finset.range (r + 1)) (fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    rw [colorDegreeTerm_eq_zero_of_lt G t (by omega : r < k), abs_zero])]
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · subst hr0
    simp [colorDegreeTerm_zero_right]
  · rw [show Finset.range (r + 1) = insert 0 (Finset.Icc 1 r) from by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
      Finset.sum_insert (by simp), colorDegreeTerm_zero_right, abs_zero, zero_add]
    exact sum_abs_colorDegreeTerm_le G t r hr1

/-- **Double summability of the colour-degree term**: `(r,k) ↦ colorDegreeTerm G t r k` is
summable over `ℕ × ℕ` whenever `e·A < 1` (`A = ∑_{P} |t|^|P|`).  Via `summable_abs_iff` and
`summable_prod_of_nonneg`: each row is finitely supported, and the row absolute sums are
majorised by the summable `(r^r/r!)·A^r`.  Enables the capstone `tsum_comm`. -/
theorem summable_uncurry_colorDegreeTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ)
    (hact : Real.exp 1 * (∑ P ∈ allPolymers G, |t| ^ P.card) < 1) :
    Summable (fun p : ℕ × ℕ => colorDegreeTerm G t p.1 p.2) := by
  classical
  have hsumnn : (0 : ℝ) ≤ ∑ P ∈ allPolymers G, |t| ^ P.card :=
    Finset.sum_nonneg (fun P _ => by positivity)
  have hAabs : Real.exp 1 * |∑ P ∈ allPolymers G, |t| ^ P.card| < 1 := by
    rwa [abs_of_nonneg hsumnn]
  rw [← summable_abs_iff, summable_prod_of_nonneg (fun p => abs_nonneg _)]
  refine ⟨fun r => ?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := Finset.range (r + 1)) (fun k hk => ?_)
    rw [Finset.mem_range, not_lt] at hk
    rw [colorDegreeTerm_eq_zero_of_lt G t (by omega : r < k), abs_zero]
  · refine Summable.of_nonneg_of_le (fun r => tsum_nonneg (fun k => abs_nonneg _))
      (fun r => tsum_abs_colorDegreeTerm_le G t r) ?_
    have hpow : ∀ r : ℕ, ((r : ℝ) ^ r / (r.factorial : ℝ)) *
        (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r =
        ((r : ℝ) ^ r / (r.factorial : ℝ)) * |∑ P ∈ allPolymers G, |t| ^ P.card| ^ r := by
      intro r; rw [abs_of_nonneg hsumnn]
    simp_rw [hpow]
    exact summable_pow_self_div_factorial_mul_abs_pow _ hAabs

/-- **`colorDegreeTerm` vanishes when `m·|allPolymers G| < r`**: no surjective `m`-colouring of a
graph on `Fin r` whose incompatibility structure comes from `r` polymers can use more than
`m·|allPolymers G|` labels, so for `m·N < r` every colour count is `0`
(`properSurjectiveColorings_empty_of_card_lt` per `ω`).  Provides the eventual vanishing in `r`
that turns the finite log-Taylor colouring sum into a `tsum`. -/
theorem colorDegreeTerm_eq_zero_of_card_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) {r m : ℕ}
    (hr : m * (allPolymers G).card < r) : colorDegreeTerm G t r m = 0 := by
  classical
  rw [colorDegreeTerm]
  refine mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun ω hω => ?_)))
  have hω' : ∀ i, ω i ∈ allPolymers G := fun i => Fintype.mem_piFinset.mp hω i
  rw [properSurjectiveColorings_empty_of_card_lt G hω' hr, Finset.card_empty,
    Nat.cast_zero, zero_div, zero_mul]

/-- **Mayer term as the `tsum` of its colour-degree row**: `mayerExpansionTerm G r t =
∑'_k colorDegreeTerm G t r k`.  The colour-degree row is finitely supported (`Icc 1 r`), so the
`tsum` collapses to the finite double sum of `mayerExpansionTerm_eq_double_sum`. -/
theorem mayerExpansionTerm_eq_tsum_colorDegreeTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (r : ℕ) (t : ℝ) :
    mayerExpansionTerm G r t = ∑' k, colorDegreeTerm G t r k := by
  classical
  rw [mayerExpansionTerm_eq_double_sum,
    tsum_eq_sum (s := Finset.Icc 1 r) (fun k hk => by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le, Nat.lt_one_iff] at hk
      rcases hk with hk0 | hkr
      · rw [hk0, colorDegreeTerm_zero_right]
      · exact colorDegreeTerm_eq_zero_of_lt G t hkr)]
  rfl

/-- **Log-Taylor term as the `tsum` of its colour-degree column**: the `n`-th log-Taylor term equals
`∑'_r colorDegreeTerm G t r (n+1)`.  The colour-degree column is finitely supported
(`r ≤ (n+1)·|allPolymers G|`, by `colorDegreeTerm_eq_zero_of_card_lt`), so the `tsum` collapses to
the finite range sum of `logTaylor_term_eq_coloring`. -/
theorem logTaylorTerm_eq_tsum_colorDegreeTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n *
        (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅, ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
        (n + 1) =
      ∑' r, colorDegreeTerm G t r (n + 1) := by
  classical
  rw [logTaylor_term_eq_coloring,
    tsum_eq_sum (s := Finset.range ((n + 1) * (allPolymers G).card + 1)) (fun r hr => by
      rw [Finset.mem_range, not_lt] at hr
      exact colorDegreeTerm_eq_zero_of_card_lt G t
        (by omega : (n + 1) * (allPolymers G).card < r))]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [colorDegreeTerm, Nat.add_sub_cancel]
  push_cast
  ring

/-- **Mayer–Montroll identity (general `t`)**: in the convergence regime, the polymer free energy
equals the sum of the Mayer expansion terms,
`polymerFreeEnergy G t = ∑'_n mayerExpansionTerm G n t` (GJ §18.4).

Proof (Fubini swap of the colour-degree double sum).  The analytic side
`polymerFreeEnergy_hasSum_via_log` gives `polymerFreeEnergy = ∑'_n logTaylorTerm n`, and each
`logTaylorTerm n = ∑'_r colorDegreeTerm G t r (n+1)` (column), while
`mayerExpansionTerm G r t = ∑'_k colorDegreeTerm G t r k` (row).  Double-summability
(`summable_uncurry_colorDegreeTerm`, valid for `e·A < 1`) licenses `tsum_comm`; the `k = 0` column
vanishes, giving the `n ↔ n+1` shift between the log-Taylor and Mayer indexings.

The two hypotheses are the genuine analytic convergence conditions: `h_abs` (`|ε(t)| < 1`) for the
`log(1+ε)` series, and `hact` (`e·A < 1`, `A = ∑_P |t|^|P|`) for the double-sum Fubini swap; both
hold in the Kotecký–Preiss / high-temperature regime. -/
theorem mayer_identity_general_t {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ}
    (h_abs : |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅, ∏ P ∈ Γ, t ^ P.card| < 1)
    (hact : Real.exp 1 * (∑ P ∈ allPolymers G, |t| ^ P.card) < 1) :
    polymerFreeEnergy G t = ∑' n, mayerExpansionTerm G n t := by
  classical
  have hsum : Summable (Function.uncurry fun r k => colorDegreeTerm G t r k) :=
    summable_uncurry_colorDegreeTerm G t hact
  have hlog := polymerFreeEnergy_hasSum_via_log G h_abs
  have hg : Summable (fun k => ∑' r, colorDegreeTerm G t r k) := hsum.prod_symm.prod
  have hg0 : (∑' r, colorDegreeTerm G t r 0) = 0 := by
    simp_rw [colorDegreeTerm_zero_right]; exact tsum_zero
  -- shift the `k`-index: the `k = 0` colour column vanishes, so the log-Taylor `n`-sum
  -- (indexed by `n+1`) equals the full `k`-sum.
  have hshift : ∑' n, ∑' r, colorDegreeTerm G t r (n + 1) =
      ∑' k, ∑' r, colorDegreeTerm G t r k := by
    rw [hg.tsum_eq_zero_add]; simp only [hg0, zero_add]
  -- Fubini swap of the colour-degree double sum (licensed by double-summability).
  have hcomm : ∑' k, ∑' r, colorDegreeTerm G t r k =
      ∑' r, ∑' k, colorDegreeTerm G t r k := hsum.tsum_comm
  calc polymerFreeEnergy G t
      = ∑' n, ∑' r, colorDegreeTerm G t r (n + 1) := by
        rw [← hlog.tsum_eq]
        exact tsum_congr (fun n => logTaylorTerm_eq_tsum_colorDegreeTerm G t n)
    _ = ∑' k, ∑' r, colorDegreeTerm G t r k := hshift
    _ = ∑' r, ∑' k, colorDegreeTerm G t r k := hcomm
    _ = ∑' r, mayerExpansionTerm G r t :=
        tsum_congr (fun r => (mayerExpansionTerm_eq_tsum_colorDegreeTerm G r t).symm)

/-- **Mayer–Montroll identity, eventual form near `t = 0`**: for `t` in some neighbourhood of `0`,
`polymerFreeEnergy G t = ∑'_n mayerExpansionTerm G n t` (GJ §18.4).

Both convergence hypotheses of `mayer_identity_general_t` hold near `0`: `|ε(t)| < 1` since
`ε(t) → 0` (`vdPolymerFamilies_sum_minus_one_tendsto_zero`), and `e·A(t) < 1` since
`A(t) = ∑_P |t|^|P| → 0` (every polymer is nonempty, so `A(0) = 0` and `A` is continuous). -/
theorem mayer_identity_general_t_eventually {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      polymerFreeEnergy G t = ∑' n, mayerExpansionTerm G n t := by
  classical
  -- `|ε(t)| < 1` eventually.
  have h_abs_tendsto : Filter.Tendsto (fun t : ℝ =>
      |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅, ∏ P ∈ Γ, t ^ P.card|)
      (nhds 0) (nhds 0) := by
    simpa using (continuous_abs.tendsto 0).comp
      (vdPolymerFamilies_sum_minus_one_tendsto_zero G)
  have h_abs_ev : ∀ᶠ t : ℝ in nhds 0,
      |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅, ∏ P ∈ Γ, t ^ P.card| < 1 :=
    h_abs_tendsto.eventually_lt_const zero_lt_one
  -- `e·A(t) < 1` eventually, where `A(t) = ∑_P |t|^|P|`.
  have hcont : Continuous
      (fun t : ℝ => Real.exp 1 * ∑ P ∈ allPolymers G, |t| ^ P.card) :=
    continuous_const.mul (continuous_finset_sum _ (fun P _ => continuous_abs.pow P.card))
  have hA0 : Real.exp 1 * ∑ P ∈ allPolymers G, |(0 : ℝ)| ^ P.card = 0 :=
    mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun P hP => by
      rw [abs_zero, zero_pow (Finset.card_ne_zero.mpr (mem_allPolymers.mp hP).nonempty)])))
  have hA : Filter.Tendsto
      (fun t : ℝ => Real.exp 1 * ∑ P ∈ allPolymers G, |t| ^ P.card) (nhds 0) (nhds 0) := by
    have h := hcont.tendsto 0
    rwa [hA0] at h
  have hact_ev : ∀ᶠ t : ℝ in nhds 0,
      Real.exp 1 * (∑ P ∈ allPolymers G, |t| ^ P.card) < 1 :=
    hA.eventually_lt_const zero_lt_one
  exact (h_abs_ev.and hact_ev).mono
    (fun t ht => mayer_identity_general_t G ht.1 ht.2)

end IsingModel
