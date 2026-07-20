import IsingModel.ClusterExpansion.Basic
import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.ClusterExpansion.Families.Predicates
import IsingModel.ClusterExpansion.Families.EvenSubgraphs
import IsingModel.ClusterExpansion.Families.VertexDisjoint
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ProperColorings
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.EdgeInclusionExclusion

/-!
# The `r!`-to-one colour-class fibre (1/5): the labelled-polymer bijection

Structural split (1/5) of
`IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre`.
This child holds the labelled-polymer set `labelledPolymers` and its cardinality, the forward
map `(ω, c) ↦ (i ↦ ⟨c i, ω i⟩)` with well-definedness, injectivity and surjectivity, the
inverse direction (`invColorClass`, `invProper`), the fibre cardinality
`card_proper_colorClass_fiber = r!` and the fibre activity sum `r! · W(Ω)`.  See the
`IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre` facade module for the
full contents overview.
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

end IsingModel
