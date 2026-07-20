import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.ClusterExpansion.Families.EvenSubgraphs
import IsingModel.ClusterExpansion.Families.VertexDisjoint
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ProperColorings
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre.FibreBijection

/-!
# The `r!`-to-one colour-class fibre (2/5): the filtered-`Finset` fibre sums

Structural split (2/5) of
`IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre`.
This child holds the `Finset`-filter reformulations: the fibre sum as a filtered
product-`Finset` sum, the colour-count sum as a product-`Finset` sum, its regrouping by
colour classes, and the evaluated inner fibre sum (`r!·W(Ω)` or `0`).  See the
`IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre` facade module for the
full contents overview.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

end IsingModel
