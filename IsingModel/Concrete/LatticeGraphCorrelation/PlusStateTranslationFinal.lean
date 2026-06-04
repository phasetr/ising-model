import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateTranslationCapstone
import IsingModel.Concrete.CubicBoxAdjacencyGeometry

/-!
# Screening the translated ambient back to the cubic exhaustion (Issue #3581 PR 4c)

The recentered middle term of the translation squeeze
(`gibbsExpectationBC_translatedInner_recenter`) lives on the *translated* ambient
`vaddFinset (-a) (cubicBox d M)`.  This file uses the general-ambient screening
(`gibbsExpectationBC_extendGraph_screening`) to bring it back onto the cubic
exhaustion: the `+` expectation of `O` with the centered inner region `cubicBox d n`
on the translated ambient equals the natural cubic `plusBoxLocalExpectation`.

* `innerOf_eq_plusBoxInterior_map` — the centered inner region is the lifted cubic
  inner region.
* `hsep_translated` — the shell-separation hypothesis (a `cubicBox d n` site's
  neighbours lie in `cubicBox d (n+1)`).
* `gibbsExpectationBC_innerOf_translated_eq_plusBoxLocal` — the screening identity.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17, pp. 100–104.
-/

namespace IsingModel

namespace Ambient

open Finset

variable {d : ℕ}

/-- **The centered inner region is the lifted cubic inner region**: for
`cubicBox d (n+1) ⊆ Ω`, `innerOf Ω (cubicBox d n)` is the image of
`plusBoxInterior d n (n+1)` under the inclusion `↑(cubicBox d (n+1)) ↪ ↑Ω`. -/
theorem innerOf_eq_plusBoxInterior_map {n : ℕ} {Ω : Finset (Fin d → ℤ)}
    (h12 : cubicBox d (n + 1) ⊆ Ω) :
    innerOf Ω (cubicBox d n) = (plusBoxInterior d n (n + 1)).map (subtypeInclEmb h12) := by
  ext u
  simp only [innerOf, plusBoxInterior, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map, subtypeInclEmb, Function.Embedding.coeFn_mk]
  constructor
  · intro hu
    exact ⟨⟨u.val, cubicBox_mono d (Nat.le_succ n) hu⟩, hu, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact hk

/-- **Shell separation for the translated screening**: every extra edge (in the
induced graph on `Ω` but not the `cubicBox d (n+1)`-extension) has both endpoints
outside the centered inner region, because a `cubicBox d n` site's neighbours lie
inside `cubicBox d (n+1)` (`cubicBox_adj_mem_succ`). -/
theorem hsep_translated {n : ℕ} {Ω : Finset (Fin d → ℤ)} (h12 : cubicBox d (n + 1) ⊆ Ω)
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Ω).edgeSet]
    [Fintype (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d (n + 1)) Ω).edgeSet]
    (e : Sym2 (↑Ω : Type _))
    (he : e ∈ (inducedGraph (IsingModel.latticeGraph d) Ω).edgeFinset \
        (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d (n + 1)) Ω).edgeFinset)
    (u : (↑Ω : Type _)) (hu : u ∈ e) :
    u ∉ (plusBoxInterior d n (n + 1)).map (subtypeInclEmb h12) := by
  rw [← innerOf_eq_plusBoxInterior_map h12]
  simp only [innerOf, Finset.mem_filter, Finset.mem_univ, true_and]
  intro huI
  rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset] at he
  obtain ⟨hind, hnotext⟩ := he
  revert hu hind hnotext
  refine Sym2.ind (fun x y => ?_) e
  intro hmem hind hnotext
  rw [SimpleGraph.mem_edgeSet] at hind
  apply hnotext
  rw [SimpleGraph.mem_edgeSet]
  have hadj : (IsingModel.latticeGraph d).Adj x.val y.val := hind
  rcases Sym2.mem_iff.mp hmem with rfl | rfl
  · exact ⟨cubicBox_mono d (Nat.le_succ n) huI, cubicBox_adj_mem_succ huI hadj, hadj⟩
  · exact ⟨cubicBox_adj_mem_succ huI hadj.symm, cubicBox_mono d (Nat.le_succ n) huI, hadj⟩

/-- **Geometric inclusion**: the box `cubicBox d (n+1)` sits inside the translate (by
`-a`) of the box grown by `latticeRadius a` (`cubicBox_subset_vaddFinset`,
`latticeRadius_neg`). -/
theorem cubicBox_succ_subset_vaddFinset_neg (a : Fin d → ℤ) (n : ℕ) :
    cubicBox d (n + 1) ⊆ vaddFinset (-a) (cubicBox d (n + 1 + latticeRadius a)) := by
  have h := cubicBox_subset_vaddFinset (-a) (n + 1)
  rwa [latticeRadius_neg] at h

/-- **The recentered middle term equals the cubic `+` local expectation**: applying
the general-ambient screening (`gibbsExpectationBC_extendGraph_screening`) with the
shell separation `hsep_translated`, the `+` expectation of `O` with the centered
inner region on the translated ambient equals the natural cubic
`plusBoxLocalExpectation`. -/
theorem gibbsExpectationBC_innerOf_translated_eq_plusBoxLocal (a : Fin d → ℤ) {n : ℕ}
    {J h β : ℝ} (O : LocalMonotoneObservable d)
    (h12 : cubicBox d (n + 1) ⊆ vaddFinset (-a) (cubicBox d (n + 1 + latticeRadius a)))
    (hSn1 : O.S ⊆ cubicBox d (n + 1)) :
    gibbsExpectationBC
        (inducedGraph (IsingModel.latticeGraph d)
          (vaddFinset (-a) (cubicBox d (n + 1 + latticeRadius a))))
        β (fun _ => J) h
        (innerOf (vaddFinset (-a) (cubicBox d (n + 1 + latticeRadius a))) (cubicBox d n))
        (plusConfig _) (O.lift (hSn1.trans h12))
      = plusBoxLocalExpectation n (n + 1) J h β O hSn1 := by
  haveI : Fintype (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d (n + 1))
    (vaddFinset (-a) (cubicBox d (n + 1 + latticeRadius a)))).edgeSet := Fintype.ofFinite _
  rw [innerOf_eq_plusBoxInterior_map h12]
  unfold plusBoxLocalExpectation plusBoxExpectation
  refine gibbsExpectationBC_extendGraph_screening (IsingModel.latticeGraph d) h12
    (plusBoxInterior d n (n + 1))
    (fun e he u hu => hsep_translated h12 e he u hu)
    (O.lift (hSn1.trans h12)) (O.lift hSn1) (fun σ₁ σ₂ => ?_)
  change O.φ (restrictConfig (hSn1.trans h12) ((configEquivSubtypeProd h12).symm (σ₁, σ₂)))
    = O.φ (restrictConfig hSn1 σ₁)
  rw [restrictConfig_trans hSn1 h12, restrictConfig_configEquivSubtypeProd_symm]

/-- **The translated sandwich middle term equals the cubic `+` local expectation**:
composing the recentering covariance (`gibbsExpectationBC_translatedInner_recenter`)
with the screening connection, the `+` expectation of `O.vadd a` with the translated
inner region on the centered cubic ambient `cubicBox d (n+1+R)` equals
`plusBoxLocalExpectation n (n+1) O`. -/
theorem gibbsExpectationBC_translatedInner_vadd_eq_plusBoxLocal (a : Fin d → ℤ) {n : ℕ}
    {J h β : ℝ} (O : LocalMonotoneObservable d) (hSn1 : O.S ⊆ cubicBox d (n + 1))
    (hSM : (O.vadd a).S ⊆ cubicBox d (n + 1 + latticeRadius a)) :
    gibbsExpectationBC
        (inducedGraph (IsingModel.latticeGraph d) (cubicBox d (n + 1 + latticeRadius a)))
        β (fun _ => J) h (translatedInner a n (n + 1 + latticeRadius a)) (plusConfig _)
        ((O.vadd a).lift hSM)
      = plusBoxLocalExpectation n (n + 1) J h β O hSn1 := by
  rw [gibbsExpectationBC_translatedInner_recenter a O hSM
      (hSn1.trans (cubicBox_succ_subset_vaddFinset_neg a n)),
    gibbsExpectationBC_innerOf_translated_eq_plusBoxLocal a O
      (cubicBox_succ_subset_vaddFinset_neg a n) hSn1]

end Ambient

end IsingModel
