import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateTranslationFinal

/-!
# General shell separation for ambient independence (Issue #3581)

Towards exhaustion independence of the cubic-exhaustion `+`-state functional: the
shell-separation hypothesis `hsep` of the general-ambient screening
(`gibbsExpectationBC_extendGraph_screening`) holds whenever every site of the inner
region `I` has all its lattice neighbours inside the smaller ambient `Λ₁`.  This
generalises the cubic-specific `hsep_translated` (#3587).

* `hsep_of_neighbors_subset` — the general shell-separation criterion.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17 (statement p. 95, proof pp. 102–103).
-/

namespace IsingModel

namespace Ambient

open Finset

variable {d : ℕ}

/-- **General shell separation**: if every site of the inner region `I` has all its
lattice neighbours inside `Λ₁`, then every extra edge (in the induced graph on `Λ₂`
but not the `Λ₁`-extension) has both endpoints outside `I` — so the screening
hypothesis `hsep` holds. -/
theorem hsep_of_neighbors_subset {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ₂).edgeSet]
    [Fintype (extendGraphFromΛ₁ (IsingModel.latticeGraph d) Λ₁ Λ₂).edgeSet]
    (I : Finset (↑Λ₁ : Type _))
    (hNN : ∀ k ∈ I, ∀ y : Fin d → ℤ, (IsingModel.latticeGraph d).Adj k.val y → y ∈ Λ₁)
    (e : Sym2 (↑Λ₂ : Type _))
    (he : e ∈ (inducedGraph (IsingModel.latticeGraph d) Λ₂).edgeFinset \
        (extendGraphFromΛ₁ (IsingModel.latticeGraph d) Λ₁ Λ₂).edgeFinset)
    (u : (↑Λ₂ : Type _)) (hu : u ∈ e) :
    u ∉ I.map (subtypeInclEmb h12) := by
  simp only [Finset.mem_map, subtypeInclEmb, Function.Embedding.coeFn_mk, not_exists, not_and]
  intro k hkI hku
  rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset] at he
  obtain ⟨hind, hnotext⟩ := he
  revert hu hind hnotext
  refine Sym2.ind (fun x y => ?_) e
  intro hmem hind hnotext
  rw [SimpleGraph.mem_edgeSet] at hind
  apply hnotext
  rw [SimpleGraph.mem_edgeSet]
  have hadj : (IsingModel.latticeGraph d).Adj x.val y.val := hind
  rcases Sym2.mem_iff.mp hmem with hux | huy
  · have hxv : (x : Fin d → ℤ) = k.val := by
      rw [← hux]; exact congrArg Subtype.val hku.symm
    refine ⟨hxv ▸ k.2, hNN k hkI y.val (hxv ▸ hadj), hadj⟩
  · have hyv : (y : Fin d → ℤ) = k.val := by
      rw [← huy]; exact congrArg Subtype.val hku.symm
    refine ⟨hNN k hkI x.val (hyv ▸ hadj.symm), hyv ▸ k.2, hadj⟩

/-- **Ambient independence of the `+` boundary expectation** (general inner region):
for an inner region `I` whose lattice neighbours all lie in `Λ₁ ⊆ Λ₂`, and an
observable depending only on the inner configuration, the `+` boundary expectation
on `Λ₂` equals that on `Λ₁` — the shell is frozen `+` and cancels.  (The
neighbours-in-`Λ₁` separation supplies the screening hypothesis via
`hsep_of_neighbors_subset`.) -/
theorem gibbsExpectationBC_screening_of_neighbors {Λ₁ Λ₂ : Finset (Fin d → ℤ)}
    (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ₂).edgeSet]
    (I : Finset (↑Λ₁ : Type _)) {J h β : ℝ}
    (hNN : ∀ k ∈ I, ∀ y : Fin d → ℤ, (IsingModel.latticeGraph d).Adj k.val y → y ∈ Λ₁)
    (φ : Config (↑Λ₂ : Type _) → ℝ) (φ' : Config (↑Λ₁ : Type _) → ℝ)
    (hφ : ∀ σ₁ σ₂, φ ((configEquivSubtypeProd h12).symm (σ₁, σ₂)) = φ' σ₁) :
    gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) Λ₂) β (fun _ => J) h
        (I.map (subtypeInclEmb h12)) (plusConfig _) φ
      = gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) Λ₁) β (fun _ => J) h I
          (plusConfig _) φ' := by
  haveI : Fintype (extendGraphFromΛ₁ (IsingModel.latticeGraph d) Λ₁ Λ₂).edgeSet :=
    Fintype.ofFinite _
  exact gibbsExpectationBC_extendGraph_screening (IsingModel.latticeGraph d) h12 I
    (fun e he u hu => hsep_of_neighbors_subset h12 I hNN e he u hu) φ φ' hφ

end Ambient

end IsingModel
