import IsingModel.ComplexAnalyticity.Compactness

/-!
# Closure-carrier compactness handoffs (GJ §4.6 Thm 4.6.2)

Closure versions of the Arzelà–Ascoli compactness handoffs (Issue #628): the closure of the
pointwise function-space image is closed by definition, and it sits inside the compact pointwise
product by `closure_minimal` against the compact-hence-closed product — so the closedness input
of the closed-product handoffs disappears. Together with the closure inheritance of
equicontinuity, the compact carrier `toFun ⁻¹' closure (toFun '' S)` replaces the range-image
closedness field of the Ascoli data structures.

* `isCompact_closure_toFun_image_complex_of_subset_pi_compacts` — the Tychonoff closure handoff.
* `isCompact_closure_toFun_image_complex_of_norm_le` — the norm-bounded specialisation.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70.
-/

namespace IsingModel

/-- **Tychonoff closure handoff**: with compact pointwise targets, the *closure* of the
pointwise function-space image is compact — no closedness input. -/
theorem isCompact_closure_toFun_image_complex_of_subset_pi_compacts
    {X : Type*} [TopologicalSpace X]
    {S : Set C(X, ℂ)}
    (K : X → Set ℂ)
    (hK : ∀ x, IsCompact (K x))
    (hmem : ∀ f ∈ S, ∀ x, f x ∈ K x) :
    IsCompact (closure (ContinuousMap.toFun '' S)) := by
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi hK) isClosed_closure ?_
  refine closure_minimal ?_ (isCompact_univ_pi hK).isClosed
  rintro _ ⟨f, hf, rfl⟩
  exact Set.mem_pi.mpr (fun x _ => hmem f hf x)

/-- **Norm-bounded Tychonoff closure handoff**: pointwise norm bounds alone make the closure of
the pointwise image compact. -/
theorem isCompact_closure_toFun_image_complex_of_norm_le
    {X : Type*} [TopologicalSpace X]
    {S : Set C(X, ℂ)}
    (R : X → ℝ)
    (hnorm : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ R x) :
    IsCompact (closure (ContinuousMap.toFun '' S)) :=
  isCompact_closure_toFun_image_complex_of_subset_pi_compacts
    (fun x => Metric.closedBall (0 : ℂ) (R x))
    (fun x => isCompact_closedBall (0 : ℂ) (R x))
    (fun f hf x => by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm f hf x)

/-- **The pointwise image of an equicontinuous family of continuous maps is equicontinuous as a
set**: re-index along representatives. -/
theorem set_equicontinuous_toFun_image
    {X : Type*} [TopologicalSpace X] {S : Set C(X, ℂ)}
    (hSeq : Equicontinuous ((↑) : S → X → ℂ)) :
    (ContinuousMap.toFun '' S).Equicontinuous := by
  classical
  have hcomp := hSeq.comp
    (fun a : ContinuousMap.toFun '' S => (⟨a.2.choose, a.2.choose_spec.1⟩ : S))
  have heq : (((↑) : S → X → ℂ) ∘
      fun a : ContinuousMap.toFun '' S => (⟨a.2.choose, a.2.choose_spec.1⟩ : S))
      = ((↑) : ContinuousMap.toFun '' S → X → ℂ) := by
    funext a
    simp only [Function.comp_apply]
    exact a.2.choose_spec.2
  rwa [heq] at hcomp

/-- **Members of the closure of the pointwise image are continuous**: the closure is
equicontinuous, and members of an equicontinuous set are continuous. -/
theorem continuous_of_mem_closure_toFun_image
    {X : Type*} [TopologicalSpace X] {S : Set C(X, ℂ)}
    (hSeq : Equicontinuous ((↑) : S → X → ℂ))
    {g : X → ℂ} (hg : g ∈ closure (ContinuousMap.toFun '' S)) :
    Continuous g :=
  (set_equicontinuous_toFun_image hSeq).closure.continuous ⟨g, hg⟩

/-- **The closure carrier projects exactly onto the closure**: the pointwise image of
`toFun ⁻¹' closure (toFun '' S)` is `closure (toFun '' S)` — surjectivity holds because every
member of the closure is continuous and lifts to a `ContinuousMap`. -/
theorem toFun_image_preimage_closure_eq
    {X : Type*} [TopologicalSpace X] {S : Set C(X, ℂ)}
    (hSeq : Equicontinuous ((↑) : S → X → ℂ)) :
    ContinuousMap.toFun '' (ContinuousMap.toFun ⁻¹' closure (ContinuousMap.toFun '' S))
      = closure (ContinuousMap.toFun '' S) := by
  apply Set.Subset.antisymm
  · exact Set.image_preimage_subset _ _
  · intro g hg
    exact ⟨⟨g, continuous_of_mem_closure_toFun_image hSeq hg⟩, hg, rfl⟩

/-- **Compact-open compactness of the closure carrier** (no closedness input): with pointwise
norm bounds and equicontinuity, the set of continuous maps whose underlying function lies in
the closure of the pointwise image is compact in the compact-open topology. -/
theorem isCompact_closureCarrier_compactOpen_complex_of_norm_le_equicontinuous
    {X : Type*} [TopologicalSpace X] {S : Set C(X, ℂ)} (R : X → ℝ)
    (hnorm : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ R x)
    (hSeq : Equicontinuous ((↑) : S → X → ℂ)) :
    IsCompact (ContinuousMap.toFun ⁻¹' closure (ContinuousMap.toFun '' S) : Set C(X, ℂ)) := by
  refine ArzelaAscoli.isCompact_of_equicontinuous _ ?_ ?_
  · rw [toFun_image_preimage_closure_eq hSeq]
    exact isCompact_closure_toFun_image_complex_of_norm_le R hnorm
  · have hcl := (set_equicontinuous_toFun_image hSeq).closure
    have hcomp := hcl.comp
      (fun f : (ContinuousMap.toFun ⁻¹' closure (ContinuousMap.toFun '' S) : Set C(X, ℂ)) =>
        (⟨(f : C(X, ℂ)), f.2⟩ : closure (ContinuousMap.toFun '' S)))
    exact hcomp

end IsingModel
