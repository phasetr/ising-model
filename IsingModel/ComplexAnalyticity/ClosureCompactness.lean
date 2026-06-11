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

end IsingModel
