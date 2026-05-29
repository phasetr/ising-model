import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.IncrementCapstone

/-!
# Direct increment API for the Lemma 17.5.2 capstone

This file extracts the **direct increment** API from `CEConditionalCapstone.lean`
(Issue #3054, refactor PR #3127 per codex strategic review). The CE-route
bundles in `CEConditionalCapstone.lean` route the user from a complex circle
bound + ne-zero disc to the summable derivative increment via the Cauchy
estimate; this file provides a parallel API for users whose increment bound
comes from a non-CE source (direct supply, or a finer complex analysis input
that does not fit the standard Cauchy decomposition).

The `CERouteIccDirect{,Poly}GeometricIncrement` predicates are named aliases
for the `hincr` shape expected by the `IncrementCapstone.lean` consumers.
The four pass-through theorems compose the predicates with the consumers
to deliver the named `Lemma_17_5_2_UpperBound` or the two-sided sandwich.

These do not depend on any CE-route bundle infrastructure (no Cauchy
estimate, no `Z_ℂ ≠ 0` hypothesis, no sphere bound). The CE-route bundles in
`CEConditionalCapstone.lean` continue to serve when the increment is to be
derived from complex analyticity; this file serves the complementary entry
point.

References:

* Glimm-Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp. 311-312.
* Codex strategic review for Issue #3054 (PR #3125-#3126).
-/

namespace IsingModel
namespace Ambient

/-- **Direct geometric-increment predicate**, parallel to
`CERouteIccGeometricIncrement` (in `CEConditionalCapstone.lean`) but bypassing
the Cauchy decomposition entirely. This is a named alias for the `hincr`
shape expected by
`lemma_17_5_2_{upper_bound,capstone}_of_geometric_increments_on_covered_stages`
in `IncrementCapstone.lean`. Useful as a structurally explicit entry point
when the user has a direct increment bound from any non-CE route. -/
def CERouteIccDirectGeometricIncrement
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ) : Prop :=
  ∀ β₁ β₂ : ℝ, Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
    ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
      ∀ β ∈ Set.Icc β₁ β₂,
        dist
          (deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
          (deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
              M * ratio ^ k

/-- **Direct poly-geometric-increment predicate**, parallel to
`CERouteIccPolyGeometricIncrement` (in `CEConditionalCapstone.lean`) but
bypassing the Cauchy decomposition. Named alias for the `hincr` shape
expected by
`lemma_17_5_2_{upper_bound,capstone}_of_poly_geometric_increments_on_covered_stages`. -/
def CERouteIccDirectPolyGeometricIncrement
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ) : Prop :=
  ∀ β₁ β₂ : ℝ, Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
    ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
      ∀ β ∈ Set.Icc β₁ β₂,
        dist
          (deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
          (deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
              M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k)

/-- **End-to-end Lemma 17.5.2 upper bound from direct geometric increment**:
direct pass-through of `CERouteIccDirectGeometricIncrement` to
`lemma_17_5_2_upper_bound_of_geometric_increments_on_covered_stages`. -/
theorem lemma_17_5_2_upper_bound_of_CERouteIccDirectGeometricIncrement
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccDirectGeometricIncrement Λ J x z M ratio) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_geometric_increments_on_covered_stages
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1 h

/-- **End-to-end Lemma 17.5.2 capstone from direct geometric increment + decay**:
direct pass-through of `CERouteIccDirectGeometricIncrement` and the validating
endpoint pseudo-mass exponential-decay hypothesis to
`lemma_17_5_2_capstone_of_geometric_increments_on_covered_stages`. -/
theorem lemma_17_5_2_capstone_of_CERouteIccDirectGeometricIncrement
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccDirectGeometricIncrement Λ J x z M ratio)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_geometric_increments_on_covered_stages
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1 h hdecay

/-- **End-to-end Lemma 17.5.2 upper bound from direct poly-geometric increment**:
pass-through to `lemma_17_5_2_upper_bound_of_poly_geometric_increments_on_covered_stages`. -/
theorem lemma_17_5_2_upper_bound_of_CERouteIccDirectPolyGeometricIncrement
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccDirectPolyGeometricIncrement Λ J x z M ratio) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_poly_geometric_increments_on_covered_stages
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1 h

/-- **End-to-end Lemma 17.5.2 capstone from direct poly-geometric increment + decay**:
pass-through to `lemma_17_5_2_capstone_of_poly_geometric_increments_on_covered_stages`. -/
theorem lemma_17_5_2_capstone_of_CERouteIccDirectPolyGeometricIncrement
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccDirectPolyGeometricIncrement Λ J x z M ratio)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_poly_geometric_increments_on_covered_stages
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1 h hdecay

end Ambient
end IsingModel
