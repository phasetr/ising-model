import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Base finite-volume and ∞-volume correlation wrappers at ℤ^d

Concrete wrappers for the finite-volume (`correlationΛ`, `partitionFunctionΛ`,
`freeEnergyΛ`) and ∞-volume (`correlationInfinite`, `magnetizationInfinite`,
`spontaneousCorrelation`) functionals on the ℤ^d Ising model.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlationΛ volume-monotonicity**:
`A ⊆ Λ₁ ⊆ Λ₂ ⇒ ⟨σ^A⟩_{Λ₁} ≤ ⟨σ^A⟩_{Λ₂}` for ferromagnetic `p`. -/
theorem correlationΛ_latticeGraph_monotone_volume
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (h12 : Λ₁ ⊆ Λ₂)
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset (Fin d → ℤ)} (hA : A ⊆ Λ₁) :
    correlationΛ (IsingModel.latticeGraph d) Λ₁ p (liftFinset A hA)
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ₂ p
          (liftFinset A (hA.trans h12)) :=
  correlationΛ_monotone_volume (IsingModel.latticeGraph d) h12 p hf hA

/-! ## Moved: correlationΛ / partitionFunctionΛ basic bound wrappers

The four wrappers
`partitionFunctionΛ_latticeGraph_pos`,
`abs_correlationΛ_latticeGraph_le_one`,
`correlationΛ_latticeGraph_le_one`,
`correlationΛ_latticeGraph_nonneg` now live in
`BaseCorrelationBounds.lean`. -/


/-! ## Moved: AlongExhaustion apply unfoldings

The 2 `@[simp]` ℤ^d `freeEnergyAlongExhaustion_latticeGraph_apply` and
`partitionFunctionAlongExhaustion_latticeGraph_apply` wrappers now live
alongside the Λ-layer apply unfoldings in
`IsingModel.Concrete.LatticeGraphCorrelation.BaseApply`.
The earlier import path is preserved by re-importing the new child.
-/


/-- **ℤ^d freeEnergyAlongExhaustion = log Z / |Λ|** (log-bridge). -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_eq_log_div_card
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      = (Fintype.card (↑((Ambient.cubicExhaustion d).volume n) : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p n) :=
  freeEnergyAlongExhaustion_eq_log_div_card (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-! ## Moved: correlationAlongExhaustion per-stage bound wrappers

The 4 ℤ^d wrappers
`correlationAlongExhaustion_latticeGraph_le_one`,
`_le_correlationInfinite_of_other`, `_le_correlationInfinite`,
and `_nonneg` now live in
`IsingModel.Concrete.LatticeGraphCorrelation.BaseCorrelationAlongExBounds`.
The earlier import path is preserved by re-importing the new child.
-/


/-- **ℤ^d `correlationInfinite` on the empty site set = 1** (any Exhaustion). -/
@[simp]
theorem correlationInfinite_latticeGraph_empty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p ∅ = 1 :=
  correlationInfinite_empty (IsingModel.latticeGraph d) Λ p

/-! ## Moved: Λ-layer apply unfoldings

The 3 ℤ^d `partitionFunctionΛ_latticeGraph_apply`,
`correlationΛ_latticeGraph_apply`, and `freeEnergyΛ_latticeGraph_apply`
wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.BaseApply`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: magnetization* / spontaneousCorrelation monotone_ambient_subgraph wrappers

The 4 ℤ^d
`magnetization{Λ,AlongExhaustion,Infinite}_latticeGraph_monotone_ambient_subgraph`
and `spontaneousCorrelation_latticeGraph_monotone_ambient_subgraph`
wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.BaseMonotoneAmbientSubgraph`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: spontaneousCorrelation / spontaneousMagnetization_monotone_ambient_subgraph wrappers

The two ℤ^d wrappers
`abs_spontaneousCorrelation_latticeGraph_le_one` and
`spontaneousCorrelation_latticeGraph_sq_le_one`, plus the
`spontaneousMagnetization_latticeGraph_monotone_ambient_subgraph`
companion, now live in
`IsingModel.Concrete.LatticeGraphCorrelation.BaseSpontaneousCorrelation`.
-/


/-! ## Moved: correlationΛ + correlationAlongExhaustion empty/subset/J_zero wrappers

The 7 ℤ^d wrappers
`correlationAlongExhaustion_latticeGraph_{J_zero_of_subset,J_zero_eventually_eq}`,
`correlationΛ_latticeGraph_empty`, and
`correlationAlongExhaustion_latticeGraph_{empty,of_subset,of_not_subset,cubicExhaustion_monotone}`
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.BaseCorrelationAlongEx`.
The earlier import path is preserved by re-importing the new child.
-/


/-- **ℤ^d correlationΛ_gks_second** (GKS-II at finite volume). -/
theorem correlationΛ_latticeGraph_gks_second
    (d : ℕ) {Λ : Finset (Fin d → ℤ)}
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A B : Finset (Fin d → ℤ)} (hA : A ⊆ Λ) (hB : B ⊆ Λ) :
    ∃ hAB : A ∆ B ⊆ Λ,
      correlationΛ (IsingModel.latticeGraph d) Λ p (liftFinset A hA)
        * correlationΛ (IsingModel.latticeGraph d) Λ p (liftFinset B hB)
        ≤ correlationΛ (IsingModel.latticeGraph d) Λ p (liftFinset (A ∆ B) hAB) := by
  have hAB : A ∆ B ⊆ Λ := by
    intro x hx
    rw [Finset.mem_symmDiff] at hx
    rcases hx with ⟨hxA, _⟩ | ⟨hxB, _⟩
    · exact hA hxA
    · exact hB hxB
  refine ⟨hAB, ?_⟩
  exact correlationΛ_gks_second (IsingModel.latticeGraph d) p hf hA hB

end Ambient
end IsingModel
