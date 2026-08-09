import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d finite-volume correlation monotonicity, the log bridge, and GKS-II

Concrete `latticeGraph d` statements about the finite-volume correlation `correlationΛ`,
about the free energy along `Ambient.cubicExhaustion d`, and about the infinite-volume
correlation.

Enlarging the finite volume does not decrease the correlation of a site set that already
lies in the smaller volume, and the product of the correlations of two site sets of one
finite volume is at most the correlation of their symmetric difference. Both of those
assume `Ferromagnetic` on the parameter record, and the symmetric-difference statement
carries the containment of that difference in the enclosing volume inside its conclusion
rather than taking it as a hypothesis.

At a stage of the cubic exhaustion the free energy is the logarithm of the partition
function of that stage divided by the number of sites the stage holds, and the
infinite-volume correlation of the empty site set is `1` along an arbitrary
`Ambient.Exhaustion` of `Fin d → ℤ`; neither of those takes a hypothesis. No instance
argument is taken anywhere in this module.
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

/-- **ℤ^d `correlationInfinite` on the empty site set = 1** (any Exhaustion). -/
@[simp]
theorem correlationInfinite_latticeGraph_empty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p ∅ = 1 :=
  correlationInfinite_empty (IsingModel.latticeGraph d) Λ p

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
