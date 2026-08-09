import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d free-energy trivial slices and the edgeless-graph comparison

Concrete `latticeGraph d` statements along an arbitrary `Ambient.Exhaustion` of `Fin d → ℤ`.
At vanishing inverse temperature, and at vanishing coupling and field together, the
infinite-volume free energy is `Real.log 2`; nonemptiness of every volume of the exhaustion
is the hypothesis in each case, and no instance argument is taken. At vanishing coupling the
free energy agrees with its value on the edgeless graph over `Fin d → ℤ`, in the
infinite-volume form as well as at a fixed stage; these carry no `Prop`-typed hypothesis, but
each requires a `Fintype` instance on the edge set induced by the edgeless graph on every
volume.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `freeEnergyInfinite_beta_zero`** (any-Exhaustion, ∀ n nonempty):
`freeEnergyInfinite ⟨J, h, 0⟩ = log 2`. -/
theorem freeEnergyInfinite_latticeGraph_beta_zero_forall_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_beta_zero (IsingModel.latticeGraph d) Λ J h hne

/-- **ℤ^d `freeEnergyInfinite_zero_params`** (any-Exhaustion, ∀ n nonempty):
`freeEnergyInfinite ⟨0, 0, β⟩ = log 2`. -/
theorem freeEnergyInfinite_latticeGraph_zero_params_forall_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_zero_params (IsingModel.latticeGraph d) Λ β hne

/-- **ℤ^d `freeEnergyInfinite_eq_bot_at_J_zero`** (any-Exhaustion):
at `J = 0` the ∞-vol free energy equals the `⊥`-graph value. -/
theorem freeEnergyInfinite_latticeGraph_eq_bot_at_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
      (⊥ : SimpleGraph (Fin d → ℤ)) (Λ.volume n)).edgeSet]
    (h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (⊥ : SimpleGraph (Fin d → ℤ)) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_eq_bot_at_J_zero (IsingModel.latticeGraph d) Λ h β

/-- **ℤ^d `freeEnergyAlongExhaustion_eq_bot_at_J_zero`** (any-Exhaustion):
at `J = 0` the per-stage free energy equals the `⊥`-graph value. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_bot_at_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
      (⊥ : SimpleGraph (Fin d → ℤ)) (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (⊥ : SimpleGraph (Fin d → ℤ)) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_eq_bot_at_J_zero
    (IsingModel.latticeGraph d) Λ h β n

end Ambient
end IsingModel
