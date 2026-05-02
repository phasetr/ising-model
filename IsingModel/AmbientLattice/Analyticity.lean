import IsingModel.AmbientLattice.Defs
import IsingModel.ClusterExpansion

/-!
# Joint analyticity for AmbientLattice finite-volume Λ-restricted Ising

Lifts the joint analyticity of `partitionFunction` and `freeEnergy` in
`(β, J, h) ∈ ℝ × ℝ × ℝ` (Glimm-Jaffe §18.6 capstone, established in
`IsingModel/ClusterExpansion.lean` via direct sum-of-exp analyticity)
to the finite-volume Λ-restricted versions defined in
`IsingModel/AmbientLattice/Defs.lean`. Each theorem is a thin wrapper
around the corresponding theorem on `inducedGraph G Λ`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **partitionFunctionΛ jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6
capstone, Λ-layer): direct lift of `IsingModel.partitionFunction_analyticAt_joint`
to the finite-volume Λ-restricted partition function. -/
theorem partitionFunctionΛ_analyticAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => partitionFunctionΛ G Λ ⟨p.2.1, p.2.2, p.1⟩)
      (β, J, h) :=
  IsingModel.partitionFunction_analyticAt_joint (inducedGraph G Λ) β J h

/-- **partitionFunctionΛ jointly `AnalyticOnNhd ℝ` over `Set.univ`**
(§18.6 capstone, Λ-layer). -/
theorem partitionFunctionΛ_analyticOnNhd_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => partitionFunctionΛ G Λ ⟨p.2.1, p.2.2, p.1⟩)
      Set.univ :=
  IsingModel.partitionFunction_analyticOnNhd_joint (inducedGraph G Λ)

/-- **freeEnergyΛ jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6
capstone, Λ-layer): direct lift of `IsingModel.freeEnergy_analyticAt_joint`
to the finite-volume Λ-restricted free energy. -/
theorem freeEnergyΛ_analyticAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => freeEnergyΛ G Λ ⟨p.2.1, p.2.2, p.1⟩)
      (β, J, h) :=
  IsingModel.freeEnergy_analyticAt_joint (inducedGraph G Λ) β J h

/-- **freeEnergyΛ jointly `AnalyticOnNhd ℝ` over `Set.univ`** (§18.6
capstone, Λ-layer). -/
theorem freeEnergyΛ_analyticOnNhd_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => freeEnergyΛ G Λ ⟨p.2.1, p.2.2, p.1⟩)
      Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_joint (inducedGraph G Λ)

/-- **freeEnergyΛ jointly `Continuous` in `(β, J, h)`** (§18.6, Λ-layer). -/
theorem freeEnergyΛ_continuous_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Continuous (fun p : ℝ × ℝ × ℝ => freeEnergyΛ G Λ ⟨p.2.1, p.2.2, p.1⟩) :=
  IsingModel.freeEnergy_continuous_joint (inducedGraph G Λ)

/-- **freeEnergyΛ jointly `Differentiable ℝ` in `(β, J, h)`** (§18.6, Λ-layer). -/
theorem freeEnergyΛ_differentiable_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Differentiable ℝ
      (fun p : ℝ × ℝ × ℝ => freeEnergyΛ G Λ ⟨p.2.1, p.2.2, p.1⟩) :=
  IsingModel.freeEnergy_differentiable_joint (inducedGraph G Λ)

end Ambient
end IsingModel
