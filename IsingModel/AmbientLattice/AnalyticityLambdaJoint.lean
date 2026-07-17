import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.HighTempGeneralRegularity.CorrelationRegularity

/-!
# AmbientLattice/Analyticity Λ-level joint analyticity wrappers

Narrow child module for the 10 Λ-level joint analyticity wrappers
(partitionFunctionΛ + freeEnergyΛ + correlationΛ AnalyticAt /
AnalyticOnNhd / Continuous / Differentiable joint). The theorem
names are unchanged from the former `Analyticity` declarations.
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

/-- **correlationΛ jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6,
Λ-layer): direct lift of `IsingModel.correlation_analyticAt_joint`. -/
theorem correlationΛ_analyticAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (A : Finset (↑Λ : Type _)) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => correlationΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ A)
      (β, J, h) :=
  IsingModel.correlation_analyticAt_joint (inducedGraph G Λ) A β J h

/-- **correlationΛ jointly `AnalyticOnNhd ℝ` over `Set.univ`** (§18.6,
Λ-layer). -/
theorem correlationΛ_analyticOnNhd_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (A : Finset (↑Λ : Type _)) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => correlationΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ A)
      Set.univ :=
  IsingModel.correlation_analyticOnNhd_joint (inducedGraph G Λ) A

/-- **correlationΛ jointly `Continuous` in `(β, J, h)`** (§18.6, Λ-layer). -/
theorem correlationΛ_continuous_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (A : Finset (↑Λ : Type _)) :
    Continuous (fun p : ℝ × ℝ × ℝ => correlationΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ A) :=
  IsingModel.correlation_continuous_joint (inducedGraph G Λ) A

/-- **correlationΛ jointly `Differentiable ℝ` in `(β, J, h)`** (§18.6,
Λ-layer). -/
theorem correlationΛ_differentiable_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun p : ℝ × ℝ × ℝ => correlationΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ A) :=
  IsingModel.correlation_differentiable_joint (inducedGraph G Λ) A

end Ambient

end IsingModel
