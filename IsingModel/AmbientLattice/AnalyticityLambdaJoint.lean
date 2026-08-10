import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.HighTempGeneralRegularity.CorrelationRegularity

/-!
# Joint regularity of the Λ-restricted partition function, free energy and correlation

Statements for an ambient graph `G : SimpleGraph V` and a finite volume `Λ : Finset V`,
about the maps on `ℝ × ℝ × ℝ` that send `(β, J, h)` to `partitionFunctionΛ G Λ ⟨J, h, β⟩`,
to `freeEnergyΛ G Λ ⟨J, h, β⟩`, and — for a test set `A : Finset ↑Λ` — to
`correlationΛ G Λ ⟨J, h, β⟩ A`. All three are jointly `AnalyticAt ℝ` at an arbitrary point
of `ℝ × ℝ × ℝ` and jointly `AnalyticOnNhd ℝ` over `Set.univ`, so no parameter value is
excluded and no radius is named. The free energy and the correlation are in addition
`Continuous` and `Differentiable ℝ`; the partition function appears here in the two
analyticity forms alone.

Every statement takes exactly two instance binders, `DecidableEq V` and
`Fintype (inducedGraph G Λ).edgeSet`, and its Prop-valued hypothesis list is empty: the
coupling, the field and the inverse temperature range over all of `ℝ`, and `Λ` is
unrestricted, the empty volume included. Each proof rewrites the Λ-layer definition to its
base-layer counterpart at `inducedGraph G Λ` and applies the §18.6 joint result there.
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
