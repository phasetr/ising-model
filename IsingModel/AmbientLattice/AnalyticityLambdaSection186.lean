import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.HighTempGeneralRegularity.FreeEnergyAnalyticity

/-!
# Directional analyticity of the Λ-restricted partition function and free energy (§18.6)

Statements for an ambient graph `G : SimpleGraph V` and a finite volume `Λ : Finset V`,
about `partitionFunctionΛ G Λ` and `freeEnergyΛ G Λ`. Three parameter regimes appear, and
each statement belongs to exactly one of them; the regime is fixed by which field value the
slice freezes, so the qualifications below do not carry across the paragraph breaks.

*Zero field.* For the slices `fun β' ↦ partitionFunctionΛ G Λ ⟨J, 0, β'⟩` and
`fun J' ↦ partitionFunctionΛ G Λ ⟨J', 0, β⟩`: `Continuous`, `Differentiable ℝ`,
`AnalyticAt ℝ` at an arbitrary point, and `AnalyticOnNhd ℝ` over `Set.univ`. For the two
matching free-energy slices: `AnalyticAt ℝ` at an arbitrary point and `AnalyticOnNhd ℝ`
over `Set.univ`.

*Arbitrary field.* The free energy is `AnalyticAt ℝ` at an arbitrary point and
`AnalyticOnNhd ℝ` over `Set.univ` in each of the three directions `β`, `J` and `h` taken
separately; the partition function is `AnalyticAt ℝ` in each of the same three directions.

*Joint in the triple.* `fun (β, J, h) ↦ partitionFunctionΛ G Λ ⟨J, h, β⟩` is `Continuous`
and `Differentiable ℝ` on `ℝ × ℝ × ℝ`.

Every statement takes exactly two instance binders, `DecidableEq V` and
`Fintype (inducedGraph G Λ).edgeSet`, and its Prop-valued hypothesis list is empty; in
particular the free-energy statements ask nothing of `Λ`, whose cardinality enters
`freeEnergyΛ` only through the factor `(Λ.card : ℝ)⁻¹`. Each proof rewrites the Λ-layer
definition to its base-layer counterpart at `inducedGraph G Λ` and applies the §18.6 result
there.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.6 partitionFunctionΛ regularity at `h = 0` Λ-layer wraps -/

/-- **Λ-layer: partitionFunction Continuous in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_continuous_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Continuous (fun β : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_continuous_beta_h_zero
    (inducedGraph G Λ) J

/-- **Λ-layer: partitionFunction Continuous in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_continuous_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Continuous (fun J : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_continuous_J_h_zero
    (inducedGraph G Λ) β

/-- **Λ-layer: partitionFunction Differentiable in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_differentiable_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Differentiable ℝ
      (fun β : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_differentiable_beta_h_zero
    (inducedGraph G Λ) J

/-- **Λ-layer: partitionFunction Differentiable in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_differentiable_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Differentiable ℝ
      (fun J : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_differentiable_J_h_zero
    (inducedGraph G Λ) β

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_analyticAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticAt ℝ
      (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β'⟩) β := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_beta_h_zero
    (inducedGraph G Λ) J β

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_analyticAt_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) :
    AnalyticAt ℝ
      (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', 0, β⟩) J := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_J_h_zero
    (inducedGraph G Λ) β J

/-- **Λ-layer: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `β`
at `h = 0`**. -/
theorem partitionFunctionΛ_analyticOnNhd_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β'⟩) Set.univ := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticOnNhd_beta_h_zero
    (inducedGraph G Λ) J

/-- **Λ-layer: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `J`
at `h = 0`**. -/
theorem partitionFunctionΛ_analyticOnNhd_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', 0, β⟩) Set.univ := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticOnNhd_J_h_zero
    (inducedGraph G Λ) β

/-! ### §18.6 freeEnergyΛ per-direction analyticity Λ-layer wraps -/

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem freeEnergyΛ_analyticAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, 0, β'⟩) β :=
  IsingModel.freeEnergy_analyticAt_beta_h_zero (inducedGraph G Λ) J β

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem freeEnergyΛ_analyticAt_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', 0, β⟩) J :=
  IsingModel.freeEnergy_analyticAt_J_h_zero (inducedGraph G Λ) β J

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β`
at `h = 0`**. -/
theorem freeEnergyΛ_analyticOnNhd_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, 0, β'⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_beta_h_zero (inducedGraph G Λ) J

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J`
at `h = 0`**. -/
theorem freeEnergyΛ_analyticOnNhd_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', 0, β⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_J_h_zero (inducedGraph G Λ) β

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `β` at general `h`**. -/
theorem freeEnergyΛ_analyticAt_beta_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, h, β'⟩) β :=
  IsingModel.freeEnergy_analyticAt_beta_general_h
    (inducedGraph G Λ) J h β

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `J` at general `h`**. -/
theorem freeEnergyΛ_analyticAt_J_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', h, β⟩) J :=
  IsingModel.freeEnergy_analyticAt_J_general_h
    (inducedGraph G Λ) β h J

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `h`**. -/
theorem freeEnergyΛ_analyticAt_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ => freeEnergyΛ G Λ ⟨J, h', β⟩) h :=
  IsingModel.freeEnergy_analyticAt_h (inducedGraph G Λ) J β h

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
general `h`**. -/
theorem freeEnergyΛ_analyticOnNhd_beta_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, h, β'⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_beta_general_h
    (inducedGraph G Λ) J h

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
general `h`**. -/
theorem freeEnergyΛ_analyticOnNhd_J_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h : ℝ) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', h, β⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_J_general_h
    (inducedGraph G Λ) β h

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `h`**. -/
theorem freeEnergyΛ_analyticOnNhd_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticOnNhd ℝ
      (fun h' : ℝ => freeEnergyΛ G Λ ⟨J, h', β⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_h (inducedGraph G Λ) J β

/-! ### §18.6 partitionFunction joint + general-h analyticity
Λ-layer wraps -/

/-- **Λ-layer: partitionFunction jointly `Continuous` in
`(β, J, h)`**. -/
theorem partitionFunctionΛ_continuous_joint
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionΛ G Λ ⟨p.2.1, p.2.2, p.1⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_continuous_joint (inducedGraph G Λ)

/-- **Λ-layer: partitionFunction jointly `Differentiable ℝ` in
`(β, J, h)`**. -/
theorem partitionFunctionΛ_differentiable_joint
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionΛ G Λ ⟨p.2.1, p.2.2, p.1⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_differentiable_joint
    (inducedGraph G Λ)

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `β` at general
`h`**. -/
theorem partitionFunctionΛ_analyticAt_beta_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, h, β'⟩) β := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_beta_general_h
    (inducedGraph G Λ) J h β

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `J` at general
`h`**. -/
theorem partitionFunctionΛ_analyticAt_J_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', h, β⟩) J := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_J_general_h
    (inducedGraph G Λ) β h J

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `h`**. -/
theorem partitionFunctionΛ_analyticAt_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ => partitionFunctionΛ G Λ ⟨J, h', β⟩) h := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_h
    (inducedGraph G Λ) J β h


end Ambient

end IsingModel
