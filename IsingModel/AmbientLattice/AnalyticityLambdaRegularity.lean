import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.HighTempGeneralRegularity.PolymerBounds

/-!
# AmbientLattice/Analyticity Λ regularity wrappers

Narrow child module for the 10 Λ-layer freeEnergyΛ correction +
polymerFreeEnergy_Λ continuous/differentiable + tanh
analyticAt/analyticOnNhd wrappers. The theorem names are unchanged from
the former `Analyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Λ-layer: strict `freeEnergyΛ` upper bound in cluster-expansion
convergence regime** (§18.5 Λ wrap of #1527). -/
theorem freeEnergyΛ_lt_log_two_plus_high_temp_correction
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) <
      Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / Λ.card := by
  rw [freeEnergyΛ_apply]
  have hne' : 0 < Fintype.card ↑Λ := by rw [Fintype.card_coe]; exact hne
  have := IsingModel.freeEnergy_lt_log_two_plus_high_temp_correction
    (inducedGraph G Λ) J β hβJ hne' h_pow
  rwa [Fintype.card_coe] at this

/-- **Λ-layer: strict `freeEnergyΛ` upper bound in cluster-expansion
convergence regime (ferromagnetic)** (§18.5 Λ wrap, ferro). -/
theorem freeEnergyΛ_lt_log_two_plus_high_temp_correction_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) <
      Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / Λ.card :=
  freeEnergyΛ_lt_log_two_plus_high_temp_correction
    G Λ J β (mul_nonneg hβ.le hJ) hne h_pow

/-- **Λ-layer: `polymerFreeEnergy` is `ContinuousAt` for `t ≥ 0`**
(§18.5 Λ wrap of #1517 / Step 611). -/
theorem polymerFreeEnergy_Λ_continuousAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun s : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ) s) t :=
  IsingModel.polymerFreeEnergy_continuousAt (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy` is `DifferentiableAt` for `t ≥ 0`**
(§18.5 Λ wrap). -/
theorem polymerFreeEnergy_Λ_differentiableAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableAt ℝ (fun s : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ) s) t :=
  IsingModel.polymerFreeEnergy_differentiableAt (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy` is `ContinuousOn (Set.Ici 0)`**
(§18.5 Λ wrap). -/
theorem polymerFreeEnergy_Λ_continuousOn_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    ContinuousOn (fun s : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ) s)
      (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_continuousOn_Ici_zero (inducedGraph G Λ)

/-- **Λ-layer: `polymerFreeEnergy` is `DifferentiableOn (Set.Ici 0)`**
(§18.5 Λ wrap). -/
theorem polymerFreeEnergy_Λ_differentiableOn_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    DifferentiableOn ℝ (fun s : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ) s)
      (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_differentiableOn_Ici_zero
    (inducedGraph G Λ)

/-- **Λ-layer: `polymerFreeEnergy ∘ tanh ∘ (·*J)` `AnalyticAt ℝ`
in β** (§18.6 Λ wrap of #1569 Step 613). -/
theorem polymerFreeEnergy_Λ_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun β' : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β' * J))) β :=
  IsingModel.polymerFreeEnergy_tanh_analyticAt_beta
    (inducedGraph G Λ) J β hβJ

/-- **Λ-layer: `polymerFreeEnergy ∘ tanh ∘ (β*·)` `AnalyticAt ℝ`
in J** (§18.6 Λ wrap). -/
theorem polymerFreeEnergy_Λ_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun J' : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J'))) J :=
  IsingModel.polymerFreeEnergy_tanh_analyticAt_J
    (inducedGraph G Λ) β J hβJ

/-- **Λ-layer: `polymerFreeEnergy ∘ tanh ∘ (·*J)` `AnalyticOnNhd
ℝ _ (Set.Ici 0)` in β under `0 ≤ J`** (§18.6 Λ wrap). -/
theorem polymerFreeEnergy_Λ_tanh_analyticOnNhd_beta_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β' * J))) (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_tanh_analyticOnNhd_beta_Ici_zero
    (inducedGraph G Λ) hJ

/-- **Λ-layer: `polymerFreeEnergy ∘ tanh ∘ (β*·)` `AnalyticOnNhd
ℝ _ (Set.Ici 0)` in J under `0 ≤ β`** (§18.6 Λ wrap). -/
theorem polymerFreeEnergy_Λ_tanh_analyticOnNhd_J_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β : ℝ} (hβ : 0 ≤ β) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J'))) (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_tanh_analyticOnNhd_J_Ici_zero
    (inducedGraph G Λ) hβ


end Ambient

end IsingModel
