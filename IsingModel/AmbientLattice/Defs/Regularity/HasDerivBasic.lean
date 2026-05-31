import IsingModel.AmbientLattice.Defs.Regularity.Correlation

/-!
# Lambda-layer regularity split

HasDerivAt wrappers for free energy, partition function, and Boltzmann weight.

Part of the split Lambda-layer regularity wrappers (Issue #1850).
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **HasDerivAt for `freeEnergyΛ` in β at general h** with explicit
derivative `(|↑Λ|)⁻¹ · ⟨−H⟩`. -/
theorem hasDerivAt_freeEnergyΛ_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun β' => freeEnergyΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ))
      ((Fintype.card ↑(Λ : Finset V) : ℝ)⁻¹ *
        IsingModel.gibbsExpectation (inducedGraph G Λ)
          (⟨J, h, β⟩ : IsingParams ℝ)
          (fun σ => - IsingModel.hamiltonian (inducedGraph G Λ)
                      (⟨J, h, β⟩ : IsingParams ℝ) σ)) β := by
  simp_rw [freeEnergyΛ_apply]
  exact IsingModel.hasDerivAt_freeEnergy_beta_general_h _ J h β

/-- **HasDerivAt for `freeEnergyΛ` in J** with explicit derivative
`(|↑Λ|)⁻¹ · ⟨β·∑_e edgeSpin⟩`. -/
theorem hasDerivAt_freeEnergyΛ_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    HasDerivAt (fun J' => freeEnergyΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ))
      ((Fintype.card ↑(Λ : Finset V) : ℝ)⁻¹ *
        IsingModel.gibbsExpectation (inducedGraph G Λ)
          (⟨J, h, β⟩ : IsingParams ℝ)
          (fun σ => β * (∑ e ∈ (inducedGraph G Λ).edgeFinset,
            IsingModel.edgeSpin (K := ℝ) σ e))) J := by
  simp_rw [freeEnergyΛ_apply]
  exact IsingModel.hasDerivAt_freeEnergy_J _ J h β

/-- **HasDerivAt for `freeEnergyΛ` in h** with explicit derivative
`(|↑Λ|)⁻¹ · ⟨β · M⟩` (magnetization per site). -/
theorem hasDerivAt_freeEnergyΛ_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    HasDerivAt (fun h' => freeEnergyΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ))
      ((Fintype.card ↑(Λ : Finset V) : ℝ)⁻¹ *
        IsingModel.gibbsExpectation (inducedGraph G Λ)
          (⟨J, h, β⟩ : IsingParams ℝ)
          (fun σ => β * IsingModel.totalMagnetization σ)) h := by
  simp_rw [freeEnergyΛ_apply]
  exact IsingModel.hasDerivAt_freeEnergy_field _ J h β

/-- **HasDerivAt for `partitionFunctionΛ` in β** with explicit
derivative as Boltzmann-weighted Hamiltonian sum. -/
theorem hasDerivAt_partitionFunctionΛ_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun β' => partitionFunctionΛ G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ))
      (∑ σ : IsingModel.Config ↑(Λ : Finset V),
        - IsingModel.hamiltonian (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ *
          IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) β := by
  simp_rw [partitionFunctionΛ_apply]
  exact IsingModel.hasDerivAt_partitionFunction_beta _ J h β

/-- **HasDerivAt for `partitionFunctionΛ` in J** with explicit
derivative as Boltzmann-weighted edge-spin sum. -/
theorem hasDerivAt_partitionFunctionΛ_J (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun J' => partitionFunctionΛ G Λ
        (⟨J', h, β⟩ : IsingParams ℝ))
      (∑ σ : IsingModel.Config ↑(Λ : Finset V),
        β * (∑ e ∈ (inducedGraph G Λ).edgeFinset,
              IsingModel.edgeSpin (K := ℝ) σ e) *
          IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) J := by
  simp_rw [partitionFunctionΛ_apply]
  exact IsingModel.hasDerivAt_partitionFunction_J _ J h β

/-- **HasDerivAt for `partitionFunctionΛ` in h** with explicit
derivative as Boltzmann-weighted total-magnetization sum. -/
theorem hasDerivAt_partitionFunctionΛ_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun h' => partitionFunctionΛ G Λ
        (⟨J, h', β⟩ : IsingParams ℝ))
      (∑ σ : IsingModel.Config ↑(Λ : Finset V),
        β * IsingModel.totalMagnetization σ *
          IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) h := by
  simp_rw [partitionFunctionΛ_apply]
  exact IsingModel.hasDerivAt_partitionFunction_field _ J h β

omit [DecidableEq V] in
/-- **HasDerivAt for ambient-induced Boltzmann weight in β** at a
single configuration `σ : Config ↑Λ`. -/
theorem hasDerivAt_boltzmannWeightΛ_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (σ : IsingModel.Config ↑(Λ : Finset V)) :
    HasDerivAt
      (fun β' => IsingModel.boltzmannWeight (inducedGraph G Λ)
        (⟨J, h, β'⟩ : IsingParams ℝ) σ)
      (- IsingModel.hamiltonian (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ *
         IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) β :=
  IsingModel.hasDerivAt_boltzmannWeight_beta _ J h β σ

omit [DecidableEq V] in
/-- **HasDerivAt for ambient-induced Boltzmann weight in J** at a
single configuration. -/
theorem hasDerivAt_boltzmannWeightΛ_J (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (σ : IsingModel.Config ↑(Λ : Finset V)) :
    HasDerivAt
      (fun J' => IsingModel.boltzmannWeight (inducedGraph G Λ)
        (⟨J', h, β⟩ : IsingParams ℝ) σ)
      (β * (∑ e ∈ (inducedGraph G Λ).edgeFinset,
              IsingModel.edgeSpin (K := ℝ) σ e) *
         IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) J :=
  IsingModel.hasDerivAt_boltzmannWeight_J _ J h β σ

omit [DecidableEq V] in
/-- **HasDerivAt for ambient-induced Boltzmann weight in h** at a
single configuration. -/
theorem hasDerivAt_boltzmannWeightΛ_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (σ : IsingModel.Config ↑(Λ : Finset V)) :
    HasDerivAt
      (fun h' => IsingModel.boltzmannWeight (inducedGraph G Λ)
        (⟨J, h', β⟩ : IsingParams ℝ) σ)
      (β * IsingModel.totalMagnetization σ *
         IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) h :=
  IsingModel.hasDerivAt_boltzmannWeight_field _ J h β σ


end Ambient
end IsingModel
