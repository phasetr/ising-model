import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Bounds.PerStage
import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplexFreeEnergy

/-!
# ℤ^d compact upper-log and absolute-log free-energy bounds

Part of the split per-stage complex bounds layer for the GJ §4.6 Vitali route.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d compact-field upper normalised-log handoff under bounded edge density**:
if `K` is compact, the exhaustion has bounded edge density, every stage is
nonempty, and `Z_{Λ_n}(h)` is nonzero on `K`, then
`Real.log ‖Z_{Λ_n}(h)‖ / |Λ_n|` has one stage-independent upper bound on `K`.
This is only the upper half of the later normalised absolute-log input. -/
theorem exists_real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (β J : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hZ : ∀ n, ∀ h ∈ K,
      Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n ≠ 0) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C :=
  Ambient.exists_real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_on_isCompact
    (IsingModel.latticeGraph d) Λ hBED β J hK hZ

/-- **ℤ^d stage free-energy bound from a normalised absolute-log bound**:
if `|log ‖Z_{Λ_n}(h)‖| / |Λ_n| ≤ C` at a nonempty stage, then the principal
complex free energy is bounded by `C + π / |Λ_n|`. This records the exact
normalised-log input needed after the compact `Z_ℂ` envelope. -/
theorem norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) [Nonempty (↑(Λ.volume n) : Type _)] {h : ℂ} {C : ℝ}
    (hC :
      |Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ‖Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
      ≤ C + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  Ambient.norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_stage
    (IsingModel.latticeGraph d) Λ β J n hC

/-- **ℤ^d setwise free-energy bound from normalised absolute-log control**:
if one constant `C` bounds `|log ‖Z_{Λ_n}(h)‖| / |Λ_n|` for every stage and
every field in `K`, then the ℤ^d along-exhaustion principal free energies obey
the corresponding stagewise bound on `K`. -/
theorem norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (β J : ℝ) {K : Set ℂ} {C : ℝ}
    (hC : ∀ n, ∀ h ∈ K,
      |Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ∀ n, ∀ h ∈ K,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        ≤ C + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  Ambient.norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set
    (IsingModel.latticeGraph d) Λ β J hC

/-- **ℤ^d stage-independent setwise free-energy bound from normalised
absolute-log control**: if one constant `C` bounds
`|log ‖Z_{Λ_n}(h)‖| / |Λ_n|` for every nonempty stage and every `h ∈ K`, then
the ℤ^d along-exhaustion principal free energies are bounded on `K` by the
single constant `C + π`. -/
theorem norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set_uniform_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (β J : ℝ) {K : Set ℂ} {C : ℝ}
    (hC : ∀ n, ∀ h ∈ K,
      |Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ∀ n, ∀ h ∈ K,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        ≤ C + Real.pi :=
  Ambient.norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set_uniform
    (IsingModel.latticeGraph d) Λ β J hC

end Ambient
end IsingModel
