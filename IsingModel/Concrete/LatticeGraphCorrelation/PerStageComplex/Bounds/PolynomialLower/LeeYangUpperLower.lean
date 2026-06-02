import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Bounds.UpperLog

/-!
# ℤ^d Lee-Yang upper and lower-log handoff bounds

Part of the split polynomial-witness lower-log and local boundedness layer.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d compact-field upper normalised-log bound on Lee-Yang compact sets**:
on compact subsets of `leeYangDomain`, Lee-Yang nonvanishing discharges the
nonzero hypothesis in the compact upper normalised-log handoff. -/
theorem exists_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_ly_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C :=
  Ambient.exists_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_leeYangDomain
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hK hKsub

/-- **ℤ^d Lee-Yang compact absolute normalised-log handoff from lower control**:
on compact `K ⊆ leeYangDomain`, the Lee-Yang upper normalised-log bound and a
stage-uniform lower normalised-log hypothesis yield the absolute normalised-log
control consumed by the free-energy bounds. -/
theorem exists_abs_log_norm_div_card_le_lower_ly_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hLower : ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      |Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C :=
  Ambient.exists_abs_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_lower_leeYang
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hK hKsub hLower

/-- **ℤ^d Lee-Yang compact locally bounded free-energy family from lower
control**: on compact `K ⊆ leeYangDomain`, a stage-uniform lower
normalised-log hypothesis combines with the Lee-Yang upper bound to give one
constant `C` with `‖f_n(h)‖ ≤ C + π` for all stages and all `h ∈ K`. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_lower_log_ly_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hLower : ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_lower_log_leeYang
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hK hKsub hLower

end Ambient
end IsingModel
