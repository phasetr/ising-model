import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSSubstantiveCanonicalSummary
import IsingModel.Inequalities.HighTemp.Susceptibility

/-!
# Substantive HLS ↔ susceptibility bridge bundle

GJ-proposition-unit bundle bridging the substantive HLS sum bound (#3199, #3202)
to the susceptibility infinite-volume bound (#3196).

Both establish high-temperature bounds in different forms:
- Substantive HLS: `∑_z corr·corr ≤ K·exp(-M·dist)`
- Susceptibility: `χ_∞(i) ≤ β·J·2d/(1-β·J·2d)`

**Reference:** Glimm-Jaffe §17.5 Lemma 17.5.2 / §5.1 / §5.3.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Joint witness from substantive HLS + susceptibility -/

/-- **Joint witness: substantive HLS bound + susceptibility bound** under
ferromagnetic + strict high-temp. -/
theorem hls_and_susceptibility_bound_of_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ))) ∧
    (∀ i : Fin d → ℤ,
      susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
        ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) :=
  ⟨hls_substantive_bound hf hβJd_pos hβJd_lt,
   fun i =>
    susceptibilityInfinite_latticeGraph_le_of_ferromagnetic_high_temp
      hf hβJd_lt i⟩

/-! ## Susceptibility bound from canonical entry -/

/-- **Canonical susceptibility bound** (ferromagnetic + strict high-temp). -/
theorem hls_susceptibility_bound
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  susceptibilityInfinite_latticeGraph_le_of_ferromagnetic_high_temp
    hf hβJd_lt i

/-- **Canonical susceptibility bound denominator positivity** helper. -/
theorem hls_susceptibility_denom_pos
    {β J : ℝ} {d : ℕ}
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) < 1 - β * J * ↑(2 * d) := by linarith

/-- **Canonical susceptibility bound numerator nonneg** helper. -/
theorem hls_susceptibility_numer_nonneg
    {β J : ℝ} {d : ℕ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    (0 : ℝ) ≤ β * J * ↑(2 * d) :=
  mul_nonneg (mul_nonneg hf.hβ.le hf.hJ) (by positivity)

/-! ## Joint canonical witness -/

/-- **Existential joint witness `K ≥ 0`, `M > 0`, `S < ∞` under ferromagnetic
high-temp**. -/
theorem exists_K_M_S_substantive_hls_susceptibility
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M S : ℝ, 0 ≤ K ∧ 0 < M ∧ 0 ≤ S := by
  obtain ⟨K, M, hK_nn, hM_pos, _⟩ := hls_substantive_bound hf hβJd_pos hβJd_lt
  refine ⟨K, M, β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)),
          hK_nn, hM_pos, ?_⟩
  apply div_nonneg (hls_susceptibility_numer_nonneg hf)
  linarith

/-! ## Cluster property + susceptibility joint statement -/

/-- **Joint cluster property + susceptibility bound** (ferromagnetic +
strict high-temp). -/
theorem hls_cluster_and_susceptibility
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    (∀ i : Fin d → ℤ,
      susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
        ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) :=
  ⟨hls_cluster_property hf hβJd_pos hβJd_lt,
   fun i =>
    susceptibilityInfinite_latticeGraph_le_of_ferromagnetic_high_temp
      hf hβJd_lt i⟩

end Ambient
end IsingModel
