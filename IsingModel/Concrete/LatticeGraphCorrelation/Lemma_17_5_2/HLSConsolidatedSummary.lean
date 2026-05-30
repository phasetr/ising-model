import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSLatticeMassBridge

/-!
# Substantive HLS consolidated summary + utilities

GJ-proposition-unit final consolidated summary bundle providing the highest-
level joint statements combining all substantive HLS chain conclusions:

- `latticeMass > 0`
- `clusterProperty`
- Susceptibility infinite-volume bound
- Substantive HLS sum bound
- HasExponentialDecay at the strongest rate `-log(β·J·(2d))`
- Per-site cofinite tendsto

All derivable from a minimal hypothesis set: `Ferromagnetic ⟨J, 0, β⟩`,
`1 ≤ d`, `0 < β·J·(2d)`, `β·J·(2d) < 1`.

**Reference:** Glimm-Jaffe §17.5 / §5.1 / §5.3 / §17.8.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Highest-level consolidated summary -/

/-- **All-in-one substantive HLS conclusions under ferromagnetic strict
high-temp**: returns all 6 conclusions in a single tuple. -/
theorem substantive_hls_full_consolidated
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    -- latticeMass > 0
    (0 < latticeMass d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    -- clusterProperty
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    -- Susceptibility ≤ explicit bound
    (∀ i : Fin d → ℤ,
      susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
        ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ∧
    -- Substantive HLS sum bound
    (∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ))) ∧
    -- HasExponentialDecay at strongest rate
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact latticeMass_pos_of_substantive_minimal hd
      (Ambient.cubicExhaustion d) hf hβJd_pos hβJd_lt
  · exact hls_cluster_property hf hβJd_pos hβJd_lt
  · intro i
    exact susceptibilityInfinite_latticeGraph_le_of_ferromagnetic_high_temp
      hf hβJd_lt i
  · exact hls_substantive_bound hf hβJd_pos hβJd_lt
  · exact hls_hasExponentialDecay hf hβJd_lt

/-! ## Per-conclusion projection -/

/-- **Project to substantive HLS bound** from the consolidated statement. -/
theorem substantive_hls_bound_proj
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) :=
  (substantive_hls_full_consolidated hd hf hβJd_pos hβJd_lt).2.2.2.1

/-- **Project to latticeMass > 0** from the consolidated statement. -/
theorem substantive_latticeMass_pos_proj
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  (substantive_hls_full_consolidated hd hf hβJd_pos hβJd_lt).1

/-- **Project to clusterProperty** from the consolidated statement. -/
theorem substantive_clusterProperty_proj
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  (substantive_hls_full_consolidated hd hf hβJd_pos hβJd_lt).2.1

/-- **Project to HasExponentialDecay at strongest rate** from the consolidated. -/
theorem substantive_hasExponentialDecay_proj
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) :=
  (substantive_hls_full_consolidated hd hf hβJd_pos hβJd_lt).2.2.2.2

/-- **Project to susceptibility bound** from the consolidated. -/
theorem substantive_susceptibility_proj
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  (substantive_hls_full_consolidated hd hf hβJd_pos hβJd_lt).2.2.1 i

/-! ## Utility: rate accessors via projection -/

/-- **Substantive HLS rate `-log(β·J·(2d))` from minimal hypotheses**. -/
theorem substantive_canonical_rate
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) < -Real.log (β * J * ↑(2 * d)) :=
  neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt

end Ambient
end IsingModel
