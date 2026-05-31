import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSSusceptibilityBridge
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExpDecayMass

/-!
# Substantive HLS ↔ latticeMass joint bundle

GJ-proposition-unit bundle bridging the substantive HLS chain to the
`latticeMass > 0` positivity (`latticeMass_pos_of_high_temp_exhaustion`),
with the final consolidated HLS summary and projections.

The consolidated theorem names previously lived in the standalone
`HLSConsolidatedSummary` module; that wrapper module was retired, while the
public theorem names remain available here and through the top-level
`Lemma_17_5_2` umbrella.

**Reference:** Glimm-Jaffe §17.5 pp. 304-306, Lemma 17.5.2 pp. 311-312.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## latticeMass positivity from substantive setup -/

/-- **`latticeMass > 0` from substantive HLS hypotheses** (ferromagnetic,
strict positive `β·J·(2d)`, strict high-temp). -/
theorem latticeMass_pos_of_substantive_hls_hypotheses
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_high_temp_exhaustion hd Λ hf.hJ hf.hβ hβJ hβJd_lt

/-- **Joint statement: latticeMass > 0 + substantive HLS bound**. -/
theorem latticeMass_pos_and_substantive_hls_bound
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 < latticeMass d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    (∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ))) :=
  ⟨latticeMass_pos_of_substantive_hls_hypotheses hd
    (Ambient.cubicExhaustion d) hf hβJ hβJd_lt,
   hls_substantive_bound hf hβJd_pos hβJd_lt⟩

/-! ## Joint: latticeMass > 0 + cluster property + susceptibility -/

/-- **Joint triplet: latticeMass > 0 + cluster property + susceptibility
bound** (ferromagnetic + strict high-temp). -/
theorem latticeMass_cluster_susceptibility_substantive
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 < latticeMass d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    (∀ i : Fin d → ℤ,
      susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
        ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) :=
  ⟨latticeMass_pos_of_substantive_hls_hypotheses hd
    (Ambient.cubicExhaustion d) hf hβJ hβJd_lt,
   hls_cluster_property hf hβJd_pos hβJd_lt,
   fun i =>
    susceptibilityInfinite_latticeGraph_le_of_ferromagnetic_high_temp
      hf hβJd_lt i⟩

/-! ## Helper: 0 < β·J from substantive hypotheses -/

/-- **`0 < β·J` from `0 < β·J·(2d)`** (helper). -/
theorem betaJ_pos_of_betaJd_pos
    {β J : ℝ} {d : ℕ} (hd_pos : 0 < d)
    (hβJd_pos : 0 < β * J * (2 * d)) :
    0 < β * J := by
  have h2d_pos : (0 : ℝ) < 2 * d := by positivity
  have : β * J = β * J * (2 * d) / (2 * d) := by
    field_simp
  rw [this]
  exact div_pos hβJd_pos h2d_pos

/-- **Substantive HLS witness from minimal hypotheses (without explicit
`0 < β·J`)**. -/
theorem latticeMass_pos_of_substantive_minimal
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have hd_pos : 0 < d := hd
  have hβJ := betaJ_pos_of_betaJd_pos hd_pos hβJd_pos
  exact latticeMass_pos_of_substantive_hls_hypotheses hd Λ hf hβJ hβJd_lt

/-! ## Highest-level consolidated summary -/

/-- **All-in-one substantive HLS conclusions under ferromagnetic strict
high-temp**: returns all substantive conclusions in a single tuple. -/
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
