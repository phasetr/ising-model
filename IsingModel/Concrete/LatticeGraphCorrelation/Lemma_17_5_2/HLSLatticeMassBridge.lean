import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSSusceptibilityBridge
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExpDecayMass

/-!
# Substantive HLS ↔ latticeMass joint bundle

GJ-proposition-unit bundle bridging the substantive HLS chain to the
`latticeMass > 0` positivity (`latticeMass_pos_of_high_temp_exhaustion`).

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

end Ambient
end IsingModel
