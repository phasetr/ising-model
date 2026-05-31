import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSConsolidatedSummary
import IsingModel.Inequalities.HighTemp.SusceptibilityFerromagneticAliases

/-!
# Substantive HLS general-exhaustion bundle

GJ-proposition-unit bundle of general-exhaustion versions for the
substantive HLS chain (which were cubic-exhaustion specific).

Uses:
- `susceptibilityInfinite_latticeGraph_le_of_high_temp_gen` for general
  exhaustion susceptibility bound.

**Reference:** Glimm-Jaffe §17.5 / §5.1 / §5.3.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## General-exhaustion susceptibility -/

/-- **Susceptibility bound for ANY exhaustion** (ferromagnetic + strict
high-temp). -/
theorem hls_susceptibility_bound_gen
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) Λ ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  susceptibilityInfinite_latticeGraph_le_of_ferromagnetic_high_temp_gen
    Λ hf hβJd_lt i

/-- **latticeMass > 0 for ANY exhaustion** (ferromagnetic + strict
high-temp). -/
theorem hls_latticeMass_pos_gen
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_high_temp_exhaustion hd Λ hf.hJ hf.hβ hβJ hβJd_lt

/-- **latticeMass > 0 from minimal hypotheses for ANY exhaustion**. -/
theorem hls_latticeMass_pos_gen_minimal
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have hβJ := betaJ_pos_of_betaJd_pos hd hβJd_pos
  exact hls_latticeMass_pos_gen hd Λ hf hβJ hβJd_lt

/-! ## Joint: gen-exhaustion susceptibility + latticeMass -/

/-- **Joint: susceptibility bound + latticeMass > 0 for ANY exhaustion**. -/
theorem hls_susceptibility_and_latticeMass_gen
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (∀ i : Fin d → ℤ,
      susceptibilityInfinite (latticeGraph d) Λ ⟨J, 0, β⟩ i
        ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ∧
    (0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨fun i => hls_susceptibility_bound_gen Λ hf hβJd_lt i,
   hls_latticeMass_pos_gen_minimal hd Λ hf hβJd_pos hβJd_lt⟩

/-! ## Generic accessor: hypotheses helper -/

/-- **`0 < β·J·(2d) ∧ β·J·(2d) < 1` packaging**. -/
theorem high_temp_regime_packaging
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < β * J * (2 * d) ∧ β * J * ↑(2 * d) < 1 :=
  ⟨hβJd_pos, hβJd_lt⟩

/-- **High-temp packaging unpacker** (helper). -/
theorem high_temp_regime_unpack
    {β J : ℝ} {d : ℕ}
    (h : 0 < β * J * (2 * d) ∧ β * J * ↑(2 * d) < 1) :
    0 < β * J * (2 * d) ∧ β * J * ↑(2 * d) < 1 := h

end Ambient
end IsingModel
