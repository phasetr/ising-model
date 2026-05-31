import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMaster

/-!
# Substantive HLS ferromag aliases bundle

GJ-proposition-unit bundle providing ferromag-hypothesis-focused alias
combinations.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Ferromag-focused aliases -/

/-- **Ferromag forwarded directly**. -/
theorem hls_ferromag_forward
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) :=
  hf

/-- **Ferromag implies J ≥ 0**. -/
theorem hls_ferromag_implies_J_nonneg
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 ≤ J :=
  hf.hJ

/-- **Ferromag implies β > 0**. -/
theorem hls_ferromag_implies_beta_pos
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 < β :=
  hf.hβ

/-- **Ferromag + βJ > 0 implies cluster**. -/
theorem hls_ferromag_implies_cluster
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  hls_master_cluster hd hf hβJ hβJd_lt

/-- **Ferromag-bundled full HLS pack**. -/
theorem hls_ferromag_full_pack
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) ∧
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    (0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨hf, hls_master_cluster hd hf hβJ hβJd_lt, hls_master_mass hd hf hβJ hβJd_lt⟩

/-- **Ferromag implies non-negative correlation** (one-pair version). -/
theorem hls_ferromag_correlation_nonneg
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (A : Finset (Fin d → ℤ)) :
    0 ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) A :=
  Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf A

end Ambient
end IsingModel
