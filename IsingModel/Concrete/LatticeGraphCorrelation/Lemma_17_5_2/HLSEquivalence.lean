import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSExistentialWrappers

/-!
# Substantive HLS equivalence bundle

GJ-proposition-unit bundle of equivalences between different forms of the
substantive HLS chain entry points.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Equivalence wrappers -/

/-- **`hls_sum_bound` ↔ `hls_main_substantive_betaJ_pos`** are alpha-equivalent. -/
theorem hls_sum_bound_eq_hls_main_substantive_betaJ_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    hls_sum_bound hd hf hβJ hβJd_lt
      = hls_main_substantive_betaJ_pos hd hf hβJ hβJd_lt :=
  rfl

/-- **Trivial: `hls_cluster` ↔ `hls_main_cluster_betaJ_pos`**. -/
theorem hls_cluster_eq_hls_main_cluster
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    hls_cluster hd hf hβJ hβJd_lt
      = hls_main_cluster_betaJ_pos hd hf hβJ hβJd_lt :=
  rfl

/-- **Trivial: `hls_latticeMass` ↔ `hls_main_latticeMass_pos_betaJ_pos`**. -/
theorem hls_latticeMass_eq_hls_main_latticeMass
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    hls_latticeMass hd hf hβJ hβJd_lt
      = hls_main_latticeMass_pos_betaJ_pos hd hf hβJ hβJd_lt :=
  rfl

/-- **Trivial: `hls_hasExpDecay` ↔ `hls_main_hasExpDecay_betaJ_pos`**. -/
theorem hls_hasExpDecay_eq_hls_main_hasExpDecay
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    hls_hasExpDecay hd hf hβJ hβJd_lt
      = hls_main_hasExpDecay_betaJ_pos hd hf hβJ hβJd_lt :=
  rfl

/-- **Trivial: `hls_susc` ↔ `hls_main_susceptibility_betaJ_pos`**. -/
theorem hls_susc_eq_hls_main_susceptibility
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    hls_susc hd hf hβJ hβJd_lt i
      = hls_main_susceptibility_betaJ_pos hd hf hβJ hβJd_lt i :=
  rfl

end Ambient
end IsingModel
