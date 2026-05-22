import IsingModel.AmbientLattice.Defs.Core

/-!
# Ambient lattice correlation and magnetization bounds

General correlation and magnetization wrappers at the ambient finite-volume
layer.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- The correlation on `Λ` is bounded: `|⟨σ^A⟩| ≤ 1`. -/
theorem abs_correlationΛ_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    |correlationΛ G Λ p A| ≤ 1 :=
  IsingModel.abs_correlation_le_one _ _ _

/-- The correlation on `Λ` is at most `1`. -/
theorem correlationΛ_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ G Λ p A ≤ 1 :=
  IsingModel.correlation_le_one _ _ _

/-- The correlation on `Λ` is at least `-1`. Lower side of
`abs_correlationΛ_le_one`. -/
theorem neg_one_le_correlationΛ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    -1 ≤ correlationΛ G Λ p A :=
  (abs_le.mp (abs_correlationΛ_le_one G Λ p A)).1

/-- **`correlationΛ² ≤ 1`** unconditionally. -/
theorem correlationΛ_sq_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ G Λ p A ^ 2 ≤ 1 :=
  IsingModel.correlation_sq_le_one _ p A

/-- For ferromagnetic `p`, the correlation on `Λ` is non-negative
(GKS-I, lifted to the ambient framework). -/
theorem correlationΛ_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (A : Finset (↑Λ : Type _)) :
    0 ≤ correlationΛ G Λ p A :=
  gks_first _ _ hf _

/-- **Unfolding of `magnetizationΛ`**:
`magnetizationΛ G Λ p i = correlationΛ G Λ p {i}`, by definition. -/
theorem magnetizationΛ_apply (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (i : ↑Λ) :
    magnetizationΛ G Λ p i = correlationΛ G Λ p {i} := rfl

/-- **`magnetizationΛ ≤ 1`** at any site `i : ↑Λ`, for any parameters.
Direct from `correlationΛ_le_one` at `A = {i}`. -/
theorem magnetizationΛ_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) (i : ↑Λ) :
    magnetizationΛ G Λ p i ≤ 1 :=
  correlationΛ_le_one G Λ p {i}

/-- **`|magnetizationΛ| ≤ 1`** at any site `i : ↑Λ`, for any parameters.
Direct from `abs_correlationΛ_le_one` at `A = {i}`. -/
theorem abs_magnetizationΛ_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) (i : ↑Λ) :
    |magnetizationΛ G Λ p i| ≤ 1 :=
  abs_correlationΛ_le_one G Λ p {i}

/-- **`-1 ≤ magnetizationΛ`** at any site `i : ↑Λ`, for any parameters. -/
theorem neg_one_le_magnetizationΛ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) (i : ↑Λ) :
    -1 ≤ magnetizationΛ G Λ p i :=
  neg_one_le_correlationΛ G Λ p {i}

/-- **`magnetizationΛ² ≤ 1`** unconditionally. From
`abs_magnetizationΛ_le_one` via `sq_le_one'`. -/
theorem magnetizationΛ_sq_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) (i : ↑Λ) :
    magnetizationΛ G Λ p i ^ 2 ≤ 1 := by
  have h := abs_magnetizationΛ_le_one G Λ p i
  have : |magnetizationΛ G Λ p i| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **`magnetizationΛ ≥ 0`** for ferromagnetic `p` at any site `i : ↑Λ`.
Direct from `correlationΛ_nonneg` at `A = {i}` (GKS-I). -/
theorem magnetizationΛ_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (i : ↑Λ) :
    0 ≤ magnetizationΛ G Λ p i :=
  correlationΛ_nonneg G Λ p hf {i}

end Ambient

end IsingModel
