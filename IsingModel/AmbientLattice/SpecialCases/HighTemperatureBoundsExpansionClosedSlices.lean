import IsingModel.AmbientLattice.Exhaustion

/-!
# The zero-field partition function at the trivial parameter slices

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|Λ|` for the cardinality of the stage volume.

At the parameter record `⟨0, 0, β⟩` for arbitrary `β`, and at `⟨J, 0, 0⟩` for arbitrary `J`,
the partition function of the stage volume equals `2 ^ |Λ|`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion FV (3.45) at `J = 0` consistency check**:
`Z_n(⟨0, 0, β⟩) = 2^|Λ_n|`. Per-stage Step 314 abstract. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunctionΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ) = _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero
    G (Λ.volume n) β

/-- **Along-exhaustion FV (3.45) at `β = 0` consistency check**:
`Z_n(⟨J, 0, 0⟩) = 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (J : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunctionΛ G (Λ.volume n) (⟨J, 0, 0⟩ : IsingParams ℝ) = _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero
    G (Λ.volume n) J

end Ambient

end IsingModel
