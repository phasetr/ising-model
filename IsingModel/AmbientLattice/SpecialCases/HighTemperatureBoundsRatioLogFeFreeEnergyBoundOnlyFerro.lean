import IsingModel.AmbientLattice.Exhaustion

/-!
# Upper bounds on the free-energy difference under `0 ≤ J` and `0 < β`

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume. The difference taken is the free energy at `⟨J, 0, β⟩` minus its value at one
of the trivial slices `⟨0, 0, β⟩` and `⟨J, 0, 0⟩`.

Under `0 ≤ J`, `0 < β` and `0 < |Λ|`, each of those two differences is at most
`β * J * |E| / |Λ|`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic f ratio bound at J=0**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card := by
  change freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ) ≤ _
  exact freeEnergyΛ_high_temp_h_zero_ratio_bound
    G (Λ.volume n) J β (mul_nonneg hβ.le hJ) hne

/-- **Along-ex ferromagnetic f ratio bound at β=0**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card := by
  change freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyΛ G (Λ.volume n) (⟨J, 0, 0⟩ : IsingParams ℝ) ≤ _
  exact freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero
    G (Λ.volume n) J β (mul_nonneg hβ.le hJ) hne

end Ambient

end IsingModel
