import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion correlation wrappers at h = 0 (umbrella residue)

Narrow child module for the §18.3 / §18.7 ambient alongExhaustion
correlation wrapper extracted from `HighTemperatureBounds.lean`:

* `correlationAlongExhaustion_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`

It is a pass-through to
`correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`.
The theorem name is unchanged from the former `HighTemperatureBounds`
declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion transport of the project-derived pair lower bound at stage `n`.**
Applies the Λ-level single-edge lower bound at the stage-`n`
subtype `↑(Λ.volume n)`. Along-exhaustion wrapper for
`correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G (Λ.volume n)).edgeSet) :
    Real.tanh (β * J) /
        (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
          ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    G (Λ.volume n) J β hβJ i j hij he

end Ambient
end IsingModel
