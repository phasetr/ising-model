import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasic
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingleton

/-!
# Ambient alongExhaustion correlation wrappers at h = 0 (umbrella residue)

Narrow child module for the two §18.3 / §18.7 ambient alongExhaustion
correlation wrappers extracted from `HighTemperatureBounds.lean`:

* `correlationAlongExhaustion_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`
* `correlationAlongExhaustion_high_temp_h_zero_at_singleton_ferromagnetic`

The first is a pass-through to
`correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`; the
second is a thin ferromagnetic specialization of the parent
`correlationAlongExhaustion_high_temp_h_zero_at_singleton` (which
lives in
`HighTemperatureBoundsCorrelationBasicSingleton.lean`). Theorem
names are unchanged from the former `HighTemperatureBounds`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex pair correlation single-edge tanh lower bound at stage `n` (GJ §18.3 / FV (3.46))**:
applies the Λ-level single-edge lower bound at the stage-`n`
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

/-- **Along-ex singleton ferromagnetic vanish at h = 0**: under
`0 ≤ J, 0 < β`, `correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i} n = 0`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (_hJ : 0 ≤ J) (_hβ : 0 < β) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n

end Ambient
end IsingModel
