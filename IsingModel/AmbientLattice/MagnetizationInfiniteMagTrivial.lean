import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.MagnetizationInfiniteLambdaHSymmetry
import IsingModel.AmbientLattice.MagnetizationInfiniteExhaustionHSymmetry
import IsingModel.AmbientLattice.MagnetizationInfiniteHZeroJZero
import IsingModel.AmbientLattice.MagnetizationInfiniteEmptyTrivial

/-!
# Ambient magnetizationΛ / magnetizationAlongExhaustion trivial-slice wrappers

Narrow child module for the magnetizationΛ /
magnetizationAlongExhaustion trivial-slice wrappers (7 theorems):
`magnetizationΛ_beta_zero`, `magnetizationAlongExhaustion_beta_zero`,
`magnetizationΛ_zero_params`,
`magnetizationAlongExhaustion_zero_params`, `magnetizationΛ_J_zero`,
`magnetizationAlongExhaustion_J_zero_of_mem`,
`magnetizationAlongExhaustion_J_zero_eventually_eq`. The theorem
names are unchanged from the former `MagnetizationInfinite`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **`magnetizationΛ` vanishes at `β = 0`**: for any `J, h`, any site
`i : ↑Λ`, `magnetizationΛ G Λ ⟨J, h, 0⟩ i = 0`. Specialization of
`correlationΛ_beta_zero_vanish_of_nonempty` at the nonempty singleton
`{i}`. -/
theorem magnetizationΛ_beta_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) (i : ↑Λ) :
    magnetizationΛ G Λ (⟨J, h, 0⟩ : IsingParams ℝ) i = 0 :=
  correlationΛ_beta_zero_vanish_of_nonempty G Λ J h {i}
    (Finset.singleton_nonempty i)

/-- **`magnetizationAlongExhaustion` vanishes at `β = 0`** per stage:
for any `J, h`, any site `i : V`, and any `n`,
`magnetizationAlongExhaustion G Λ ⟨J, h, 0⟩ i n = 0`. Specialization
of `correlationAlongExhaustion_beta_zero_vanish` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) i n = 0 :=
  correlationAlongExhaustion_beta_zero_vanish G Λ J h {i}
    (Finset.singleton_nonempty i) n

/-- **`magnetizationΛ` vanishes at `J = h = 0`**: for any `β`, any site
`i : ↑Λ`, `magnetizationΛ G Λ ⟨0, 0, β⟩ i = 0`. Specialization of
`correlationΛ_zero_params_vanish_of_nonempty`. -/
theorem magnetizationΛ_zero_params (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (i : ↑Λ) :
    magnetizationΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) i = 0 :=
  correlationΛ_zero_params_vanish_of_nonempty G Λ β {i}
    (Finset.singleton_nonempty i)

/-- **`magnetizationAlongExhaustion` vanishes at `J = h = 0`** per stage. -/
theorem magnetizationAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) i n = 0 :=
  correlationAlongExhaustion_zero_params_vanish G Λ β {i}
    (Finset.singleton_nonempty i) n

/-- **`magnetizationΛ` closed form at `J = 0`**: for any `h, β` and any
site `i : ↑Λ`, `magnetizationΛ G Λ ⟨0, h, β⟩ i = tanh(β·h)`.
Direct lift of `IsingModel.correlation_J_zero` on the induced subgraph
at `A = {i}`, with `Finset.card_singleton` reducing `A.card = 1`. -/
theorem magnetizationΛ_J_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) (i : ↑Λ) :
    magnetizationΛ G Λ (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) := by
  change IsingModel.correlation (inducedGraph G Λ)
      (⟨0, h, β⟩ : IsingParams ℝ) {i} = _
  rw [IsingModel.correlation_J_zero, Finset.card_singleton, pow_one]

/-- **`magnetizationAlongExhaustion` closed form at `J = 0`** per stage
(on-stage): if `i ∈ Λ.volume n`, then
`magnetizationAlongExhaustion G Λ ⟨0, h, β⟩ i n = tanh(β·h)`.
Specialization of `correlationAlongExhaustion_J_zero_of_subset` at
`A = {i}`, with `{i} ⊆ Λ.volume n ↔ i ∈ Λ.volume n`. -/
theorem magnetizationAlongExhaustion_J_zero_of_mem
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) {i : V} {n : ℕ} (hi : i ∈ Λ.volume n) :
    magnetizationAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) i n
      = Real.tanh (β * h) := by
  have : ({i} : Finset V) ⊆ Λ.volume n := Finset.singleton_subset_iff.mpr hi
  have := correlationAlongExhaustion_J_zero_of_subset G Λ h β this
  rw [magnetizationAlongExhaustion_apply, this, Finset.card_singleton, pow_one]

/-- **`magnetizationAlongExhaustion` is eventually `tanh(β·h)` at `J = 0`**.
Immediate from `Exhaustion.exhaust` applied to `{i}` and
`magnetizationAlongExhaustion_J_zero_of_mem`. -/
theorem magnetizationAlongExhaustion_J_zero_eventually_eq
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (i : V) :
    ∀ᶠ n in Filter.atTop,
      magnetizationAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) i n
        = Real.tanh (β * h) := by
  obtain ⟨N, hN⟩ := Λ.exhaust {i}
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  exact magnetizationAlongExhaustion_J_zero_of_mem G Λ h β
    (Finset.singleton_subset_iff.mp (hN n hn))


end Ambient

end IsingModel
