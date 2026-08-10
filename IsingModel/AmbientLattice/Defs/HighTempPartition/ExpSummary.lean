import IsingModel.AmbientLattice.Defs.HighTempPartition.ExpBounds

/-!
# Λ-restricted high-temperature summaries at zero external field

Single-statement bundles for `partitionFunctionΛ`, for its logarithm and for `freeEnergyΛ`,
for an arbitrary `G : SimpleGraph V` and an arbitrary finite volume `Λ : Finset V`. Each
bundle is one conjunction whose parts are a lower bound, an upper bound, and the two values
the quantity takes on the degenerate slices `J = 0` and `β = 0`. The external field is zero
throughout: the parameter records occurring are `⟨J, 0, β⟩`, `⟨0, 0, β⟩` and `⟨J, 0, 0⟩`.

Written with the number of edges of `inducedGraph G Λ`, the subgraph of `G` that `Λ`
induces, the lower bounds are the hyperbolic-cosine ones and the upper bounds the
exponential ones. The partition function lies between `2 ^ Λ.card` times `cosh (β * J)`
raised to that edge count and `2 ^ Λ.card` times `exp (β * J * edge count)`; its logarithm
lies between `Λ.card * log 2` plus the edge count times `log (cosh (β * J))` and
`Λ.card * log 2` plus `β * J` times the edge count; the free energy lies between `log 2`
plus the edge count over `Λ.card` times `log (cosh (β * J))` and `log 2` plus `β * J` times
the edge count over `Λ.card`.

On the two slices the recorded values agree with one another and involve neither `J` nor
`β`: the partition function is `2 ^ Λ.card` on both, its logarithm is `Λ.card * log 2` on
both, and the free energy is `log 2` on both.

Each bundle comes in two forms, one assuming `0 ≤ β * J` and one assuming `0 ≤ J` together
with `0 < β`. The two free-energy bundles additionally assume `0 < Λ.card`; the partition
function and logarithm bundles do not. Every statement takes `[DecidableEq V]` and
`[Fintype (inducedGraph G Λ).edgeSet]`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Λ-level sharper f complete-summary exp bundle**: under `0 < |Λ|`,
`0 ≤ β·J`, single statement bundling sharper sandwich + trivial-slice
values at the Λ-layer. -/
theorem freeEnergyΛ_high_temp_h_zero_complete_summary_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card ∧
    freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
    freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  obtain ⟨h1, h2⟩ := freeEnergyΛ_high_temp_h_zero_sandwich_exp
    G Λ J β hβJ hne
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [freeEnergyΛ_apply]
    have := IsingModel.freeEnergy_J_zero (inducedGraph G Λ) (0 : ℝ) β hcard
    simpa [mul_zero, Real.cosh_zero] using this
  · rw [freeEnergyΛ_apply]
    exact IsingModel.freeEnergy_beta_zero (inducedGraph G Λ) J 0 hcard

/-- **Λ-level sharper Z complete-summary exp bundle**: under `0 ≤ β·J`,
single statement bundling sharper sandwich + trivial-slice values. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card := by
  obtain ⟨h1, h2⟩ := partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    G Λ J β hβJ
  exact ⟨h1, h2,
    partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero G Λ β,
    partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero G Λ J⟩

/-- **Λ-level sharper log Z complete-summary exp bundle**: under
`0 ≤ β·J`, single statement bundling sharper sandwich + trivial-slice
values. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (Λ.card : ℝ) * Real.log 2
        + ((inducedGraph G Λ).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ (Λ.card : ℝ) * Real.log 2
        + β * J * (inducedGraph G Λ).edgeFinset.card ∧
    Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 := by
  obtain ⟨h1, h2⟩ := log_partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    G Λ J β hβJ
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero,
        Real.log_pow]
  · rw [partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero,
        Real.log_pow]

/-- **Λ-level ferromagnetic Z complete-summary exp bundle**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level ferromagnetic log Z complete-summary exp bundle**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (Λ.card : ℝ) * Real.log 2
        + ((inducedGraph G Λ).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ (Λ.card : ℝ) * Real.log 2
        + β * J * (inducedGraph G Λ).edgeFinset.card ∧
    Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level ferromagnetic f complete-summary exp bundle**. -/
theorem freeEnergyΛ_high_temp_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card ∧
    freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
    freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  freeEnergyΛ_high_temp_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ) hne

end Ambient

end IsingModel
