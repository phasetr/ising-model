import IsingModel.AmbientComplexAnalyticity.HighTempExpansion

/-!
# Volume-uniform `Z_ℂ` lower bound: structural conditional reduction

This module decomposes the volume-uniform complex partition function lower
bound (the `hZ` provider input for the Lemma 17.5.2 capstone, PR #3032) into
two clean structural inputs:

* `VolumeUniformZComplexIdentity` — the complex high-temperature factorization
  `Z_ℂ_{Λ_n}(↑J, 0, β) = 2^|Λ_n| · cosh(β·↑J)^|E_n| · ∑_Γ ∏ tanh(β·↑J)^|P|`
  holds with a *single* radius `r > 0` for every stage `n`.

* `VolumeUniformComplexHTBound` — the right-hand side of the factorization is
  bounded below by some fixed `ε > 0` for every stage `n`.

The conditional theorem
`volume_uniform_hZ_provider_of_HT_bound_and_identity` produces the
volume-uniform `Z_ℂ` lower bound from these two inputs. The per-fixed-volume
identity (PR #3064 / #3066) gives a stage-dependent radius `r_n`; promoting
this to a single `r` independent of `n` requires complex cluster-expansion
convergence (Mayer / Kotecky–Preiss), still the open research-level hard core
for Issue #3054.

## Open inputs

`VolumeUniformZComplexIdentity` and `VolumeUniformComplexHTBound` are recorded
as `Prop`s; their proofs depend on the volume-uniform polymer cluster-expansion
convergence. The current per-stage / per-fixed-volume bounds
(`partitionFunctionComplex_norm_ge_eps_on_closedBall_at_zero_beta_real_J` /
`partitionFunctionComplexAlongExhaustion_norm_ge_eps_on_closedBall_at_zero_beta_real_J`)
match the structural inputs at each fixed stage but with `r_n, ε_n` that may
shrink to zero as `n → ∞`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

open scoped Topology

/-- **Volume-uniform complex high-temperature RHS lower bound** (structural
input for the Lemma 17.5.2 `hZ` provider, Issue #3054): there exist a single
`r > 0` and `ε > 0` such that for *every* exhaustion stage `n`, the
high-temperature polymer-expansion RHS at the stage's induced subgraph is
bounded below by `ε` on the closed complex ball `Metric.closedBall (0 : ℂ) r`.
This is the genuine input requiring complex cluster-expansion convergence
(Mayer / Kotecky–Preiss). -/
def VolumeUniformComplexHTBound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (Ambient.inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) : Prop :=
  ∃ r > 0, ∃ ε > 0, ∀ n : ℕ, ∀ β ∈ Metric.closedBall (0 : ℂ) r,
    ε ≤ ‖(2 : ℂ) ^ (Λ.volume n).card *
        Complex.cosh (β * (J : ℂ)) ^
          (Ambient.inducedGraph G (Λ.volume n)).edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies
              (Ambient.inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Complex.tanh (β * (J : ℂ)) ^ P.card‖

/-- **Volume-uniform `Z_ℂ` identity** (structural input for the Lemma 17.5.2
`hZ` provider, Issue #3054): there exists a single `r > 0` such that for
*every* exhaustion stage `n`, the complex high-temperature polymer expansion
holds for `partitionFunctionComplexAlongExhaustion G Λ (J:ℂ) 0 β n` on the
entire `Metric.closedBall (0 : ℂ) r`. The per-fixed-volume identity (PR #3064 /
#3066) supplies this with a stage-dependent radius; promoting to a single `r`
needs the polymer expansion to converge on a uniform disc (research-level). -/
def VolumeUniformZComplexIdentity
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (Ambient.inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) : Prop :=
  ∃ r > 0, ∀ n : ℕ, ∀ β ∈ Metric.closedBall (0 : ℂ) r,
    Ambient.partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) 0 β n =
      (2 : ℂ) ^ (Λ.volume n).card *
        Complex.cosh (β * (J : ℂ)) ^
          (Ambient.inducedGraph G (Λ.volume n)).edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies
              (Ambient.inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Complex.tanh (β * (J : ℂ)) ^ P.card

/-- **Volume-uniform `hZ` provider via the cluster-expansion route**
(Issue #3054): given the volume-uniform RHS lower bound
`VolumeUniformComplexHTBound G Λ J` and the volume-uniform identity
`VolumeUniformZComplexIdentity G Λ J`, produce a single `r > 0` and `ε > 0`
such that
`ε ≤ ‖partitionFunctionComplexAlongExhaustion G Λ (J:ℂ) 0 β n‖`
for **every** stage `n` and `β ∈ Metric.closedBall (0:ℂ) r`.

The volume-uniform `hZ` provider feeds the Lemma 17.5.2 capstone
`dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound` (PR #3032).
Both structural inputs remain open at the volume-uniform level (research-level
cluster-expansion convergence). -/
theorem volume_uniform_hZ_provider_of_HT_bound_and_identity
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (Ambient.inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ)
    (hHT : VolumeUniformComplexHTBound G Λ J)
    (hid : VolumeUniformZComplexIdentity G Λ J) :
    ∃ r > 0, ∃ ε > 0, ∀ n : ℕ, ∀ β ∈ Metric.closedBall (0 : ℂ) r,
      ε ≤ ‖Ambient.partitionFunctionComplexAlongExhaustion
          G Λ (J : ℂ) 0 β n‖ := by
  obtain ⟨r_HT, hr_HT, ε, hε, h_HT⟩ := hHT
  obtain ⟨r_id, hr_id, h_id⟩ := hid
  set r : ℝ := min r_HT r_id with hr_def
  have hr_pos : 0 < r := lt_min hr_HT hr_id
  have hr_le_HT : r ≤ r_HT := min_le_left _ _
  have hr_le_id : r ≤ r_id := min_le_right _ _
  refine ⟨r, hr_pos, ε, hε, ?_⟩
  intro n β hβ
  have hβ_HT : β ∈ Metric.closedBall (0 : ℂ) r_HT := by
    rw [Metric.mem_closedBall] at hβ ⊢; linarith
  have hβ_id : β ∈ Metric.closedBall (0 : ℂ) r_id := by
    rw [Metric.mem_closedBall] at hβ ⊢; linarith
  rw [h_id n β hβ_id]
  exact h_HT n β hβ_HT

end Ambient
end IsingModel
