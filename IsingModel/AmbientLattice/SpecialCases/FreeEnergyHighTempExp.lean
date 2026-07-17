import IsingModel.AmbientLattice.Exhaustion

/-!
# Sharper high-temperature free-energy upper bound wrappers along an exhaustion

Narrow child module for the two sharper-exp `freeEnergyAlongExhaustion`
high-temperature upper bound wrappers extracted from
`FreeEnergy.lean`:

* `freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp`
* `freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp_uniform`

The pointwise stage-`n` wrapper unfolds `freeEnergyAlongExhaustion`
to the ambient `freeEnergyΛ_high_temp_h_zero_upper_bound_exp`
lemma; the uniform variant combines it with the
`BoundedEdgeDensity` hypothesis to produce a uniform-in-`n` bound.
Theorem names are unchanged from the former `FreeEnergy`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex sharper freeEnergy upper bound at stage `n`**: under
`0 ≤ β·J` and `0 < |Λ_n|`, `f_n(⟨J, 0, β⟩) ≤ log 2 + β·J·|E_n|/|Λ_n|`.
Stage-`n` Λ-level specialization of
`freeEnergy_high_temp_h_zero_upper_bound_exp`. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card := by
  change freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) ≤ _
  exact freeEnergyΛ_high_temp_h_zero_upper_bound_exp
    G (Λ.volume n) J β hβJ hne

/-- **Uniform sharper `f` upper bound under bounded edge density**:
under `0 ≤ β·J`, `BoundedEdgeDensity G Λ` constant `c`, and
`Λ.volume n` nonempty, at every stage `n`
`f_n(⟨J, 0, β⟩) ≤ log 2 + β·J·c`.

Combines `freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp`
(Step 395 along-ex) `f_n ≤ log 2 + β·J·|E_n|/|Λ_n|` with the edge
density bound `|E_n|/|Λ_n| ≤ c` to get a uniform-in-`n` bound. The
asymptotic `c → d` for the ℤ^d cubic exhaustion (with `c = d`) makes
this a clean per-stage bound that survives `lim sup` to the
infinite-volume limit. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp_uniform
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _))
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 + β * J * c := by
  have hcard_pos : 0 < (Λ.volume n).card := hne.card_pos
  have hcard_pos_real : (0 : ℝ) < ((Λ.volume n).card : ℝ) := by
    exact_mod_cast hcard_pos
  have hcard_eq :
      (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) = ((Λ.volume n).card : ℝ) := by
    rw [Fintype.card_coe]
  have h_step1 := freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp
    G Λ J β hβJ n hcard_pos
  have h_edge_le : β * J *
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card ≤ β * J * c := by
    have hbound := hc n hne
    rw [hcard_eq] at hbound
    have h_edgeRatio :
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            ((Λ.volume n).card : ℝ) ≤ c := by
      rw [div_le_iff₀ hcard_pos_real]
      linarith
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h_edgeRatio hβJ
  linarith

end Ambient
end IsingModel
