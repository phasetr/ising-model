import IsingModel.AmbientLattice.Exhaustion

/-!
# High-temperature upper bounds on the stage free energy at zero external field

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V`, the stagewise `Fintype` instance on that subgraph's edge set, and the
hypothesis `0 ≤ β * J`.

At the zero-field triple `⟨J, 0, β⟩` and a stage whose volume has positive cardinality, the
stage free energy is at most `Real.log 2 + β * J * |E| / |Λ.volume n|`, writing `|E|` for the
edge count of the stage subgraph.

Adding a constant `c : ℝ` that bounds `|E|` by `c * |Λ.volume n|` at every stage with nonempty
volume gives, at each such stage, the bound `Real.log 2 + β * J * c`, whose right-hand side is
determined by `β`, `J` and `c` alone. It follows by bounding the edge ratio by `c` and
multiplying by the nonnegative factor `β * J`.
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
