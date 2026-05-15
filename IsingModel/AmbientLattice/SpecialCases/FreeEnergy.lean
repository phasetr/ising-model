import IsingModel.AmbientLattice.SpontaneousMono
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyHSymmetry
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyTrivialSlices

/-!
# Non-analytic free-energy special cases

This module contains the special-case free-energy APIs that do not depend on
the analytic cluster-expansion stack: bounded edge density, trivial parameter
slices, basic `h`-symmetry, and uniform exhaustion bounds.

It is split from the legacy `AmbientLattice.SpecialCases` body so modules such
as `AmbientLatticeSum` can use these free-energy facts without importing
`AmbientLattice.Analyticity`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Uniform upper bound under bounded edge density -/

/-- **Bounded edge density along an exhaustion**: there is `c : ℝ` such
that for every `n` with `Λ.volume n` nonempty,
`|E(G[Λ_n])| ≤ c · |Λ_n|`.

Example: bounded-degree ambient graphs with max degree `Δ` satisfy
this with `c = Δ / 2`. -/
def BoundedEdgeDensity (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] : Prop :=
  ∃ c : ℝ, ∀ n, (Λ.volume n).Nonempty →
    ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
      c * Fintype.card (↑(Λ.volume n) : Type _)

/-- **Uniform upper bound on `freeEnergyAlongExhaustion` under bounded
edge density**: if `BoundedEdgeDensity G Λ` with constant `c`, then for
every `n` with `Λ.volume n` nonempty and any Ising parameters `p`,
`freeEnergyAlongExhaustion G Λ p n ≤ log 2 + |β|·(|J|·c + |h|)`.

Direct consequence of `freeEnergyAlongExhaustion_upper_bound` (PR #122)
and the edge-density bound `|E_n|/|Λ_n| ≤ c`. -/
theorem freeEnergyAlongExhaustion_le_uniform_upper_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _))
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ p n ≤
      Real.log 2 + |p.β| * (|p.J| * c + |p.h|) := by
  have hcard_pos : (0 : ℝ) < Fintype.card (↑(Λ.volume n) : Type _) := by
    rw [Fintype.card_coe]; exact_mod_cast Finset.card_pos.mpr hne
  have hratio :
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
        Fintype.card (↑(Λ.volume n) : Type _) ≤ c :=
    (div_le_iff₀ hcard_pos).mpr (hc n hne)
  calc freeEnergyAlongExhaustion G Λ p n
      ≤ Real.log 2 +
          |p.β| * (|p.J| * (inducedGraph G (Λ.volume n)).edgeFinset.card +
              |p.h| * Fintype.card (↑(Λ.volume n) : Type _))
            / Fintype.card (↑(Λ.volume n) : Type _) :=
        freeEnergyAlongExhaustion_upper_bound G Λ p n hne
    _ = Real.log 2 +
          |p.β| * (|p.J| *
              ((inducedGraph G (Λ.volume n)).edgeFinset.card /
                Fintype.card (↑(Λ.volume n) : Type _)) + |p.h|) := by
          field_simp
    _ ≤ Real.log 2 + |p.β| * (|p.J| * c + |p.h|) := by
          gcongr

/-! ## Moved: trivial free-energy slices along exhaustion

The six trivial-parameter-slice closed forms
(`freeEnergyAlongExhaustion_beta_zero`,
`freeEnergyInfinite_beta_zero`,
`freeEnergyAlongExhaustion_zero_params`,
`freeEnergyInfinite_zero_params`,
`freeEnergyAlongExhaustion_eq_bot_at_J_zero`,
`freeEnergyAlongExhaustion_J_zero`) now live in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergyTrivialSlices`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-! ## Sharper high-temperature free-energy upper bounds -/

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

/-! ## Moved: `h`-symmetry / `|h|`-monotonicity wrappers

The three `freeEnergyAlongExhaustion_{neg_h, eq_abs_h, monotone_abs_h}`
wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergyHSymmetry`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-- **BddAbove for `freeEnergyAlongExhaustion` under bounded edge density**:
assuming `BoundedEdgeDensity G Λ`, the range of the exhaustion free energy
is bounded above.

For nonempty stages the bound is `log 2 + |β|·(|J|·c + |h|)` by the
uniform upper bound above; for empty stages the value is
`(Fintype.card ∅)⁻¹ · log 1 = 0`, which is at most the same constant
(after taking its `max` with `0`). -/
theorem BddAbove_freeEnergyAlongExhaustion_range
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ) :
    BddAbove (Set.range (freeEnergyAlongExhaustion G Λ p)) := by
  obtain ⟨c, hc⟩ := hBED
  refine ⟨max 0 (Real.log 2 + |p.β| * (|p.J| * c + |p.h|)), ?_⟩
  rintro y ⟨n, rfl⟩
  by_cases hne : (Λ.volume n).Nonempty
  · exact le_max_of_le_right
      (freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ p hc n hne)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hcard : Fintype.card (↑(Λ.volume n) : Type _) = 0 := by
      rw [Fintype.card_coe, hne]; rfl
    have hfe : freeEnergyAlongExhaustion G Λ p n = 0 := by
      change IsingModel.freeEnergy (inducedGraph G (Λ.volume n)) p = 0
      unfold IsingModel.freeEnergy
      rw [hcard, Nat.cast_zero, inv_zero, zero_mul]
    rw [hfe]; exact le_max_left _ _

end Ambient
end IsingModel
