import IsingModel.AmbientLattice.SpontaneousMono
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyHSymmetry
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyTrivialSlices
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyTrivialSlicesInfinite
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyHighTempExp

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

/-! ## Moved: 2 sharper high-temperature free-energy upper bounds

The two sharper-exp `freeEnergyAlongExhaustion`
high-temperature upper bound wrappers
(`freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp`,
`freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp_uniform`)
now live in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergyHighTempExp`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

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
