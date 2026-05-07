import IsingModel.AmbientLattice.SpontaneousMono

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

/-! ## Trivial free-energy slices along exhaustion -/

/-- **Along-exhaustion β=0 closed form**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ, J, h`,
`freeEnergyAlongExhaustion G Λ ⟨J, h, 0⟩ n = log 2`.

Specialization of `IsingModel.freeEnergy_beta_zero` (PR #131) via
`change` + definitional unfolding of `freeEnergyAlongExhaustion`
through `freeEnergyΛ` to `IsingModel.freeEnergy (inducedGraph …)`. -/
theorem freeEnergyAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) n
      = Real.log 2 := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2
  exact IsingModel.freeEnergy_beta_zero _ J h (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Infinite-volume β=0 closed form**:
under `∀ n, (Λ.volume n).Nonempty`, `freeEnergyInfinite G Λ ⟨J, h, 0⟩ = log 2`
for any `J, h, G, Λ`.

The sequence `n ↦ freeEnergyAlongExhaustion G Λ ⟨J, h, 0⟩ n` is constantly
`log 2` by `freeEnergyAlongExhaustion_beta_zero`, so its `limsup` on
`atTop` is `log 2` by `Filter.limsup_const`.

Sanity check: the β = 0 slice of the §4.6 Prop 4.6.1 infinite-volume
free energy is trivially the maximum-entropy value.

A weakened version requiring only `∀ᶠ n in atTop, (Λ.volume n).Nonempty`
is provided as `freeEnergyInfinite_beta_zero_of_eventually_nonempty`
in `AmbientLatticeSum.lean`. -/
theorem freeEnergyInfinite_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 := by
  unfold freeEnergyInfinite
  have hconst : freeEnergyAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ)
      = fun _ : ℕ => Real.log 2 := by
    funext n
    exact freeEnergyAlongExhaustion_beta_zero G Λ J h n (hne n)
  rw [hconst]
  exact Filter.limsup_const (Real.log 2)

/-- **Along-exhaustion J=h=0 closed form**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ` and any `β`,
`freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n = log 2`.

Specialization of `IsingModel.freeEnergy_zero_params` via `change` +
definitional unfolding of `freeEnergyAlongExhaustion` through
`freeEnergyΛ` to `IsingModel.freeEnergy (inducedGraph …)`. -/
theorem freeEnergyAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2 := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2
  exact IsingModel.freeEnergy_zero_params _ β (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Infinite-volume J=h=0 closed form**:
under `∀ n, (Λ.volume n).Nonempty`, `freeEnergyInfinite G Λ ⟨0, 0, β⟩ = log 2`
for any `β, G, Λ`.

The sequence `n ↦ freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n` is constantly
`log 2` by `freeEnergyAlongExhaustion_zero_params`, so its `limsup` on
`atTop` is `log 2` by `Filter.limsup_const`.

Companion to `freeEnergyInfinite_beta_zero`: both give the
maximum-entropy value `log 2` from orthogonal degeneracies
(β=0 vs. H ≡ 0).

A weakened version requiring only `∀ᶠ n in atTop, (Λ.volume n).Nonempty`
is provided as `freeEnergyInfinite_zero_params_of_eventually_nonempty`
in `AmbientLatticeSum.lean`. -/
theorem freeEnergyInfinite_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
  unfold freeEnergyInfinite
  have hconst : freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = fun _ : ℕ => Real.log 2 := by
    funext n
    exact freeEnergyAlongExhaustion_zero_params G Λ β n (hne n)
  rw [hconst]
  exact Filter.limsup_const (Real.log 2)

/-- **Along-exhaustion J=0 graph-independence**:
`freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n
  = freeEnergyAlongExhaustion ⊥ Λ ⟨0, h, β⟩ n`
for any `n`, any `G, Λ`, any `h, β` (no nonempty hypothesis).

Lift of `IsingModel.freeEnergy_eq_bot_at_J_zero` (PR #175) through
the definitional unfolding
`freeEnergyAlongExhaustion = freeEnergy (inducedGraph …)`:
apply the base identity on both sides to reduce to the same
`freeEnergy_bot` expression. -/
theorem freeEnergyAlongExhaustion_eq_bot_at_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (⊥ : SimpleGraph V) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n))
          (⟨0, h, β⟩ : IsingParams ℝ)
  rw [IsingModel.freeEnergy_eq_bot_at_J_zero (inducedGraph G (Λ.volume n)),
      IsingModel.freeEnergy_eq_bot_at_J_zero
        (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n))]

/-- **Along-exhaustion J=0 closed form (graph-independent)**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ` and any `h, β`,
`freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n = log (2·cosh(β·h))`.

Specialization of `IsingModel.freeEnergy_J_zero` via `change` +
definitional unfolding. -/
theorem freeEnergyAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = Real.log (2 * Real.cosh (β * h)) := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) = _
  exact IsingModel.freeEnergy_J_zero _ h β (Finset.Nonempty.fintype_card_coe_pos hne)

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

/-! ## `h`-symmetry / `|h|` monotonicity along exhaustion -/

/-- **Along-exhaustion h-evenness**:
`freeEnergyAlongExhaustion G Λ ⟨J, -h, β⟩ n = freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, -h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, h, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_neg_h _ J h β

/-- **Along-exhaustion `|h|`-rewrite**:
`freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n = freeEnergyAlongExhaustion G Λ ⟨J, |h|, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, |h|, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_eq_abs_h _ J h β

/-- **Along-exhaustion ferromagnetic `|h|`-monotonicity**:
for `J ≥ 0`, `β > 0` and any real `h₁, h₂` with `|h₁| ≤ |h₂|`,
`freeEnergyAlongExhaustion G Λ ⟨J, h₁, β⟩ n ≤ freeEnergyAlongExhaustion G Λ ⟨J, h₂, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_monotone_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h₁, β⟩ : IsingParams ℝ)
    ≤ IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, h₂, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_monotone_abs_h _ J β hJ hβ hh

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
