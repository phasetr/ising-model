import IsingModel.AmbientLattice.Exhaustion

/-!
# Closed forms, field symmetry and monotonicity for the logarithm of the partition function

`partitionFunctionΛ G Λ p` is the partition function of the subgraph that a finite volume
`Λ : Finset V` induces in an arbitrary ambient graph `G : SimpleGraph V`, and
`partitionFunctionAlongExhaustion G Λ p` reads it at the stage volume `Λ.volume n` of an
exhaustion; every statement here is about `Real.log` of one of those two. No statement
assumes `Ferromagnetic p` as a bundle or requires a volume to be nonempty, and the only
instance binders are `[DecidableEq V]` and a `Fintype` instance on the induced edge set,
taken on the volume itself at the finite-volume layer and stagewise at the exhaustion layer.

Two closed forms are recorded, and they stand at the finite-volume layer only, with no
counterpart along an exhaustion in this module: at `J = 0` the value is
`↑Λ.card * log (2 * cosh (β * h))`, and at `β = 0` it is `↑Λ.card * log 2`. Both hold for an
arbitrary finite volume, the empty one included, where each side is `0`.

The remaining shapes stand at both layers. Negating the field leaves the value unchanged, so
it may be rewritten with `|h|` in place of `h`, and those two carry no hypothesis on the
parameters. The monotonicity statements carry their sign conditions singly rather than
through `Ferromagnetic`: in the coupling under `0 ≤ h`, `0 < β`, `0 ≤ J₁` and `J₁ ≤ J₂`; in
the field under `0 ≤ J`, `0 < β`, `0 ≤ h₁` and `h₁ ≤ h₂`; in the inverse temperature under
`0 ≤ J`, `0 ≤ h`, `0 < β₁` and `β₁ ≤ β₂`; and in `|h|` under `0 ≤ J`, `0 < β` and
`|h₁| ≤ |h₂|`, which asks nothing of the signs of `h₁` and `h₂`.
-/

namespace IsingModel

open Finset
open Ambient

variable {V : Type*} [DecidableEq V]

/-- **Closed form for `log (partitionFunctionΛ G Λ ⟨0, h, β⟩)`**:
at `J = 0`, `log Z_Λ = |Λ| · log(2 · cosh(β · h))`.

Direct from `IsingModel.partitionFunction_J_zero`
(`Z = (2·cosh(β·h))^|ι|`) via `Real.log_pow` and `Fintype.card_coe`. -/
theorem log_partitionFunctionΛ_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) :
    Real.log (partitionFunctionΛ G Λ (⟨0, h, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log (2 * Real.cosh (β * h)) := by
  change Real.log (IsingModel.partitionFunction
      (inducedGraph G Λ) (⟨0, h, β⟩ : IsingParams ℝ)) = _
  rw [IsingModel.partitionFunction_J_zero, Real.log_pow, Fintype.card_coe]

/-- **Closed form for `log (partitionFunctionΛ G Λ ⟨J, h, 0⟩)`**:
at `β = 0`, `log Z_Λ = |Λ| · log 2`.

Direct from `IsingModel.partitionFunction_beta_zero`
(`Z = Fintype.card (Config ↑Λ) = 2^|↑Λ|`) via
`card_config_eq_two_pow`, `Real.log_pow`, and `Fintype.card_coe`. -/
theorem log_partitionFunctionΛ_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    Real.log (partitionFunctionΛ G Λ (⟨J, h, 0⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 := by
  change Real.log (IsingModel.partitionFunction
      (inducedGraph G Λ) (⟨J, h, 0⟩ : IsingParams ℝ)) = _
  rw [IsingModel.partitionFunction_beta_zero,
      IsingModel.card_config_eq_two_pow]
  push_cast
  rw [Real.log_pow, Fintype.card_coe]

/-- **Log form of Λ-level h-evenness**:
`log Z_Λ(J, -h, β) = log Z_Λ(J, h, β)`. Direct from
`partitionFunctionΛ_neg_h` by applying `Real.log`. -/
theorem log_partitionFunctionΛ_neg_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    Real.log (partitionFunctionΛ G Λ (⟨J, -h, β⟩ : IsingParams ℝ))
      = Real.log (partitionFunctionΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ)) := by
  rw [partitionFunctionΛ_neg_h]

/-- **Log form of Λ-level `|h|`-rewrite**:
`log Z_Λ(J, h, β) = log Z_Λ(J, |h|, β)`. Direct from
`partitionFunctionΛ_eq_abs_h`. -/
theorem log_partitionFunctionΛ_eq_abs_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    Real.log (partitionFunctionΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ))
      = Real.log (partitionFunctionΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ)) := by
  rw [partitionFunctionΛ_eq_abs_h]

/-- **Log form of Λ-level J-monotonicity**:
for `h ≥ 0`, `β > 0`, `0 ≤ J₁ ≤ J₂`,
`log Z_Λ(⟨J₁, h, β⟩) ≤ log Z_Λ(⟨J₂, h, β⟩)`. Via `Real.log_le_log`
using `partitionFunctionΛ_pos` and `partitionFunctionΛ_monotone_J`. -/
theorem log_partitionFunctionΛ_monotone_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) :
    Real.log (partitionFunctionΛ G Λ (⟨J₁, h, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ G Λ (⟨J₂, h, β⟩ : IsingParams ℝ)) :=
  Real.log_le_log (partitionFunctionΛ_pos G Λ _)
    (partitionFunctionΛ_monotone_J G Λ h β hh hβ hJ₁ hJ)

/-- **Log form of Λ-level h-monotonicity**: ferromagnetic direction. -/
theorem log_partitionFunctionΛ_monotone_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) :
    Real.log (partitionFunctionΛ G Λ (⟨J, h₁, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ G Λ (⟨J, h₂, β⟩ : IsingParams ℝ)) :=
  Real.log_le_log (partitionFunctionΛ_pos G Λ _)
    (partitionFunctionΛ_monotone_h G Λ J β hJ hβ hh₁ hh)

/-- **Log form of Λ-level β-monotonicity**: ferromagnetic direction. -/
theorem log_partitionFunctionΛ_monotone_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    Real.log (partitionFunctionΛ G Λ (⟨J, h, β₁⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ G Λ (⟨J, h, β₂⟩ : IsingParams ℝ)) :=
  Real.log_le_log (partitionFunctionΛ_pos G Λ _)
    (partitionFunctionΛ_monotone_beta G Λ J h hJ hh hβ₁ hβ)

/-- **Log form of Λ-level `|h|`-monotonicity**: ferromagnetic
`|h₁| ≤ |h₂|` implies `log Z_Λ(⟨J, h₁, β⟩) ≤ log Z_Λ(⟨J, h₂, β⟩)`. -/
theorem log_partitionFunctionΛ_monotone_abs_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    Real.log (partitionFunctionΛ G Λ (⟨J, h₁, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ G Λ (⟨J, h₂, β⟩ : IsingParams ℝ)) :=
  Real.log_le_log (partitionFunctionΛ_pos G Λ _)
    (partitionFunctionΛ_monotone_abs_h G Λ J β hJ hβ hh)

/-- **Along-exhaustion log-Z h-evenness** per stage:
`log Z(Λ.volume n; ⟨J, -h, β⟩) = log Z(Λ.volume n; ⟨J, h, β⟩)`. -/
theorem log_partitionFunctionAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionΛ_neg_h G (Λ.volume n) J h β

/-- **Along-exhaustion log-Z `|h|`-rewrite** per stage:
`log Z(Λ.volume n; ⟨J, h, β⟩) = log Z(Λ.volume n; ⟨J, |h|, β⟩)`. -/
theorem log_partitionFunctionAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionΛ_eq_abs_h G (Λ.volume n) J h β

/-- **Along-exhaustion log-Z J-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionΛ_monotone_J G (Λ.volume n) h β hh hβ hJ₁ hJ

/-- **Along-exhaustion log-Z h-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_monotone_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionΛ_monotone_h G (Λ.volume n) J β hJ hβ hh₁ hh

/-- **Along-exhaustion log-Z β-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionΛ_monotone_beta G (Λ.volume n) J h hJ hh hβ₁ hβ

/-- **Along-exhaustion log-Z `|h|`-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_monotone_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionΛ_monotone_abs_h G (Λ.volume n) J β hJ hβ hh


end IsingModel
