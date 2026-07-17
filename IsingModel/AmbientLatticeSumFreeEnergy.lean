import IsingModel.AmbientLattice.Exhaustion

/-!
# AmbientLatticeSum freeEnergyΛ basic wrappers

Narrow child module for the basic freeEnergyΛ /
freeEnergyAlongExhaustion wrappers (13 theorems):
`freeEnergyΛ_ge_log_two_cosh`, `freeEnergyΛ_ge_log_two`,
`freeEnergyΛ_nonneg_of_ferromagnetic`,
`freeEnergyAlongExhaustion_nonneg_of_ferromagnetic`,
`freeEnergyΛ_J_zero`, `freeEnergyΛ_beta_zero`,
`freeEnergyΛ_zero_params`, `freeEnergyΛ_neg_h`,
`freeEnergyΛ_eq_abs_h`, `freeEnergyΛ_monotone_abs_h`,
`freeEnergyΛ_monotone_J`, `freeEnergyΛ_monotone_h`,
`freeEnergyΛ_monotone_beta`. The theorem names are unchanged from
the former `AmbientLatticeSum` declarations.
-/

namespace IsingModel

open Finset
open Ambient

variable {V : Type*} [DecidableEq V]

/-- **`freeEnergyΛ ≥ log(2·cosh(β·h))`** for ferromagnetic on nonempty `Λ`.
Wrapper of `IsingModel.freeEnergy_ge_log_two_cosh`. -/
theorem freeEnergyΛ_ge_log_two_cosh
    (G : SimpleGraph V) {Λ : Finset V} (hne : Λ.Nonempty)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) := by
  exact IsingModel.freeEnergy_ge_log_two_cosh _ hJ hh hβ hne.fintype_card_coe_pos

/-- **`freeEnergyΛ ≥ log 2`** for ferromagnetic on nonempty `Λ`.
Thin wrapper of base-layer
`IsingModel.freeEnergy_ge_log_two_of_ferromagnetic`. -/
theorem freeEnergyΛ_ge_log_two
    (G : SimpleGraph V) {Λ : Finset V} (hne : Λ.Nonempty)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2 ≤ freeEnergyΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_ge_log_two_of_ferromagnetic
    (inducedGraph G Λ) _ ⟨hJ, hh, hβ⟩ hne.fintype_card_coe_pos

/-- **`freeEnergyΛ ≥ 0`** for ferromagnetic on nonempty `Λ`.
Thin wrapper of base-layer
`IsingModel.freeEnergy_nonneg_of_ferromagnetic`. -/
theorem freeEnergyΛ_nonneg_of_ferromagnetic
    (G : SimpleGraph V) {Λ : Finset V} (hne : Λ.Nonempty)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyΛ G Λ p :=
  IsingModel.freeEnergy_nonneg_of_ferromagnetic
    (inducedGraph G Λ) p hf hne.fintype_card_coe_pos

/-- **Per-stage `freeEnergyAlongExhaustion ≥ 0`** (ferromagnetic, nonempty stage):
direct from `freeEnergyΛ_nonneg_of_ferromagnetic` at `Λ.volume n`. -/
theorem freeEnergyAlongExhaustion_nonneg_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {n : ℕ}
    (hne : (Λ.volume n).Nonempty) :
    0 ≤ freeEnergyAlongExhaustion G Λ p n :=
  freeEnergyΛ_nonneg_of_ferromagnetic G hne p hf

/-- **Λ-level free-energy closed form at `J = 0`**:
for nonempty `Λ` and any ambient graph `G`,
`freeEnergyΛ G Λ ⟨0, h, β⟩ = log(2·cosh(β·h))`. Thin wrapper of
`IsingModel.freeEnergy_J_zero` through
`freeEnergyΛ := freeEnergy (inducedGraph G Λ)`. -/
theorem freeEnergyΛ_J_zero
    (G : SimpleGraph V) {Λ : Finset V} (hne : Λ.Nonempty)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) :
    freeEnergyΛ G Λ (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  IsingModel.freeEnergy_J_zero _ h β hne.fintype_card_coe_pos

/-- **Λ-level free-energy closed form at `β = 0`**:
for nonempty `Λ` and any ambient graph `G`,
`freeEnergyΛ G Λ ⟨J, h, 0⟩ = log 2`. Thin wrapper of
`IsingModel.freeEnergy_beta_zero`. -/
theorem freeEnergyΛ_beta_zero
    (G : SimpleGraph V) {Λ : Finset V} (hne : Λ.Nonempty)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    freeEnergyΛ G Λ (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  IsingModel.freeEnergy_beta_zero _ J h hne.fintype_card_coe_pos

/-- **Λ-level free-energy closed form at `J = 0, h = 0`**:
for nonempty `Λ` and any ambient graph `G`,
`freeEnergyΛ G Λ ⟨0, 0, β⟩ = log 2`. Thin wrapper of
`IsingModel.freeEnergy_zero_params`. -/
theorem freeEnergyΛ_zero_params
    (G : SimpleGraph V) {Λ : Finset V} (hne : Λ.Nonempty)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 :=
  IsingModel.freeEnergy_zero_params _ β hne.fintype_card_coe_pos

/-- **Λ-level free-energy h-evenness**:
`freeEnergyΛ G Λ ⟨J, -h, β⟩ = freeEnergyΛ G Λ ⟨J, h, β⟩`. Direct lift of
`IsingModel.freeEnergy_neg_h` via the flip involution through
`freeEnergyΛ = freeEnergy (inducedGraph G Λ)`. -/
theorem freeEnergyΛ_neg_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    freeEnergyΛ G Λ (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergyΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_neg_h _ J h β

/-- **Λ-level free-energy `|h|`-rewrite**:
`freeEnergyΛ G Λ ⟨J, h, β⟩ = freeEnergyΛ G Λ ⟨J, |h|, β⟩`. Direct lift
of `IsingModel.freeEnergy_eq_abs_h`. -/
theorem freeEnergyΛ_eq_abs_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    freeEnergyΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergyΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_eq_abs_h _ J h β

/-- **Λ-level ferromagnetic `|h|`-monotonicity**:
for `J ≥ 0`, `β > 0` and any real `h₁, h₂` with `|h₁| ≤ |h₂|`,
`freeEnergyΛ G Λ ⟨J, h₁, β⟩ ≤ freeEnergyΛ G Λ ⟨J, h₂, β⟩`. Direct lift
of `IsingModel.freeEnergy_monotone_abs_h`. -/
theorem freeEnergyΛ_monotone_abs_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergyΛ G Λ (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergyΛ G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_monotone_abs_h _ J β hJ hβ hh

/-- **Λ-level J-monotonicity of `freeEnergyΛ`**:
for fixed `h ≥ 0`, `β > 0`, the free energy on `Λ` is monotone in `J`
on `[0, ∞)`. Direct lift of `IsingModel.freeEnergy_monotone_J`. -/
theorem freeEnergyΛ_monotone_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => freeEnergyΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  IsingModel.freeEnergy_monotone_J (inducedGraph G Λ) h β hh hβ

/-- **Λ-level h-monotonicity of `freeEnergyΛ`**:
for fixed `J ≥ 0`, `β > 0`, the free energy on `Λ` is monotone in `h`
on `[0, ∞)`. Direct lift of `IsingModel.freeEnergy_monotone_h`. -/
theorem freeEnergyΛ_monotone_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun h : ℝ => freeEnergyΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  IsingModel.freeEnergy_monotone_h (inducedGraph G Λ) J β hJ hβ

/-- **Λ-level β-monotonicity of `freeEnergyΛ`**:
for fixed `J ≥ 0`, `h ≥ 0`, the free energy on `Λ` is monotone in `β`
on `(0, ∞)`. Direct lift of `IsingModel.freeEnergy_monotone_beta`. -/
theorem freeEnergyΛ_monotone_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => freeEnergyΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ioi 0) :=
  IsingModel.freeEnergy_monotone_beta (inducedGraph G Λ) J hJ h hh

end IsingModel
