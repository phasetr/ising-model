import IsingModel.AmbientLattice.SpecialCases.FreeEnergy

/-!
# AmbientLatticeSum freeEnergyInfinite h-symmetry + monotonicity wrappers

Narrow child module for the 6 freeEnergyInfinite h-symmetry +
monotonicity wrappers: `freeEnergyInfinite_neg_h`,
`freeEnergyInfinite_eq_abs_h`, `freeEnergyInfinite_monotone_J`,
`freeEnergyInfinite_monotone_h`, `freeEnergyInfinite_monotone_beta`,
`freeEnergyInfinite_monotone_abs_h`. The theorem names are unchanged
from the former `AmbientLatticeSum` declarations.
-/

namespace IsingModel

open Finset
open Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion h-evenness at limsup**:
`freeEnergyInfinite G Λ ⟨J, -h, β⟩ = freeEnergyInfinite G Λ ⟨J, h, β⟩`.
Lifts `freeEnergyAlongExhaustion_neg_h` pointwise to `limsup`. -/
theorem freeEnergyInfinite_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) :
    freeEnergyInfinite G Λ (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) := by
  unfold freeEnergyInfinite
  congr 1
  funext n
  exact freeEnergyAlongExhaustion_neg_h G Λ J h β n

/-- **`|h|`-form at limsup**:
`freeEnergyInfinite G Λ ⟨J, h, β⟩ = freeEnergyInfinite G Λ ⟨J, |h|, β⟩`.
Lifts `freeEnergyAlongExhaustion_eq_abs_h` pointwise to `limsup`. -/
theorem freeEnergyInfinite_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) :
    freeEnergyInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) := by
  unfold freeEnergyInfinite
  congr 1
  funext n
  exact freeEnergyAlongExhaustion_eq_abs_h G Λ J h β n

set_option linter.unusedFintypeInType false in
/-- **J-direction monotonicity of `freeEnergyInfinite`**: for fixed
`h ≥ 0`, `β > 0`, the limsup free energy is monotone in
`J ∈ Set.Ici 0`.

Lifts `freeEnergyAlongExhaustion_monotone_J` pointwise via
`Filter.limsup_le_limsup`, using the ferromagnetic lower bound and
`BoundedEdgeDensity` upper bound to control the required
`IsCoboundedUnder` / `IsBoundedUnder` hypotheses. -/
theorem freeEnergyInfinite_monotone_J
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun J : ℝ => freeEnergyInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) := by
  intro J₁ hJ₁ J₂ _ hJle
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty :=
    Λ.eventually_volume_nonempty
  have hJ₁nn : (0 : ℝ) ≤ J₁ := hJ₁
  have hJ₂nn : (0 : ℝ) ≤ J₂ := hJ₁nn.trans hJle
  have hle : ∀ᶠ n in Filter.atTop,
      freeEnergyAlongExhaustion G Λ (⟨J₁, h, β⟩ : IsingParams ℝ) n
        ≤ freeEnergyAlongExhaustion G Λ (⟨J₂, h, β⟩ : IsingParams ℝ) n := by
    apply Filter.Eventually.of_forall
    intro n
    exact freeEnergyAlongExhaustion_monotone_J G Λ hh hβ n hJ₁nn hJ₂nn hJle
  have hbdd_below_J₁ : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ (⟨J₁, h, β⟩ : IsingParams ℝ)) := by
    refine ⟨Real.log (2 * Real.cosh (β * h)), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_ge_log_two_cosh
      G Λ hJ₁nn hh hβ n hne
  have hbdd_above_J₂ : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ (⟨J₂, h, β⟩ : IsingParams ℝ)) := by
    refine ⟨Real.log 2 + |β| * (|J₂| * c + |h|), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ _ hc n hne
  exact Filter.limsup_le_limsup hle hbdd_below_J₁.isCoboundedUnder_le hbdd_above_J₂

set_option linter.unusedFintypeInType false in
/-- **h-direction monotonicity of `freeEnergyInfinite`**: for fixed
`J ≥ 0`, `β > 0`, the limsup free energy is monotone in
`h ∈ Set.Ici 0`. Lifts `freeEnergyAlongExhaustion_monotone_h`. -/
theorem freeEnergyInfinite_monotone_h
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun h : ℝ => freeEnergyInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) := by
  intro h₁ hh₁ h₂ _ hhle
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty :=
    Λ.eventually_volume_nonempty
  have hh₁nn : (0 : ℝ) ≤ h₁ := hh₁
  have hh₂nn : (0 : ℝ) ≤ h₂ := hh₁nn.trans hhle
  have hle : ∀ᶠ n in Filter.atTop,
      freeEnergyAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ) n
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) n := by
    apply Filter.Eventually.of_forall
    intro n
    exact freeEnergyAlongExhaustion_monotone_h G Λ hJ hβ n hh₁nn hh₂nn hhle
  have hbdd_below_h₁ : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ)) := by
    refine ⟨Real.log (2 * Real.cosh (β * h₁)), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_ge_log_two_cosh
      G Λ hJ hh₁nn hβ n hne
  have hbdd_above_h₂ : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ)) := by
    refine ⟨Real.log 2 + |β| * (|J| * c + |h₂|), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ _ hc n hne
  exact Filter.limsup_le_limsup hle hbdd_below_h₁.isCoboundedUnder_le hbdd_above_h₂

set_option linter.unusedFintypeInType false in
/-- **β-direction monotonicity of `freeEnergyInfinite`**: for fixed
`J ≥ 0`, `h ≥ 0`, the limsup free energy is monotone in
`β ∈ Set.Ioi 0`. Lifts `freeEnergyAlongExhaustion_monotone_beta`. -/
theorem freeEnergyInfinite_monotone_beta
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun β : ℝ => freeEnergyInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ _ hβle
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty :=
    Λ.eventually_volume_nonempty
  have hβ₁pos : (0 : ℝ) < β₁ := hβ₁
  have hβ₂pos : (0 : ℝ) < β₂ := hβ₁pos.trans_le hβle
  have hle : ∀ᶠ n in Filter.atTop,
      freeEnergyAlongExhaustion G Λ (⟨J, h, β₁⟩ : IsingParams ℝ) n
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, h, β₂⟩ : IsingParams ℝ) n := by
    apply Filter.Eventually.of_forall
    intro n
    exact freeEnergyAlongExhaustion_monotone_beta G Λ hJ hh n hβ₁pos hβ₂pos hβle
  have hbdd_below_β₁ : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ (⟨J, h, β₁⟩ : IsingParams ℝ)) := by
    refine ⟨Real.log (2 * Real.cosh (β₁ * h)), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_ge_log_two_cosh
      G Λ hJ hh hβ₁pos n hne
  have hbdd_above_β₂ : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ (⟨J, h, β₂⟩ : IsingParams ℝ)) := by
    refine ⟨Real.log 2 + |β₂| * (|J| * c + |h|), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ _ hc n hne
  exact Filter.limsup_le_limsup hle hbdd_below_β₁.isCoboundedUnder_le hbdd_above_β₂

set_option linter.unusedFintypeInType false in
/-- **`|h|`-monotonicity of `freeEnergyInfinite`**: for fixed
`J ≥ 0`, `β > 0`, `freeEnergyInfinite` is monotone in `|h|`.
Composition of `freeEnergyInfinite_eq_abs_h` and
`freeEnergyInfinite_monotone_h` on `Set.Ici 0`. -/
theorem freeEnergyInfinite_monotone_abs_h
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _))
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergyInfinite G Λ (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergyInfinite G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) := by
  rw [freeEnergyInfinite_eq_abs_h G Λ J h₁ β,
      freeEnergyInfinite_eq_abs_h G Λ J h₂ β]
  exact freeEnergyInfinite_monotone_h G Λ hJ hβ hc
    (Set.mem_Ici.mpr (abs_nonneg h₁)) (Set.mem_Ici.mpr (abs_nonneg h₂)) hh


end IsingModel
