import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint

/-!
# ℤ^d freeEnergyAlongExhaustion + freeEnergyInfinite cubicExhaustion wrappers

Narrow child module for 34 ℤ^d `freeEnergyAlongExhaustion_latticeGraph`
/ `freeEnergyInfinite_latticeGraph` / cubicExhaustion convergence,
trivial-slice, monotonicity, neg-h / abs-h, `ge_log_two_cosh` /
`ge_log_two` / `bounds` wrappers, plus the two
`spontaneousMagnetization_latticeGraph_cubicExhaustion_monotone_{J, beta}`
variants. Theorem names are unchanged from the former `TwoPoint`
declarations.
-/

namespace IsingModel
namespace Ambient

/-! ## Moved: ℤ^d freeEnergyAlongExhaustion tendsto wrappers

The 9 ℤ^d `freeEnergyAlongExhaustion_latticeGraph_*_tendsto_*`
convergence wrappers (`J_zero_tendsto_of_hcard_add`,
`beta_zero_tendsto_of_hcard_add`, `tendsto_of_disjoint_tower`,
`tendsto_of_disjointTowerHypotheses`, `tendsto_of_superadditive`,
`tendsto_of_eventually_const`,
`J_zero_tendsto_of_eventually_nonempty`,
`beta_zero_tendsto_of_eventually_nonempty`,
`zero_params_tendsto_of_eventually_nonempty`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFreeEnergyAlongExTendsto`.
The legacy import path is preserved by re-importing the new child.
-/

/-- **ℤ^d freeEnergyInfinite at β=0 under eventually-nonempty** (any-Exhaustion):
`= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_beta_zero_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_beta_zero_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ J h hne

/-- **ℤ^d freeEnergyInfinite at J=h=0 under eventually-nonempty** (any-Exhaustion):
`= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_zero_params_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_zero_params_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ β hne

/-- **ℤ^d freeEnergyInfinite at J=0 under eventually-nonempty** (any-Exhaustion):
`= log(2·cosh(β·h))`. -/
theorem freeEnergyInfinite_latticeGraph_J_zero_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyInfinite_J_zero_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ h β hne

/-- **ℤ^d freeEnergyInfinite at β = 0** (any-Exhaustion): `= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_beta_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_beta_zero_of_nonempty (IsingModel.latticeGraph d) Λ J h

/-- **ℤ^d freeEnergyInfinite at J = h = 0** (any-Exhaustion): `= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_zero_params
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_zero_params_of_nonempty (IsingModel.latticeGraph d) Λ β

/-- **ℤ^d freeEnergyInfinite at J = 0** (any-Exhaustion): `= log(2 cosh(β·h))`. -/
theorem freeEnergyInfinite_latticeGraph_J_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyInfinite_J_zero_of_nonempty (IsingModel.latticeGraph d) Λ h β

/-- **ℤ^d freeEnergyInfinite at β = 0**: `= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)] (J h : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_beta_zero_of_nonempty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h

/-- **ℤ^d freeEnergyInfinite at J = h = 0**: `= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) [Nonempty (Fin d → ℤ)] (β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_zero_params_of_nonempty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) β

/-- **ℤ^d freeEnergyInfinite at J = 0**: `= log(2 cosh(β·h))`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)] (h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyInfinite_J_zero_of_nonempty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β

/-- **Sharp lower bound** `freeEnergyInfinite ≥ log(2 cosh(βh))` on ℤ^d. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_ge_log_two_cosh
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (2 * Real.cosh (p.β * p.h))
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p := by
  refine freeEnergyInfinite_ge_log_two_cosh (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **Lower bound** `freeEnergyInfinite ≥ log 2` on ℤ^d (any Exhaustion
with caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_ge_log_two
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    Real.log 2 ≤ freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_ge_log_two (IsingModel.latticeGraph d) Λ p hf (c := c) hc

/-- **Sharp lower bound** `freeEnergyInfinite ≥ log(2 cosh(βh))` on ℤ^d
(any Exhaustion with caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_ge_log_two_cosh
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    Real.log (2 * Real.cosh (p.β * p.h))
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_ge_log_two_cosh (IsingModel.latticeGraph d)
    Λ p hf (c := c) hc

/-- **ℤ^d ∞-vol free-energy sandwich bound** (ferromagnetic):
`log 2 ≤ freeEnergyInfinite (latticeGraph d) (cubicExhaustion d) p
  ≤ log 2 + |β|·(|J|·d + |h|)`.

Capstone for the ∞-vol free-energy bounds on ℤ^d. Uses BED `c = d`
(PR #246) for the upper bound, and `freeEnergyInfinite_ge_log_two`
for the lower. Note: `[Nonempty (Fin d → ℤ)]` holds for every `d` since
`Fin 0 → ℤ` has exactly one element (empty function) and `Fin d → ℤ`
with `d ≥ 1` has `fun _ => 0`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_bounds
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log 2
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p
    ∧ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p
        ≤ Real.log 2 + |p.β| * (|p.J| * (d : ℝ) + |p.h|) := by
  have hc : ∀ n, ((Ambient.cubicExhaustion d).volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n)).edgeFinset.card : ℝ)
        ≤ (d : ℝ) * Fintype.card
            (↑((Ambient.cubicExhaustion d).volume n) : Type _) := by
    intro n _
    exact inducedLatticeGraph_card_edgeFinset_le d
      ((Ambient.cubicExhaustion d).volume n)
  refine ⟨?_, ?_⟩
  · exact freeEnergyInfinite_ge_log_two (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p hf hc
  · exact freeEnergyInfinite_le_uniform_upper_bound
      (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf hc

/-- **`|h|`-monotonicity of `freeEnergyInfinite` on ℤ^d**:
`|h₁| ≤ |h₂| ⇒ freeEnergyInfinite ⟨J, h₁, β⟩ ≤ freeEnergyInfinite ⟨J, h₂, β⟩`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_abs_h
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) := by
  refine freeEnergyInfinite_monotone_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ (c := (d : ℝ)) ?_ hh
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **h-evenness of `freeEnergyInfinite` on ℤ^d**:
`freeEnergyInfinite ⟨J, -h, β⟩ = freeEnergyInfinite ⟨J, h, β⟩`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_neg_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β

/-- **`|h|`-form of `freeEnergyInfinite` on ℤ^d**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_eq_abs_h
    (d : ℕ) (J h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_eq_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β

/-- **h-evenness of `freeEnergyInfinite` on ℤ^d** (any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_neg_h (IsingModel.latticeGraph d) Λ J h β

/-- **`|h|`-form of `freeEnergyInfinite` on ℤ^d** (any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_eq_abs_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d J-monotonicity of `freeEnergyInfinite`** (any-Exhaustion with
caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_monotone_J
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun J : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  freeEnergyInfinite_monotone_J (IsingModel.latticeGraph d) Λ hh hβ hc

/-- **ℤ^d h-monotonicity of `freeEnergyInfinite`** (any-Exhaustion with
caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_monotone_h
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun h : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  freeEnergyInfinite_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ hc

/-- **ℤ^d β-monotonicity of `freeEnergyInfinite`** (any-Exhaustion with
caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_monotone_beta
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun β : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ioi 0) :=
  freeEnergyInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh hc

/-- **ℤ^d `|h|`-monotonicity of `freeEnergyInfinite`** (any-Exhaustion
with caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_monotone_abs_h
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _))
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_monotone_abs_h (IsingModel.latticeGraph d) Λ hJ hβ hc hh

/-- **J-monotonicity of `freeEnergyInfinite` on ℤ^d** under the concrete
BED constant `c = d` (PR #246). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) := by
  refine freeEnergyInfinite_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **h-monotonicity of `freeEnergyInfinite` on ℤ^d**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun h : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) := by
  refine freeEnergyInfinite_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **β-monotonicity of `freeEnergyInfinite` on ℤ^d**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ioi 0) := by
  refine freeEnergyInfinite_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)


end Ambient

end IsingModel
