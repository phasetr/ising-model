import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete ℤ^d ζ/η/absence-of-even-bound-states wrappers (GJ §17.2/§17.7)

Narrow child module for the 5 ℤ^d critical-exponent wrappers
(`zeta_nonneg_finite_vol_latticeGraph`,
`eta_nonneg_infinite_vol_latticeGraph`,
`zeta_nonneg_infinite_vol_latticeGraph`,
`absence_of_even_bound_states_finite_vol_latticeGraph`,
`absence_of_even_bound_states_infinite_vol_latticeGraph`)
extracted from `PerStage.lean` in PR #2050. Each is a thin
pass-through to the corresponding abstract `IsingModel.*` /
`Ambient.*` lemma. The theorem names are unchanged from the former
`PerStage` declarations.
-/

namespace IsingModel
namespace Ambient

/-! #### §17.7 critical-exponent bounds at ℤ^d

Direct ℤ^d wrappers for the `η ≥ 0` and `ζ ≥ 0` critical-exponent
bounds at ℤ^d, for both finite-volume and ∞-volume. Pass-throughs of
`IsingModel.{eta,zeta}_nonneg_{finite,infinite}_vol`. -/

/-- **ℤ^d `ζ ≥ 0` finite-volume** (Λ-induced, GJ §17.7 Thm 17.7.1,
ferromagnetic at `h = 0`). Pass-through of
`IsingModel.zeta_nonneg_finite_vol`. -/
theorem zeta_nonneg_finite_vol_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (i j k l : (↑Λ : Type _))
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    IsingModel.truncated4
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          ⟨J, 0, β⟩ i j k l ≤ 0 :=
  IsingModel.zeta_nonneg_finite_vol
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hf
    i j k l hij hik hil hjk hjl hkl

/-- **ℤ^d `η ≥ 0` ∞-volume** (GJ §17.7 Thm 17.7.1, ferromagnetic).
Pass-through of `IsingModel.Ambient.eta_nonneg_infinite_vol`. -/
theorem eta_nonneg_infinite_vol_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    0 ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ p i j :=
  Ambient.eta_nonneg_infinite_vol (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d `ζ ≥ 0` ∞-volume** (GJ §17.7 Thm 17.7.1, ferromagnetic at
`h = 0`). Pass-through of `IsingModel.Ambient.zeta_nonneg_infinite_vol`. -/
theorem zeta_nonneg_infinite_vol_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    {i j k l : Fin d → ℤ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    Ambient.truncated4Infinite (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩ i j k l ≤ 0 :=
  Ambient.zeta_nonneg_infinite_vol (IsingModel.latticeGraph d) Λ J β hf
    hij hik hil hjk hjl hkl

/-- **ℤ^d absence of even bound states, finite-volume** (GJ §17.2
Λ-induced, ferromagnetic at `h = 0`). Pass-through of
`IsingModel.absence_of_even_bound_states_finite_vol`. -/
theorem absence_of_even_bound_states_finite_vol_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (i j k l : (↑Λ : Type _))
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    IsingModel.truncated4
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          ⟨J, 0, β⟩ i j k l ≤ 0 :=
  IsingModel.absence_of_even_bound_states_finite_vol
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hf
    i j k l hij hik hil hjk hjl hkl

/-- **ℤ^d absence of even bound states, ∞-volume** (GJ §17.2,
ferromagnetic at `h = 0`). Pass-through of
`IsingModel.Ambient.absence_of_even_bound_states_infinite_vol`. -/
theorem absence_of_even_bound_states_infinite_vol_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    {i j k l : Fin d → ℤ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    Ambient.truncated4Infinite (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩ i j k l ≤ 0 :=
  Ambient.absence_of_even_bound_states_infinite_vol
    (IsingModel.latticeGraph d) Λ J β hf hij hik hil hjk hjl hkl

end Ambient

end IsingModel
