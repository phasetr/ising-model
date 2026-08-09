import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d sign of the truncated four-point and two-point functions

Concrete `latticeGraph d` statements for parameter records satisfying `Ferromagnetic`.

At zero external field and for four pairwise distinct vertices the truncated four-point
function is non-positive. That sign is recorded on the subgraph induced by a fixed finite
volume, where no instance argument is taken, and in the infinite-volume form along an
arbitrary `Ambient.Exhaustion` of `Fin d → ℤ`, which requires a `Fintype` instance on the
edge set induced at every stage; it is stated under its critical-exponent reading and under
its absence-of-even-bound-states reading alike.

The infinite-volume truncated two-point function is non-negative at an unrestricted parameter
record satisfying `Ferromagnetic` and, in contrast with the four-point statements, at an
arbitrary pair of sites with no distinctness assumed; it too requires the per-stage `Fintype`
instance.
-/

namespace IsingModel
namespace Ambient

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
