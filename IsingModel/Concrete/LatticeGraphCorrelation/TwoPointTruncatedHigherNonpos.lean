import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Sign of the ℤ^d truncated three- and four-point correlations

Concrete `IsingModel.latticeGraph d` statements along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ`, at pairwise distinct sites.

Under `Ferromagnetic` on an unrestricted parameter record the truncated three-point
correlation is non-positive, which is the Griffiths-Hurst-Sherman inequality. At a record
whose external field vanishes, and again under `Ferromagnetic`, the truncated four-point
correlation is non-positive, which is the Lebowitz inequality.

At a record whose external field vanishes the truncated three-point correlation vanishes
outright, and that statement assumes no ferromagnetic condition, only that the sites are
pairwise distinct. Nothing in this module takes an instance argument.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d truncated3Infinite nonpos** (GHS) site-wise (any Exhaustion). -/
theorem truncated3Infinite_latticeGraph_nonpos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {i j k : Fin d → ℤ} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k ≤ 0 :=
  truncated3Infinite_nonpos (IsingModel.latticeGraph d) Λ p hf hij hjk hik

/-- **ℤ^d truncated4Infinite nonpos at h=0** (Lebowitz) site-wise. -/
theorem truncated4Infinite_latticeGraph_nonpos_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : Fin d → ℤ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ i j k l ≤ 0 :=
  truncated4Infinite_nonpos_h_zero (IsingModel.latticeGraph d) Λ J β hf
    hij hik hil hjk hjl hkl

/-- **ℤ^d truncated3Infinite at h=0 vanishes** site-wise, pairwise distinct. -/
theorem truncated3Infinite_latticeGraph_h_zero_of_distinct
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    {i j k : Fin d → ℤ}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ i j k = 0 :=
  truncated3Infinite_h_zero_of_distinct (IsingModel.latticeGraph d) Λ J β
    hij hjk hik

end Ambient

end IsingModel
