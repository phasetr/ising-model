import IsingModel.Inequalities.GHS.SpinFlip
import IsingModel.Inequalities.GHS.NPoint
import IsingModel.AmbientLattice.MagnetizationInfinite
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d truncated correlations under sign change of the external field

Concrete `latticeGraph d` statements about the truncated (Ursell) correlations on the
subgraph induced by a fixed finite volume when the external field `h` is replaced by `-h`.
The two-point and four-point functions are invariant under that replacement; the three-point
function changes sign. Pairwise distinctness of the arguments is the only hypothesis of each
statement, no positivity of `J`, `h` or `β` is assumed, and no instance argument is taken.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d truncated2_neg_h direct** at Λ-induced (i ≠ j).
Concrete wrapper for `IsingModel.truncated2_neg_h` (#756). -/
theorem truncated2_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    {i j : (↑Λ : Type _)} (hij : i ≠ j) :
    IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i j
      = IsingModel.truncated2
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i j :=
  IsingModel.truncated2_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β hij

/-- **ℤ^d truncated3_neg_h direct** at Λ-induced (pairwise distinct):
antisymmetric, `U_3(-h) = -U_3(h)`. Concrete wrapper for
`IsingModel.truncated3_neg_h` (#758). -/
theorem truncated3_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    {i j k : (↑Λ : Type _)} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    IsingModel.truncated3
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i j k
      = -IsingModel.truncated3
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i j k :=
  IsingModel.truncated3_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β hij hjk hik

/-- **ℤ^d truncated4_neg_h direct** at Λ-induced (pairwise distinct):
invariant under `h → -h`. Concrete wrapper for
`IsingModel.truncated4_neg_h` (#757). -/
theorem truncated4_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    {i j k l : (↑Λ : Type _)}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    IsingModel.truncated4
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i j k l
      = IsingModel.truncated4
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i j k l :=
  IsingModel.truncated4_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β hij hik hil hjk hjl hkl

end Ambient
end IsingModel
