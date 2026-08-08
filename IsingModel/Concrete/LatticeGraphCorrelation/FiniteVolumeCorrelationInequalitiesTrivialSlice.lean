import IsingModel.Inequalities.GHS
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Truncated two- and three-point functions on the trivial parameter slices in ℤ^d

Records that the truncated two- and three-point functions of the subgraph induced by the
nearest-neighbor lattice graph on a finite `Λ ⊆ ℤ^d` vanish on the parameter slices where
the sites decouple: at zero coupling, where the Boltzmann weight factors over sites, and at
zero inverse temperature, where every configuration carries the same weight. Distinctness
of the sites is assumed only on the zero-coupling slice, pairwise for the three-point
function; the zero-inverse-temperature statements hold at arbitrary, possibly repeated,
sites. The parameters left free are unconstrained on either slice.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d truncated2 J=0 vanish for i ≠ j** at Λ-induced. -/
theorem truncated2_J_zero_of_ne_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    {i j : ↑Λ} (hij : i ≠ j) :
    IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) i j = 0 :=
  IsingModel.truncated2_J_zero_of_ne
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β hij

/-- **ℤ^d truncated2 β=0 vanish** at Λ-induced. -/
theorem truncated2_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i j : ↑Λ) :
    IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ) i j = 0 :=
  IsingModel.truncated2_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h i j

/-- **ℤ^d truncated3 J=0 vanish for pairwise distinct** at Λ-induced. -/
theorem truncated3_J_zero_of_pairwise_distinct_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    {i j k : ↑Λ} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    IsingModel.truncated3
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) i j k = 0 :=
  IsingModel.truncated3_J_zero_of_pairwise_distinct
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β hij hjk hik

/-- **ℤ^d truncated3 β=0 vanish** at Λ-induced. -/
theorem truncated3_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i j k : ↑Λ) :
    IsingModel.truncated3
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ) i j k = 0 :=
  IsingModel.truncated3_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h i j k

end Ambient
end IsingModel
