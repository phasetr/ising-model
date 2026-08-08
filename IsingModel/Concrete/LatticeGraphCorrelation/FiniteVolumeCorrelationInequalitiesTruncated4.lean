import IsingModel.Inequalities.GHS
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# The truncated four-point function at finite volume in ℤ^d

Records the truncated four-point function of the subgraph induced by the nearest-neighbor
lattice graph on a finite `Λ ⊆ ℤ^d` on the decoupled slices and under the ferromagnetic
condition: it vanishes at zero inverse temperature, it equals `-2·tanh(β·h)^4` at zero
coupling and pairwise distinct sites, and it is nonpositive at zero external field for a
ferromagnetic parameter record and pairwise distinct sites. The zero-inverse-temperature
statement holds at arbitrary, possibly repeated, sites and imposes no condition on the
coupling or the external field.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.3, p. 61; the reading as `U_4 ≤ 0` is the remark
on p. 62.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d truncated4 β=0 vanish** at Λ-induced. -/
theorem truncated4_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i j k l : ↑Λ) :
    IsingModel.truncated4
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ) i j k l = 0 :=
  IsingModel.truncated4_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h i j k l

/-- **ℤ^d truncated4 J=0 closed form** at Λ-induced (pairwise distinct):
`truncated4 = -2 · tanh(β·h)^4`. -/
theorem truncated4_J_zero_of_pairwise_distinct_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    {i j k l : ↑Λ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    IsingModel.truncated4
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) i j k l
      = -2 * Real.tanh (β * h) ^ 4 :=
  IsingModel.truncated4_J_zero_of_pairwise_distinct
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β
    hij hik hil hjk hjl hkl

/-- **ℤ^d Cor 4.3.3 at Λ-induced subgraph** (Glimm–Jaffe §4.3):
`U_4(i, j, k, l) ≤ 0` at `h = 0` for ferromagnetic and distinct sites. -/
theorem cor_4_3_3_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (i j k l : ↑Λ) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    IsingModel.truncated4 (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, 0, β⟩ : IsingParams ℝ) i j k l ≤ 0 :=
  IsingModel.cor_4_3_3 (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
    J β hf i j k l hij hik hil hjk hjl hkl

end Ambient
end IsingModel
