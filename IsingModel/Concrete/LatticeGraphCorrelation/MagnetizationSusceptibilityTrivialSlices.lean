import IsingModel.PhaseTransition.MagnetizationSusceptibility
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d susceptibility and truncated two-point function on the trivial slices

Concrete identities on the subgraph induced by a fixed finite volume of `Fin d → ℤ`. At zero
coupling the susceptibility at a vertex is `t * (1 - t)` for `t = Real.tanh (β * h)`; the
`Finset`-indexed truncated two-point function underlying it contributes `t - t ^ 2` on the
diagonal, which is what makes the closed form differ from the physical `1 - t ^ 2`. At zero
external field the truncated two-point function at a pair of vertices is the correlation of
that pair, and the susceptibility at a vertex is the sum of those correlations over all
vertices. No statement here carries a hypothesis, and no instance argument is taken.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d susceptibility_J_zero direct** (Λ-induced): at `J = 0`,
`χ_i = t · (1 - t)` with `t = tanh(β·h)`. Thin pass-through of
`IsingModel.susceptibility_J_zero`. Note: uses the Finset-based
`truncated2` so the diagonal `{i, i} = {i}` term is `t - t²`, not
the physical `1 - t²` — see the base theorem's doc comment. -/
theorem susceptibility_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h)) :=
  IsingModel.susceptibility_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β i

/-- **ℤ^d truncated2 h=0 direct** (Λ-induced): at `h = 0`,
`truncated2 i j = correlation {i, j}`. Thin pass-through of
`IsingModel.truncated2_h_zero`. -/
theorem truncated2_h_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i j : (↑Λ : Type _)) :
    IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, 0, β⟩ : IsingParams ℝ) i j
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} :=
  IsingModel.truncated2_h_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β i j

/-- **ℤ^d susceptibility_h_zero direct** (Λ-induced): at `h = 0`,
`χ_i = ∑_j correlation {i, j}`. Thin pass-through of
`IsingModel.susceptibility_h_zero`. -/
theorem susceptibility_h_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, 0, β⟩ : IsingParams ℝ) i
      = ∑ j : (↑Λ : Type _),
          IsingModel.correlation
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} :=
  IsingModel.susceptibility_h_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β i

end Ambient
end IsingModel
