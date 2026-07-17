import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d correlation basic wrappers on `latticeGraph d`

Narrow child module for 8 ℤ^d `correlation_*_latticeGraph` thin
pass-throughs of the abstract `IsingModel.correlation_*` family on
`Ambient.inducedGraph (latticeGraph d) Λ`:

- bounds: `abs_correlation_le_one`, `correlation_le_one`,
  `neg_one_le_correlation`, `correlation_sq_le_one`;
- trivial slices: `correlation_beta_zero_vanish_of_nonempty_A`,
  `correlation_zero_params_vanish_of_nonempty_A`,
  `correlation_J_zero`, `correlation_empty`.

Theorem names are unchanged from the former `Magnetization`
declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d abs_correlation_le_one direct** (Λ-induced): `|⟨σ^A⟩| ≤ 1`. -/
theorem abs_correlation_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    |IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A| ≤ 1 :=
  IsingModel.abs_correlation_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A

/-- **ℤ^d correlation_le_one direct** (Λ-induced): `⟨σ^A⟩ ≤ 1`. -/
theorem correlation_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A ≤ 1 :=
  IsingModel.correlation_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A

/-- **ℤ^d neg_one_le_correlation direct** (Λ-induced): `-1 ≤ ⟨σ^A⟩`. -/
theorem neg_one_le_correlation_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    -1 ≤ IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A :=
  IsingModel.neg_one_le_correlation
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A

/-- **ℤ^d correlation_sq_le_one direct** (Λ-induced): `⟨σ^A⟩² ≤ 1`. -/
theorem correlation_sq_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A ^ 2 ≤ 1 :=
  IsingModel.correlation_sq_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A

/-! ## Moved: trivial-slice wrappers

The four wrappers
`correlation_beta_zero_vanish_of_nonempty_A_latticeGraph`,
`correlation_zero_params_vanish_of_nonempty_A_latticeGraph`,
`correlation_J_zero_latticeGraph`,
`correlation_empty_latticeGraph` now live in
`MagnetizationCorrelationBasicTrivialSlices.lean`. -/


end Ambient

end IsingModel
