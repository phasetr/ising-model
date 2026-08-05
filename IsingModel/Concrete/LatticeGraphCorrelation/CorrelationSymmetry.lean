import IsingModel.Inequalities.GHS.SpinFlip
import IsingModel.PhaseTransition.MagnetizationSusceptibility
import IsingModel.AmbientLattice.MagnetizationInfinite
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete correlation symmetry wrappers

Narrow child module for concrete `latticeGraph` correlation, magnetization, and
susceptibility h-symmetry / absolute-field wrappers, including finite-volume,
along-exhaustion, and infinite-volume forms. The theorem names are the same as
the former declarations, but callers can now avoid importing the
monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d direct finite-volume correlation symmetry wrappers -/

/-- **ℤ^d correlation_neg_h direct** at Λ-induced: Z₂ odd-symmetry
under `h → -h`. `correlation ⟨J,-h,β⟩ A = (-1)^|A| · correlation ⟨J,h,β⟩ A`.
Concrete wrapper for `IsingModel.correlation_neg_h` (#754). -/
theorem correlation_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) A
      = (-1) ^ A.card * IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β A

/-- **ℤ^d magnetization_neg_h direct** at Λ-induced.
Concrete wrapper for `IsingModel.magnetization_neg_h` (#755). -/
theorem magnetization_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i
      = -IsingModel.magnetization
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  IsingModel.magnetization_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β i

/-! ## Moved: truncated{2,3,4}_neg_h wrappers

The three wrappers
`truncated2_neg_h_latticeGraph`,
`truncated3_neg_h_latticeGraph`,
`truncated4_neg_h_latticeGraph` now live in
`CorrelationSymmetryTruncatedNegH.lean`. -/


/-- **ℤ^d correlation_eq_abs_h_of_even_card direct** at Λ-induced:
for `|A|` even, `correlation ⟨J, h, β⟩ A = correlation ⟨J, |h|, β⟩ A`.
Concrete wrapper for `IsingModel.correlation_eq_abs_h_of_even_card`
(#760). -/
theorem correlation_eq_abs_h_of_even_card_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    (A : Finset (↑Λ : Type _)) (heven : Even A.card) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, β⟩ : IsingParams ℝ) A
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, |h|, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_eq_abs_h_of_even_card
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β A heven

/-! ### ℤ^d infinite-volume even-card correlation symmetry wrappers -/

/-- **ℤ^d correlationInfinite invariance under `h → -h`** (even `|A|`):
`correlationInfinite ⟨J,-h,β⟩ A = correlationInfinite ⟨J,h,β⟩ A`.
Concrete wrapper for `correlationInfinite_neg_h_of_even_card` (#765). -/
theorem correlationInfinite_neg_h_of_even_card_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (heven : Even A.card) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) A
      = correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  correlationInfinite_neg_h_of_even_card (IsingModel.latticeGraph d) Λ J h β A heven

/-- **ℤ^d correlationInfinite equals value at `|h|`** (even `|A|`):
concrete wrapper for `correlationInfinite_eq_abs_h_of_even_card` (#765). -/
theorem correlationInfinite_eq_abs_h_of_even_card_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (heven : Even A.card) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) A
      = correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) A :=
  correlationInfinite_eq_abs_h_of_even_card (IsingModel.latticeGraph d) Λ J h β A heven

/-! ## Moved: susceptibility h-symmetry wrappers

The four wrappers `susceptibility*_latticeGraph_*_abs_h` now live in
`CorrelationSymmetrySusceptibility.lean`. -/

end Ambient
end IsingModel
