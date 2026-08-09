import IsingModel.AmbientLattice.MagnetizationInfinite
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d susceptibility at the external field and at its absolute value (§5.3)

Concrete `latticeGraph d` comparisons at a fixed site between the susceptibility at external
field `h` and at `|h|`.

The exact identity — the susceptibility at `|h|` equals the susceptibility at `h` plus the
magnetization at `|h|` minus the magnetization at `h` — holds with no hypothesis at all, on a
fixed finite volume and at a stage of an arbitrary `Ambient.Exhaustion` of `Fin d → ℤ` alike.
The one-sided inequality at a stage assumes `0 ≤ J` and `0 < β`; its infinite-volume
counterpart assumes those and, in addition, that the along-exhaustion susceptibility sequence
at `|h|` is bounded above. No instance argument is taken.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `χ_Λ(|h|) = χ_Λ(h) + M_Λ(|h|) − M_Λ(h)`** (no ferromagnetic
hypothesis). Concrete `latticeGraph d` wrapper for PR #776's
`susceptibilityΛ_eq_abs_h`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityΛ_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J h β : ℝ) (i : ↑Λ) :
    susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J, |h|, β⟩ : IsingParams ℝ) i
      = susceptibilityΛ (IsingModel.latticeGraph d) Λ
            (⟨J, h, β⟩ : IsingParams ℝ) i
          + magnetizationΛ (IsingModel.latticeGraph d) Λ
            (⟨J, |h|, β⟩ : IsingParams ℝ) i
          - magnetizationΛ (IsingModel.latticeGraph d) Λ
            (⟨J, h, β⟩ : IsingParams ℝ) i :=
  susceptibilityΛ_eq_abs_h (IsingModel.latticeGraph d) Λ J h β i

/-- **ℤ^d along-exhaustion `χ_along(|h|) = χ_along(h) + M_along(|h|) − M_along(h)`**
(no ferromagnetic hypothesis). Concrete `latticeGraph d` wrapper for PR
#777's `susceptibilityAlongExhaustion_eq_abs_h`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, |h|, β⟩ : IsingParams ℝ) i n
      = susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, h, β⟩ : IsingParams ℝ) i n
          + magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, |h|, β⟩ : IsingParams ℝ) i n
          - magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, h, β⟩ : IsingParams ℝ) i n :=
  susceptibilityAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d pointwise `χ_along(h) ≤ χ_along(|h|)`** under `0 ≤ J`, `0 < β`.
Concrete `latticeGraph d` wrapper for PR #778's
`susceptibilityAlongExhaustion_le_abs_h`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityAlongExhaustion_latticeGraph_le_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : Fin d → ℤ) (n : ℕ) :
    susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i n
      ≤ susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) i n :=
  susceptibilityAlongExhaustion_le_abs_h (IsingModel.latticeGraph d) Λ
    J h β hJ hβ i n

/-- **ℤ^d ∞-volume one-sided `χ_∞(h) ≤ χ_∞(|h|)`** (A-5′) under
`0 ≤ J`, `0 < β`, and `BddAbove` of the `|h|`-side along-exhaustion
sequence. Concrete `latticeGraph d` wrapper for PR #778's
`susceptibilityInfinite_le_abs_h`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityInfinite_latticeGraph_le_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : Fin d → ℤ)
    (hbd : BddAbove (Set.range fun n =>
      susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, |h|, β⟩ : IsingParams ℝ) i n)) :
    susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i
      ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) i :=
  susceptibilityInfinite_le_abs_h (IsingModel.latticeGraph d) Λ
    J h β hJ hβ i hbd


end Ambient
end IsingModel
