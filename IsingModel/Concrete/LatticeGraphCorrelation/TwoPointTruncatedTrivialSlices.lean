import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume

/-!
# The ℤ^d truncated three- and four-point functions at degenerate parameter records

Concrete statements about the anchored `truncated3TwoPoint` and `truncated4TwoPoint` at
`IsingModel.latticeGraph d` along `Ambient.cubicExhaustion d`, at parameter records that
switch part of the interaction off.

At vanishing external field the three-point function vanishes whenever the origin and the
separations are pairwise distinct, and that assumes no ferromagnetic condition. At
vanishing coupling the same vanishing holds under `Ferromagnetic` on the record
`⟨0, h, β⟩`, while the four-point function there has the closed form
`-2 * Real.tanh (β * h) ^ 4`, again at pairwise distinct sites; under that same condition
the closed form is `0` exactly when the external field vanishes and is strictly negative
otherwise.

At zero inverse temperature both functions vanish at arbitrary separations, distinct or
not, and under no hypothesis whatever: each infinite-volume correlation entering the Ursell
combination is itself zero there, and the combination is then closed by ring arithmetic.
No instance argument is taken anywhere in this module.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **`truncated3TwoPoint` at `h = 0` vanishes (pairwise distinct, nonzero)**:
`truncated3TwoPoint d ⟨J, 0, β⟩ r s = 0`.

Z₂ symmetry at `h = 0` forces all odd-cardinality spin products
(and hence the Ursell 3-point combination) to vanish.
Concrete specialisation of `truncated3Infinite_h_zero_of_distinct`. -/
theorem truncated3TwoPoint_h_zero_of_distinct
    (d : ℕ) (J β : ℝ)
    {r s : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hrs : r ≠ s)
    (hs : (0 : Fin d → ℤ) ≠ s) :
    truncated3TwoPoint d (⟨J, 0, β⟩ : IsingParams ℝ) r s = 0 :=
  truncated3Infinite_h_zero_of_distinct
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β
    hr hrs hs

/-- **`truncated3TwoPoint` at `J = 0` vanishes (pairwise distinct, nonzero)**:
for ferromagnetic `⟨0, h, β⟩` and `0 ≠ r, 0 ≠ s, r ≠ s`,
`truncated3TwoPoint d ⟨0, h, β⟩ r s = 0`.

Concrete ℤ^d specialisation of `truncated3Infinite_J_zero_of_pairwise_distinct`
at `i = 0, j = r, k = s`. Cluster property: at J=0 distinct sites are
independent, so the 3-point truncated function vanishes. -/
theorem truncated3TwoPoint_J_zero_of_distinct
    (d : ℕ) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {r s : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hrs : r ≠ s)
    (hs : (0 : Fin d → ℤ) ≠ s) :
    truncated3TwoPoint d (⟨0, h, β⟩ : IsingParams ℝ) r s = 0 :=
  truncated3Infinite_J_zero_of_pairwise_distinct
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) h β hf
    hr hrs hs

/-- **`truncated4TwoPoint` at `J = 0` closed form** (ferromagnetic,
pairwise distinct + nonzero separations):

`truncated4TwoPoint d ⟨0, h, β⟩ r s u = -2 · tanh(β · h)^4`.

Concrete ℤ^d specialisation of `truncated4Infinite_J_zero_of_pairwise_distinct`
at `i = 0, j = r, k = s, l = u`. Non-interacting Lebowitz 4-point
closed form. -/
theorem truncated4TwoPoint_J_zero_of_distinct
    (d : ℕ) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {r s u : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hs : (0 : Fin d → ℤ) ≠ s)
    (hu : (0 : Fin d → ℤ) ≠ u)
    (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u) :
    truncated4TwoPoint d (⟨0, h, β⟩ : IsingParams ℝ) r s u
      = -2 * Real.tanh (β * h) ^ 4 :=
  truncated4Infinite_J_zero_of_pairwise_distinct
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) h β hf
    hr hs hu hrs hru hsu

/-- **`truncated4TwoPoint` at `β = 0` vanishes**:
`truncated4TwoPoint d ⟨J, h, 0⟩ r s u = 0`.

All four Lebowitz terms vanish at β=0. -/
theorem truncated4TwoPoint_beta_zero
    (d : ℕ) (J h : ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d (⟨J, h, 0⟩ : IsingParams ℝ) r s u = 0 := by
  unfold truncated4TwoPoint truncated4Infinite
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r, s, u} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {s, u} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), s} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {r, u} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), u} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {r, s} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp)]
  ring

/-- **`truncated3TwoPoint` at `β = 0` vanishes**:
`truncated3TwoPoint d ⟨J, h, 0⟩ r s = 0`.

All seven Ursell terms (one 3-set, three pairs, three singletons) vanish
at β=0 via `correlationInfinite_beta_zero_vanish`. Direct computation. -/
theorem truncated3TwoPoint_beta_zero
    (d : ℕ) (J h : ℝ) (r s : Fin d → ℤ) :
    truncated3TwoPoint d (⟨J, h, 0⟩ : IsingParams ℝ) r s = 0 := by
  unfold truncated3TwoPoint truncated3Infinite
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r, s} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ)} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {r, s} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {r} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), s} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {s} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp)]
  ring

end Ambient

end IsingModel
