import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint

/-!
# ℤ^d two-point quantities at `r = 0` (Finset-collapse)

Narrow child module for two ℤ^d r=0 collapse wrappers extracted from
`TwoPoint.lean`:

* `twoPointFunction_zero`,
* `truncated2TwoPoint_zero`.

Both witness the Finset-vs-physics caveat: the literal `{0, 0}`
collapses to `{0}` in `Finset`, so the "two-point function at zero
separation" equals the magnetization (not the physical
`⟨σ_0^2⟩_∞ = 1`).
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## r = 0 collapse of the ℤ^d two-point quantities -/

/-- **`twoPointFunction` at `r = 0` collapses to the magnetization**:
`twoPointFunction d p 0 = magnetizationInfinite (latticeGraph d)
(cubicExhaustion d) p 0`.

This is the Finset-vs-physics caveat highlighted in the
`twoPointFunction` doc comment: the Finset literal `{0, 0}` collapses
to the singleton `{0}`, so the "two-point function at zero separation"
equals the magnetization, *not* the physical `⟨σ_0^2⟩ = 1`. -/
@[simp]
theorem twoPointFunction_zero (d : ℕ) (p : IsingParams ℝ) :
    twoPointFunction d p 0
      = magnetizationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p 0 := by
  unfold twoPointFunction magnetizationInfinite
  -- `{0, 0} = {0}` in Finset (duplicate collapse via insert_self).
  have : ({(0 : Fin d → ℤ), (0 : Fin d → ℤ)} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ)} := by
    simp
  rw [this]

/-- **`truncated2TwoPoint` at `r = 0`**: equals `M · (1 − M)` where `M` is
the site-independent magnetization at `0`.

Unfolds `truncated2TwoPoint d p 0 = truncated2Infinite ... p 0 0
= correlationInfinite ... {0, 0} − correlationInfinite ... {0} · correlationInfinite ... {0}
= M − M² = M(1 − M)`. -/
theorem truncated2TwoPoint_zero
    (d : ℕ) (p : IsingParams ℝ) :
    truncated2TwoPoint d p 0
      = (magnetizationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) p 0)
        * (1 - magnetizationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) p 0) := by
  unfold truncated2TwoPoint truncated2Infinite magnetizationInfinite
  -- `correlationInfinite ... {0, 0} = correlationInfinite ... {0}` by Finset collapse.
  have h_collapse : ({(0 : Fin d → ℤ), (0 : Fin d → ℤ)} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ)} := by simp
  rw [h_collapse]
  ring

end Ambient
end IsingModel
