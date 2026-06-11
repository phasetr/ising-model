import IsingModel.AmbientComplexAnalyticity.ClosedBallPatches.GlobalBranchGlobalisation
import IsingModel.Concrete.CubicFreeEnergy

/-!
# GJ Theorem 4.6.2 on ℤ^d with the cubic exhaustion (GJ §4.6)

The fully instantiated form of GJ Theorem 4.6.2: on `latticeGraph d` with the cubic
exhaustion, for `0 < β` and `0 < J` there is a single function analytic on the whole
Lee-Yang cone agreeing with the infinite-volume free energy at every positive real field —
no remaining hypotheses. The bounded edge density and the field-uniform real-axis
convergence (the cubic tiling–liminf form of Proposition 4.6.1) discharge the inputs of the
abstract globalisation.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70 (with Proposition 4.6.1, p. 68).
-/

namespace IsingModel
namespace Ambient

/-- **Cubic volumes are nonempty subtypes**: the origin belongs to every cube. -/
instance cubicExhaustion_volume_nonempty (d n : ℕ) :
    Nonempty (↑((cubicExhaustion d).volume n) : Type _) :=
  ⟨⟨0, by
    rw [Exhaustion.volume, cubicExhaustion, mem_cubicBox]
    intro i
    simp⟩⟩

/-- **GJ Theorem 4.6.2 on ℤ^d (cubic exhaustion, fully instantiated)**: for `0 < β` and
`0 < J` there is a function analytic on the Lee-Yang cone `{|Im h| < Re h}` whose value at
every positive real field `x` is the infinite-volume free energy of the `d`-dimensional
nearest-neighbour Ising model at `(β, J, x)`. -/
theorem freeEnergyComplex_infiniteVolume_analyticOnNhd_leeYangDomain_latticeGraph_cubic
    (d : ℕ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g IsingModel.leeYangDomain ∧
      ∀ x : ℝ, 0 < x →
        g (x : ℂ) =
          ((freeEnergyInfinite (IsingModel.latticeGraph d) (cubicExhaustion d)
            ⟨J, x, β⟩ : ℝ) : ℂ) :=
  freeEnergyComplex_infiniteVolume_analyticOnNhd_leeYangDomain
    (IsingModel.latticeGraph d) (cubicExhaustion d) hβ hJ
    (boundedEdgeDensity_latticeGraph_cubicExhaustion d)
    fun x hx =>
      freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_tendsto d ⟨J, x, β⟩
        ⟨le_of_lt hJ, le_of_lt hx, hβ⟩

end Ambient
end IsingModel
