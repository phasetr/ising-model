import IsingModel.AmbientLatticeSum.InfiniteHighTemp
import IsingModel.AmbientLatticeSum.InfiniteBounds
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergyInfinite cubicExhaustion wrappers

Narrow child module for 22 ℤ^d `freeEnergyInfinite_latticeGraph` /
cubicExhaustion trivial-slice, monotonicity, neg-h / abs-h,
`ge_log_two_cosh` / `ge_log_two` / `bounds` wrappers. Theorem names
are unchanged from the former `TwoPoint` declarations.
-/

namespace IsingModel
namespace Ambient

/-! ## Moved: ℤ^d freeEnergyInfinite trivial-slice wrappers

The 6 ℤ^d `freeEnergyInfinite_latticeGraph_{beta_zero,zero_params,J_zero}`
trivial-slice wrappers live in two child modules: the 3 unconditional ones in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFreeEnergyInfTrivialSlicesNonempty`
and the 3 `cubicExhaustion_*` ones in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFreeEnergyInfTrivialSlicesCubic`.
-/


/-- **Sharp lower bound** `freeEnergyInfinite ≥ log(2 cosh(βh))` on ℤ^d. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_ge_log_two_cosh
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (2 * Real.cosh (p.β * p.h))
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p := by
  refine freeEnergyInfinite_ge_log_two_cosh (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **Lower bound** `freeEnergyInfinite ≥ log 2` on ℤ^d (any Exhaustion
with caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_ge_log_two
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    Real.log 2 ≤ freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_ge_log_two (IsingModel.latticeGraph d) Λ p hf (c := c) hc

/-- **Sharp lower bound** `freeEnergyInfinite ≥ log(2 cosh(βh))` on ℤ^d
(any Exhaustion with caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_ge_log_two_cosh
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    Real.log (2 * Real.cosh (p.β * p.h))
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_ge_log_two_cosh (IsingModel.latticeGraph d)
    Λ p hf (c := c) hc

/-- **ℤ^d ∞-vol free-energy sandwich bound** (ferromagnetic):
`log 2 ≤ freeEnergyInfinite (latticeGraph d) (cubicExhaustion d) p
  ≤ log 2 + |β|·(|J|·d + |h|)`.

Capstone for the ∞-vol free-energy bounds on ℤ^d. Uses BED `c = d`
(PR #246) for the upper bound, and `freeEnergyInfinite_ge_log_two`
for the lower. Note: `[Nonempty (Fin d → ℤ)]` holds for every `d` since
`Fin 0 → ℤ` has exactly one element (empty function) and `Fin d → ℤ`
with `d ≥ 1` has `fun _ => 0`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_bounds
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log 2
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p
    ∧ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p
        ≤ Real.log 2 + |p.β| * (|p.J| * (d : ℝ) + |p.h|) := by
  have hc : ∀ n, ((Ambient.cubicExhaustion d).volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n)).edgeFinset.card : ℝ)
        ≤ (d : ℝ) * Fintype.card
            (↑((Ambient.cubicExhaustion d).volume n) : Type _) := by
    intro n _
    exact inducedLatticeGraph_card_edgeFinset_le d
      ((Ambient.cubicExhaustion d).volume n)
  refine ⟨?_, ?_⟩
  · exact freeEnergyInfinite_ge_log_two (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p hf hc
  · exact freeEnergyInfinite_le_uniform_upper_bound
      (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf hc

/-! ## Moved: ℤ^d freeEnergyInfinite h-symmetry wrappers

The 5 ℤ^d `freeEnergyInfinite_latticeGraph_*` h-symmetry / |h|-monotonicity
wrappers (`cubicExhaustion_monotone_abs_h`, `cubicExhaustion_neg_h`,
`cubicExhaustion_eq_abs_h`, `neg_h`, `eq_abs_h`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFreeEnergyInfHSymmetry`.
The shared `IsingModel.Concrete.LatticeGraphCorrelation.Umbrella.TwoPointUniform`
imports this module and the new child explicitly.
-/


/-! ## Moved: ℤ^d freeEnergyInfinite monotonicity wrappers

The 7 ℤ^d `freeEnergyInfinite_latticeGraph_*monotone_*` wrappers live in
two child modules: the 4 generic-`Λ` ones (`monotone_J`, `monotone_h`,
`monotone_beta`, `monotone_abs_h`) in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFreeEnergyInfMonotone`
and the 3 `cubicExhaustion_monotone_{J,h,beta}` variants in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFreeEnergyInfMonotoneCubicEx`.
-/

end Ambient

end IsingModel
