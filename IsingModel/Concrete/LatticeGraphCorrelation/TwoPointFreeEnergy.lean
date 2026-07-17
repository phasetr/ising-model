import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergyAlongExhaustion + freeEnergyInfinite cubicExhaustion wrappers

Narrow child module for 34 ℤ^d `freeEnergyAlongExhaustion_latticeGraph`
/ `freeEnergyInfinite_latticeGraph` / cubicExhaustion convergence,
trivial-slice, monotonicity, neg-h / abs-h, `ge_log_two_cosh` /
`ge_log_two` / `bounds` wrappers, plus the two
`spontaneousMagnetization_latticeGraph_cubicExhaustion_monotone_{J, beta}`
variants. Theorem names are unchanged from the former `TwoPoint`
declarations.
-/

namespace IsingModel
namespace Ambient

/-! ## Moved: ℤ^d freeEnergyAlongExhaustion tendsto wrappers

The 9 ℤ^d `freeEnergyAlongExhaustion_latticeGraph_*_tendsto_*`
convergence wrappers (`J_zero_tendsto_of_hcard_add`,
`beta_zero_tendsto_of_hcard_add`, `tendsto_of_disjoint_tower`,
`tendsto_of_disjointTowerHypotheses`, `tendsto_of_superadditive`,
`tendsto_of_eventually_const`,
`J_zero_tendsto_of_eventually_nonempty`,
`beta_zero_tendsto_of_eventually_nonempty`,
`zero_params_tendsto_of_eventually_nonempty`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFreeEnergyAlongExTendsto`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: ℤ^d freeEnergyInfinite trivial-slice wrappers

The 9 ℤ^d `freeEnergyInfinite_latticeGraph_{beta_zero,zero_params,J_zero}_*`
trivial-slice wrappers (3 `_of_eventually_nonempty` + 3 unconditional +
3 `cubicExhaustion_*`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFreeEnergyInfTrivialSlices`.
The earlier import path is preserved by re-importing the new child.
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
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d freeEnergyInfinite monotonicity wrappers

The 7 ℤ^d `freeEnergyInfinite_latticeGraph_*monotone_*` wrappers
(`monotone_J`, `monotone_h`, `monotone_beta`, `monotone_abs_h`, plus
3 `cubicExhaustion_monotone_{J,h,beta}` variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFreeEnergyInfMonotone`.
The earlier import path is preserved by re-importing the new child.
-/

end Ambient

end IsingModel
