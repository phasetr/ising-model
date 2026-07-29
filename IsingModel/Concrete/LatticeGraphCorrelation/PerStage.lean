import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.ComplexAnalyticity
import IsingModel.PeierlsInfinite
import IsingModel.AmbientComplexAnalyticity
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume

/-!
# Per-stage complex analyticity, convergence, and critical-exponent bounds at ℤ^d

ℤ^d forwarders for:

1. **Per-stage analyticity / continuity / norm-bound** — entire in `h`, `J`, `β`;
   `AnalyticOnNhd` on the Lee–Yang subdomain; per-stage Montel norm bound;
   `Z_ℂ ≠ 0` on `leeYangDomain`. Foundation for the GJ §4.6 Vitali extraction.
2. **Per-stage Gibbs expectation + FKG** — along-exhaustion Gibbs unfolding and
   the GJ §4.4 FKG inequality per stage; GJ §5.4 Prop 5.4.2 `+`-BC bound.
3. **GJ §17.7 critical-exponent bounds** — `η ≥ 0` and `ζ ≥ 0` at finite and
   ∞ volume; absence of even bound states.
4. **Subgraph monotonicity and convergence** — `partitionFunction`, `correlation`,
   `freeEnergy` monotone in subgraph; convergence of monotone subgraph sequences.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.4, §4.6, §5.4, §17.7.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Moved: ℤ^d per-stage complex analyticity wrappers

The 8 remaining ℤ^d per-stage complex analyticity / continuity /
norm-bound wrappers
(`partitionFunctionComplexAlongExhaustion_continuous_h_stage_latticeGraph`,
`norm_partitionFunctionComplexAlongExhaustion_le_of_re_bound_stage_latticeGraph`,
`partitionFunctionComplexAlongExhaustion_ne_zero_on_leeYangDomain_stage_latticeGraph`,
`freeEnergyComplexAlongExhaustion_analyticAt_h_stage_latticeGraph`,
`freeEnergyComplexAlongExhaustion_analyticOnNhd_leeYangSubdomain_stage_latticeGraph`,
`freeEnergyComplexAlongExhaustion_differentiableOn_leeYangSubdomain_stage_latticeGraph`,
`freeEnergyComplexAlongExhaustion_continuousOn_leeYangSubdomain_stage_latticeGraph`,
`freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses_latticeGraph`)
live under `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex`,
in its `Bounds.PerStage` (3) and `Branches.StageLeeYang` (1) children and
in `PerStageComplexFreeEnergy` (4). The four
`partitionFunctionComplexAlongExhaustion_analyticAt_{h,J,beta,joint}_stage_latticeGraph`
wrappers were deleted; no consumer of them was found in this repository.
-/


/-! #### Per-stage Gibbs expectation along an exhaustion + FKG (ℤ^d) -/

/-- **ℤ^d `gibbsExpectationAlongExhaustion` unfolding**: equal to
`gibbsExpectation` on the `n`-th volume with the `n`-th family
member. -/
theorem gibbsExpectationAlongExhaustion_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (F : (n : ℕ) → IsingModel.Config (↑(Λ.volume n) : Type _) → ℝ) (n : ℕ) :
    Ambient.gibbsExpectationAlongExhaustion
        (IsingModel.latticeGraph d) Λ p F n
      = IsingModel.gibbsExpectation
          (Ambient.inducedGraph
            (IsingModel.latticeGraph d) (Λ.volume n)) p (F n) :=
  Ambient.gibbsExpectationAlongExhaustion_apply
    (IsingModel.latticeGraph d) Λ p F n

/-- **ℤ^d per-stage FKG along an exhaustion** (GJ §4.4):
for ferromagnetic `p` and per-stage nonneg monotone families
`F n, G_fn n : Config (↑(Λ.volume n)) → ℝ`, the FKG inequality holds at
every stage `n`. Pass-through of `fkg_ising_along_exhaustion`. -/
theorem fkg_ising_along_exhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (F G_fn : (n : ℕ) → IsingModel.Config (↑(Λ.volume n) : Type _) → ℝ)
    (hF_nn : ∀ n, 0 ≤ F n) (hG_nn : ∀ n, 0 ≤ G_fn n)
    (hF_mono : ∀ n, Monotone (F n)) (hG_mono : ∀ n, Monotone (G_fn n))
    (n : ℕ) :
    Ambient.gibbsExpectationAlongExhaustion
        (IsingModel.latticeGraph d) Λ p F n
      * Ambient.gibbsExpectationAlongExhaustion
          (IsingModel.latticeGraph d) Λ p G_fn n
      ≤ Ambient.gibbsExpectationAlongExhaustion
          (IsingModel.latticeGraph d) Λ p (fun k => F k * G_fn k) n :=
  Ambient.fkg_ising_along_exhaustion
    (IsingModel.latticeGraph d) Λ p hf F G_fn
    hF_nn hG_nn hF_mono hG_mono n

/-- **ℤ^d GJ §5.4 Prop 5.4.2 genuine ∞-vol `+`-BC bound** (Λ-induced,
`liminf` form): for any exhaustion `Λ : Ambient.Exhaustion (Fin d → ℤ)`
with per-stage `Preconnected` + `Fintype G_n.edgeSet` instances and the
Peierls exponential bound `hexp`, the `liminf`-based canonical ∞-vol
`+`-expectation of `σ ↦ Spin.sign ℝ (σ (i n))` satisfies
`1 − plusGibbsExpectationLiminf ≤ exp(-c·β)`. Pass-through of
`IsingModel.prop_5_4_2_plusGibbsExpectationLiminf_bound`, with
`DecidableRel` supplied via `classical`. -/
theorem prop_5_4_2_plusGibbsExpectationLiminf_bound_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (hconn : ∀ n, (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).Preconnected)
    (J β c : ℝ) (hβ : 0 < β) (hJ : 0 < J)
    (B : ∀ n, Finset (↑(Λ.volume n) : Type _))
    (hB : ∀ n, (B n).Nonempty)
    (i : ∀ n, (↑(Λ.volume n) : Type _))
    (hexp : ∀ n,
      2 * ((2 : ℝ) ^ Fintype.card (↑(Λ.volume n) : Type _)) *
          Real.exp (-2 * β * J) ≤
        Real.exp (-c * β)) :
    1 - IsingModel.plusGibbsExpectationLiminf
          (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) B
          (fun n σ => IsingModel.Spin.sign ℝ (σ (i n)))
      ≤ Real.exp (-c * β) := by
  classical
  exact IsingModel.prop_5_4_2_plusGibbsExpectationLiminf_bound
    (IsingModel.latticeGraph d) Λ hconn J β c hβ hJ B hB i hexp

/-! ## Moved: ℤ^d ζ/η/absence-of-even-bound-states wrappers

The 5 ℤ^d GJ §17.2/§17.7 critical-exponent wrappers
(`zeta_nonneg_finite_vol_latticeGraph`,
`eta_nonneg_infinite_vol_latticeGraph`,
`zeta_nonneg_infinite_vol_latticeGraph`,
`absence_of_even_bound_states_finite_vol_latticeGraph`,
`absence_of_even_bound_states_infinite_vol_latticeGraph`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.PerStageZetaEta`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d Λ-induced subgraph monotone/convergent wrappers

The 8 ℤ^d Λ-induced subgraph wrappers
(`partitionFunction_monotone_subgraph_latticeGraph`,
`correlation_monotone_subgraph_latticeGraph`,
`log_partitionFunction_monotone_subgraph_latticeGraph`,
`freeEnergy_monotone_subgraph_latticeGraph`,
`correlation_convergent_subgraph_latticeGraph`,
`magnetization_convergent_subgraph_latticeGraph`,
`twoPoint_convergent_subgraph_latticeGraph`,
`freeEnergy_convergent_subgraph_latticeGraph`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.PerStageSubgraph`.
The earlier import path is preserved by re-importing the new child.
-/

end Ambient
end IsingModel
