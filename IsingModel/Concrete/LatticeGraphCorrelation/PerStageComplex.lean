import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.ComplexAnalyticity
import IsingModel.PeierlsInfinite
import IsingModel.AmbientComplexAnalyticity
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume

/-!
# Concrete ℤ^d per-stage complex analyticity wrappers

Narrow child module for ℤ^d per-stage complex analyticity / continuity /
norm-bound wrappers extracted from `PerStage.lean` in PR #2051. Foundation
for the Montel / Vitali extraction. Each is a thin pass-through to the
corresponding ambient `partitionFunctionComplexAlongExhaustion_*` /
`freeEnergyComplexAlongExhaustion_*` lemma at `IsingModel.latticeGraph d`.
The `freeEnergyComplexAlongExhaustion_*_stage_latticeGraph` Lee-Yang
subdomain wrappers now live in `PerStageComplexFreeEnergy.lean`.
-/

namespace IsingModel
namespace Ambient

/-! #### Per-stage analyticity / continuity / norm-bound for the complex
along-exhaustion sequence (ℤ^d wrappers)

ℤ^d forwarders for the per-stage properties in
`IsingModel/AmbientComplexAnalyticity.lean`. Foundation for the Montel /
Vitali extraction. -/

/-- **ℤ^d per-stage entire in `h`** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_h_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) (h₀ : ℂ) :
    AnalyticAt ℂ
      (fun h => Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) h₀ :=
  Ambient.partitionFunctionComplexAlongExhaustion_analyticAt_h_stage
    (IsingModel.latticeGraph d) Λ J β n h₀

/-- **ℤ^d per-stage entire in `J`** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_J_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (h β : ℂ) (n : ℕ) (J₀ : ℂ) :
    AnalyticAt ℂ
      (fun J => Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) J₀ :=
  Ambient.partitionFunctionComplexAlongExhaustion_analyticAt_J_stage
    (IsingModel.latticeGraph d) Λ h β n J₀

/-- **ℤ^d per-stage entire in `β`** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_beta_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J h : ℂ) (n : ℕ) (β₀ : ℂ) :
    AnalyticAt ℂ
      (fun β => Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) β₀ :=
  Ambient.partitionFunctionComplexAlongExhaustion_analyticAt_beta_stage
    (IsingModel.latticeGraph d) Λ J h n β₀

/-- **ℤ^d per-stage joint entire** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_joint_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (n : ℕ) (z₀ : ℂ × ℂ × ℂ) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ z.1 z.2.1 z.2.2 n) z₀ :=
  Ambient.partitionFunctionComplexAlongExhaustion_analyticAt_joint_stage
    (IsingModel.latticeGraph d) Λ n z₀

/-- **ℤ^d per-stage `Continuous` in `h`** for
`partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_continuous_h_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) :
    Continuous
      (fun h => Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) :=
  Ambient.partitionFunctionComplexAlongExhaustion_continuous_h_stage
    (IsingModel.latticeGraph d) Λ J β n

/-! ## Moved: per-stage freeEnergyComplexAlongExhaustion wrappers

The four `freeEnergyComplexAlongExhaustion_*_stage_latticeGraph` wrappers
(`analyticAt_h`, `analyticOnNhd_leeYangSubdomain`,
`differentiableOn_leeYangSubdomain`, `continuousOn_leeYangSubdomain`)
now live in `PerStageComplexFreeEnergy.lean`. -/



/-- **ℤ^d per-stage locally-uniform norm bound** for
`partitionFunctionComplexAlongExhaustion`: `‖Z_ℂ_{Λ_n}‖ ≤ 2^|Λ_n| · exp(...)`
under `|Re h| ≤ R`. Montel input for the Vitali extraction. -/
theorem norm_partitionFunctionComplexAlongExhaustion_le_of_re_bound_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) {R : ℝ} {h : ℂ} (hh : |h.re| ≤ R) :
    ‖Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
      ≤ Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) *
          Real.exp (|β| *
            (|J| * (Ambient.inducedGraph
                (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
              + R * Fintype.card (↑(Λ.volume n) : Type _))) :=
  Ambient.norm_partitionFunctionComplexAlongExhaustion_le_of_re_bound_stage
    (IsingModel.latticeGraph d) Λ β J n hh

/-- **ℤ^d per-stage `Z_ℂ ≠ 0 on leeYangDomain`** for
`partitionFunctionComplexAlongExhaustion` (ferromagnetic). -/
theorem partitionFunctionComplexAlongExhaustion_ne_zero_on_leeYangDomain_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangDomain) :
    Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n ≠ 0 :=
  Ambient.partitionFunctionComplexAlongExhaustion_ne_zero_on_leeYangDomain_stage
    (IsingModel.latticeGraph d) Λ hβ hJ n hh

/-- **ℤ^d real-axis convergence of `freeEnergyComplexAlongExhaustion`**
(under `DisjointTowerHypotheses` + `BoundedEdgeDensity`): at real
parameters, the complex along-exhaustion sequence converges (in `ℂ`) to
`↑(freeEnergyInfinite G Λ p)`. Pass-through of the abstract lemma. -/
theorem freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p) :
    Filter.Tendsto
      (fun n => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
      Filter.atTop
      (nhds ((Ambient.freeEnergyInfinite
        (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ)) :=
  Ambient.freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
    (IsingModel.latticeGraph d) Λ p hBED hd

end Ambient

end IsingModel
