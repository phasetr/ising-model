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

/-! ## Moved: partitionFunctionComplexAlongEx per-stage analyticAt wrappers

The four wrappers
`partitionFunctionComplexAlongExhaustion_analyticAt_h_stage_latticeGraph`,
`partitionFunctionComplexAlongExhaustion_analyticAt_J_stage_latticeGraph`,
`partitionFunctionComplexAlongExhaustion_analyticAt_beta_stage_latticeGraph`,
`partitionFunctionComplexAlongExhaustion_analyticAt_joint_stage_latticeGraph`
now live in `PerStageComplexAnalyticStage.lean`. -/


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

/-- **ℤ^d per-stage compact-uniform norm bound** for
`partitionFunctionComplexAlongExhaustion`: on any compact field set `K`, a
single real-part bound `R` feeds all stage-wise `Z_ℂ` norm estimates. The
bound remains stage-dependent and is an envelope for later normalised estimates. -/
theorem norm_partitionFunctionComplexAlongExhaustion_le_on_isCompact_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (β J : ℝ) {K : Set ℂ} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ n, ∀ h ∈ K,
      ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        ≤ Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) *
            Real.exp (|β| *
              (|J| * (Ambient.inducedGraph
                  (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
                + R * Fintype.card (↑(Λ.volume n) : Type _))) :=
  Ambient.norm_partitionFunctionComplexAlongExhaustion_le_on_isCompact_stage
    (IsingModel.latticeGraph d) Λ β J hK

/-- **ℤ^d per-stage upper bound on normalised `Real.log ‖Z_ℂ‖`**:
under `|Re h| ≤ R` and nonvanishing, the complex partition-function envelope
gives the corresponding upper bound for
`Real.log ‖Z_{Λ_n}(h)‖ / |Λ_n|`. -/
theorem real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) [Nonempty (↑(Λ.volume n) : Type _)] {R : ℝ} {h : ℂ}
    (hZ : Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n ≠ 0)
    (hh : |h.re| ≤ R) :
    Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
      ≤ Real.log 2 +
        |β| * (|J| * (Ambient.inducedGraph
            (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
          + R * Fintype.card (↑(Λ.volume n) : Type _))
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  Ambient.real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_of_re_bound_stage
    (IsingModel.latticeGraph d) Λ β J n hZ hh

/-- **ℤ^d compact-field upper normalised-log handoff under bounded edge density**:
if `K` is compact, the exhaustion has bounded edge density, every stage is
nonempty, and `Z_{Λ_n}(h)` is nonzero on `K`, then
`Real.log ‖Z_{Λ_n}(h)‖ / |Λ_n|` has one stage-independent upper bound on `K`.
This is only the upper half of the later normalised absolute-log input. -/
theorem exists_real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (β J : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hZ : ∀ n, ∀ h ∈ K,
      Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n ≠ 0) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C :=
  Ambient.exists_real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_on_isCompact
    (IsingModel.latticeGraph d) Λ hBED β J hK hZ

/-- **ℤ^d stage free-energy bound from a normalised absolute-log bound**:
if `|log ‖Z_{Λ_n}(h)‖| / |Λ_n| ≤ C` at a nonempty stage, then the principal
complex free energy is bounded by `C + π / |Λ_n|`. This records the exact
normalised-log input needed after the compact `Z_ℂ` envelope. -/
theorem norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) [Nonempty (↑(Λ.volume n) : Type _)] {h : ℂ} {C : ℝ}
    (hC :
      |Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ‖Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
      ≤ C + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  Ambient.norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_stage
    (IsingModel.latticeGraph d) Λ β J n hC

/-- **ℤ^d setwise free-energy bound from normalised absolute-log control**:
if one constant `C` bounds `|log ‖Z_{Λ_n}(h)‖| / |Λ_n|` for every stage and
every field in `K`, then the ℤ^d along-exhaustion principal free energies obey
the corresponding stagewise bound on `K`. -/
theorem norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (β J : ℝ) {K : Set ℂ} {C : ℝ}
    (hC : ∀ n, ∀ h ∈ K,
      |Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ∀ n, ∀ h ∈ K,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        ≤ C + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  Ambient.norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set
    (IsingModel.latticeGraph d) Λ β J hC

/-- **ℤ^d stage-independent setwise free-energy bound from normalised
absolute-log control**: if one constant `C` bounds
`|log ‖Z_{Λ_n}(h)‖| / |Λ_n|` for every nonempty stage and every `h ∈ K`, then
the ℤ^d along-exhaustion principal free energies are bounded on `K` by the
single constant `C + π`. -/
theorem norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set_uniform_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (β J : ℝ) {K : Set ℂ} {C : ℝ}
    (hC : ∀ n, ∀ h ∈ K,
      |Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ∀ n, ∀ h ∈ K,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        ≤ C + Real.pi :=
  Ambient.norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set_uniform
    (IsingModel.latticeGraph d) Λ β J hC

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

/-- **ℤ^d compact-field upper normalised-log bound on Lee-Yang compact sets**:
on compact subsets of `leeYangDomain`, Lee-Yang nonvanishing discharges the
nonzero hypothesis in the compact upper normalised-log handoff. -/
theorem exists_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_ly_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C :=
  Ambient.exists_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_leeYangDomain
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hK hKsub

/-- **ℤ^d Lee-Yang compact absolute normalised-log handoff from lower control**:
on compact `K ⊆ leeYangDomain`, the Lee-Yang upper normalised-log bound and a
stage-uniform lower normalised-log hypothesis yield the absolute normalised-log
control consumed by the free-energy bounds. -/
theorem exists_abs_log_norm_div_card_le_lower_ly_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hLower : ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      |Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C :=
  Ambient.exists_abs_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_lower_leeYang
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hK hKsub hLower

/-- **ℤ^d lower normalised-log handoff from polynomial-factor witnesses**:
if every stage and field in `K` has a positive Lee-Yang polynomial-factor
lower witness whose normalised logarithm is uniformly bounded below, then the
complex partition functions satisfy the lower normalised-log hypothesis used
by the Lee-Yang locally bounded family handoff. -/
theorem exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_of_poly_lower_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J R : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) {K : Set ℂ}
    (hR : ∀ h ∈ K, |h.re| ≤ R)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  Ambient.exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_of_poly_lower
    (IsingModel.latticeGraph d) Λ hβ hJ hR hPolyLower

/-- **ℤ^d Lee-Yang compact locally bounded free-energy family from lower
control**: on compact `K ⊆ leeYangDomain`, a stage-uniform lower
normalised-log hypothesis combines with the Lee-Yang upper bound to give one
constant `C` with `‖f_n(h)‖ ≤ C + π` for all stages and all `h ∈ K`. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_lower_log_ly_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hLower : ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_lower_log_leeYang
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hK hKsub hLower

/-- **ℤ^d Lee-Yang compact locally bounded free-energy family from polynomial
lower witnesses**: on compact `K ⊆ leeYangDomain`, a uniform lower
normalised-log bound for polynomial-factor witnesses yields one constant `C`
with `‖f_n(h)‖ ≤ C + π` for all stages and all `h ∈ K`. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_ly_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J R : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hR : ∀ h ∈ K, |h.re| ≤ R)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hK hKsub hR hPolyLower

/-- **ℤ^d compact Lee-Yang locally bounded free-energy family from polynomial
lower witnesses**: compactness supplies the real-part bound, so only the
polynomial-witness lower normalised-log input remains as an explicit
hypothesis. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_ly_latticeGraph_of_isCompact
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_of_isCompact
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hK hKsub hPolyLower

/-- **ℤ^d ball-local Lee-Yang locally bounded free-energy family from
polynomial lower witnesses**: a polynomial-witness lower normalised-log input
on a closed Lee-Yang ball gives `‖f_n(h)‖ ≤ C + π` on the corresponding open
ball. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_ly_latticeGraph_on_ball
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J ρ : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hsub : Metric.closedBall h₀ ρ ⊆ IsingModel.leeYangDomain)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ Metric.closedBall h₀ ρ,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_on_ball
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hsub hPolyLower

/-- **ℤ^d point-local Lee-Yang locally bounded free-energy family from
polynomial lower witnesses**: around any Lee-Yang point, a radius-dependent
polynomial-witness lower normalised-log input on a closed Lee-Yang ball gives
`‖f_n(h)‖ ≤ C + π` on the corresponding open ball. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_ly_latticeGraph_around
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain)
    (hPolyLower : ∀ ρ : ℝ, 0 < ρ →
      Metric.closedBall h₀ ρ ⊆ IsingModel.leeYangDomain →
      ∃ Lε : ℝ, ∀ n, ∀ h ∈ Metric.closedBall h₀ ρ,
        ∃ ε : ℝ, 0 < ε ∧
          ε ≤ ‖(IsingModel.isingEdgePoly
            (IsingModel.graphToEdgeList
              (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (Real.exp (-2 * β * J)))).eval
            (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
          -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_around
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hmem hPolyLower

/-- **ℤ^d compact Lee-Yang polynomial lower witnesses**: compact containment
in `leeYangDomain` supplies the stage-uniform lower normalised-log bound for
the Lee-Yang polynomial witnesses via the root-product estimate. -/
theorem exists_poly_lower_norm_isingEdgePoly_eval_leeYangFugacityVec_latticeGraph_on_isCompact
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain) :
    ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  Ambient.exists_poly_lower_norm_isingEdgePoly_eval_leeYangFugacityVec_on_isCompact
    (IsingModel.latticeGraph d) Λ hβ hJ hK hKsub

/-- **ℤ^d compact Lee-Yang lower normalised-log bound**: the root-product
polynomial lower bound discharges the lower normalised-log hypothesis on
compact subsets of `leeYangDomain`. -/
theorem exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_ly_latticeGraph_of_isCompact
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J R : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hR : ∀ h ∈ K, |h.re| ≤ R) :
    ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  Ambient.exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_leeYang_of_isCompact
    (IsingModel.latticeGraph d) Λ hβ hJ hK hKsub hR

/-- **ℤ^d compact Lee-Yang locally bounded free-energy family**: on compact
`K ⊆ leeYangDomain`, the root-product polynomial lower bound removes the
explicit polynomial-witness hypothesis and yields `‖f_n(h)‖ ≤ C + π`. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_latticeGraph_of_isCompact
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_of_isCompact
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hK hKsub

/-- **ℤ^d ball-local Lee-Yang locally bounded free-energy family**: a closed
ball contained in `leeYangDomain` gives `‖f_n(h)‖ ≤ C + π` on the
corresponding open ball without any remaining polynomial-witness hypothesis. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_latticeGraph_on_ball
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J ρ : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hsub : Metric.closedBall h₀ ρ ⊆ IsingModel.leeYangDomain) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hsub

/-- **ℤ^d point-local Lee-Yang locally bounded free-energy family**: every
point of `leeYangDomain` has a ball on which the finite-volume free-energy
family is uniformly bounded, with polynomial lower-log control discharged by
the root-product estimate. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_latticeGraph_around
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi :=
  Ambient.exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_around
    (IsingModel.latticeGraph d) Λ hBED hβ hJ hmem

/-! #### Per-stage Lee-Yang branch wrappers -/

/-- **ℤ^d per-stage Lee-Yang local branch** for
`freeEnergyComplexAlongExhaustion`: at a nonempty stage and any
`h₀ ∈ leeYangDomain`, an analytic local branch recovers the stage
partition function at the basepoint and agrees there with the stage
principal free energy. -/
theorem freeEnergyComplexAlongExhaustion_exists_analyticAt_branch_leeYangDomain_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    [Nonempty (↑(Λ.volume n) : Type _)]
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticAt ℂ f h₀
      ∧ Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f h₀)
          = Ambient.partitionFunctionComplexAlongExhaustion
              (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n
      ∧ f h₀ = Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_exists_analyticAt_branch_leeYangDomain_stage
    (IsingModel.latticeGraph d) Λ hβ hJ n hmem

/-- **ℤ^d per-stage Lee-Yang branch family** for
`freeEnergyComplexAlongExhaustion`, in pointwise `∀ h₀ ∈ leeYangDomain`
form at a fixed nonempty stage. -/
theorem freeEnergyComplexAlongExhaustion_analyticBranch_leeYangDomain_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    [Nonempty (↑(Λ.volume n) : Type _)] :
    ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ f : ℂ → ℂ,
          AnalyticAt ℂ f h₀
        ∧ Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f h₀)
            = Ambient.partitionFunctionComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n
        ∧ f h₀ = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_analyticBranch_leeYangDomain_stage
    (IsingModel.latticeGraph d) Λ hβ hJ n

/-- **ℤ^d per-stage Lee-Yang local branch on a ball** for
`freeEnergyComplexAlongExhaustion`: the local analytic branch is analytic on
the ball and its exponential recovers the stage partition function throughout
that ball. -/
theorem freeEnergyComplexAlongExhaustion_exists_analyticOnNhd_branch_ball_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    [Nonempty (↑(Λ.volume n) : Type _)]
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
            = Ambient.partitionFunctionComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ (J : ℂ) z (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_exists_analyticOnNhd_branch_ball_stage
    (IsingModel.latticeGraph d) Λ hβ hJ n hr hsub

/-- **ℤ^d strong per-stage Lee-Yang local branch on a ball** for
`freeEnergyComplexAlongExhaustion`: the same branch carries
`AnalyticOnNhd`, the ball-wide exponential identity, and basepoint agreement
with the stage principal free energy. -/
theorem freeEnergyComplexAlongExhaustion_exists_analyticOnNhd_branch_ball_stage_strong_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    [Nonempty (↑(Λ.volume n) : Type _)]
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f (Metric.ball h₀ r)
      ∧ (∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
            = Ambient.partitionFunctionComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ (J : ℂ) z (β : ℂ) n)
      ∧ f h₀ = Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_exists_analyticOnNhd_branch_ball_stage_strong
    (IsingModel.latticeGraph d) Λ hβ hJ n hr hsub

/-- **ℤ^d all-stages Lee-Yang branch family** for
`freeEnergyComplexAlongExhaustion`: if all exhaustion stages are
nonempty, every stage admits the finite-volume local branch form on the
full Lee-Yang domain in pointwise basepoint form. -/
theorem freeEnergyComplexAlongExhaustion_analyticBranch_leeYangDomain_all_stages_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ n, ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ f : ℂ → ℂ,
          AnalyticAt ℂ f h₀
        ∧ Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f h₀)
            = Ambient.partitionFunctionComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n
        ∧ f h₀ = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_analyticBranch_leeYangDomain_all_stages
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **ℤ^d all-stages Lee-Yang local branches on balls** for
`freeEnergyComplexAlongExhaustion`: if all stages are nonempty, every stage
admits a local analytic branch on each ball contained in `leeYangDomain`,
with the exponential identity holding throughout the ball. -/
theorem freeEnergyComplexAlongExhaustion_analyticOnNhd_branch_ball_all_stages_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ n, ∀ {h₀ : ℂ} {r : ℝ}, 0 < r →
      Metric.ball h₀ r ⊆ IsingModel.leeYangDomain →
      ∃ f : ℂ → ℂ,
          AnalyticOnNhd ℂ f (Metric.ball h₀ r)
        ∧ ∀ z ∈ Metric.ball h₀ r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (J : ℂ) z (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_analyticOnNhd_branch_ball_all_stages
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **ℤ^d strong all-stages Lee-Yang local branches on balls** for
`freeEnergyComplexAlongExhaustion`: the same local branch witness carries
`AnalyticOnNhd`, the ball-wide exponential identity, and basepoint agreement
with the stage principal free energy. -/
theorem freeEnergyComplexAlongExhaustion_analyticOnNhd_branch_ball_all_stages_strong_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ n, ∀ {h₀ : ℂ} {r : ℝ}, 0 < r →
      Metric.ball h₀ r ⊆ IsingModel.leeYangDomain →
      ∃ f : ℂ → ℂ,
          AnalyticOnNhd ℂ f (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (J : ℂ) z (β : ℂ) n)
        ∧ f h₀ = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_analyticOnNhd_branch_ball_all_stages_strong
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **ℤ^d pointwise-normalised all-stage Lee-Yang branch data from positive
real parameters**: pass-through of the ambient pre-Montel branch-choice
package constructor at `latticeGraph d`. -/
theorem exists_leeYangPointwiseNormalisedAllStageBranchData_of_positive_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    Nonempty
      (Ambient.LeeYangPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (J : ℂ) (β : ℂ)) :=
  Ambient.exists_leeYangPointwiseNormalisedAllStageBranchData_of_positive_real
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **ℤ^d closed-ball pointwise-normalised all-stage Lee-Yang branch data from
positive real parameters**: pass-through of the ambient closed-ball
pre-Montel branch-choice package constructor at `latticeGraph d`. -/
theorem
    exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    Nonempty
      (Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (J : ℂ) (β : ℂ)) :=
  Ambient.exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
    (IsingModel.latticeGraph d) Λ hβ hJ

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

/-! #### Conditional Vitali assembly for the complex free-energy limit -/

/-- **ℤ^d conditional Vitali assembly on an open set** for
`freeEnergyComplexAlongExhaustion`: a locally uniform limit of the
per-stage holomorphic complex free energies is holomorphic on the same
open set. -/
theorem freeEnergyComplexAlongExhaustion_vitali_bridge_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {U : Set ℂ} (hU : IsOpen U) (J β : ℂ) {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) U)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n)
      f Filter.atTop U) :
    DifferentiableOn ℂ f U :=
  Ambient.freeEnergyComplexAlongExhaustion_vitali_bridge
    (IsingModel.latticeGraph d) Λ hU J β hF hconv

/-- **ℤ^d conditional Vitali assembly on `leeYangDomain`** for
`freeEnergyComplexAlongExhaustion`. This is the concrete Step 5 handoff
for the infinite-volume proof of GJ §4.6 Thm 4.6.2. -/
theorem freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n)
      IsingModel.leeYangDomain)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n)
      f Filter.atTop IsingModel.leeYangDomain) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain
    (IsingModel.latticeGraph d) Λ J β hF hconv

/-- **ℤ^d real-axis identification of a locally uniform Vitali limit**:
the Lee-Yang locally uniform limit of the complex along-exhaustion
free energies agrees at real parameters with the cast of
`freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_limit_eq_freeEnergyInfinite_at_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {f : ℂ → ℂ}
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (p.J : ℂ) h (p.β : ℂ) n)
      f Filter.atTop IsingModel.leeYangDomain) :
    f (p.h : ℂ) =
      ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_limit_eq_freeEnergyInfinite_at_real
    (IsingModel.latticeGraph d) Λ p hBED hd hp hconv

/-- **ℤ^d conditional Vitali assembly with real-axis identification**:
combines holomorphicity of the Lee-Yang locally uniform limit with its
identification at a real parameter by `freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain_identified_at_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (p.J : ℂ) h (p.β : ℂ) n)
      IsingModel.leeYangDomain)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (p.J : ℂ) h (p.β : ℂ) n)
      f Filter.atTop IsingModel.leeYangDomain) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain ∧
      f (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain_identified_at_real
    (IsingModel.latticeGraph d) Λ p hBED hd hF hp hconv

/-! #### Local branch-family Vitali assembly on Lee-Yang balls -/

/-- **ℤ^d local branch-family Vitali bridge on a ball**: if a chosen
per-stage branch family is analytic on a ball and converges locally uniformly
there, then its limit is holomorphic on that ball. The branch hypothesis keeps
the ball-wide exponential identity and centre normalisation in the same shape
as the strong Lee-Yang branch witnesses. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_bridge_ball_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {h₀ : ℂ} {r : ℝ}
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ n,
      AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n)
        ∧ F n h₀ = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J h₀ β n)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f (Metric.ball h₀ r) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_vitali_bridge_ball
    (IsingModel.latticeGraph d) Λ J β hbranch hconv

/-- **ℤ^d local branch-family Vitali bridge with centre identification**:
for a ball centred at the real parameter `p.h`, a locally-uniform limit of
normalised branch witnesses is holomorphic on the ball and agrees at the
centre with the real infinite-volume free energy. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_ball_identified_at_center_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {r : ℝ} (hr : 0 < r)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ n,
      AnalyticOnNhd ℂ (F n) (Metric.ball (p.h : ℂ) r)
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) n)
        ∧ F n (p.h : ℂ) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop
      (Metric.ball (p.h : ℂ) r)) :
    DifferentiableOn ℂ f (Metric.ball (p.h : ℂ) r) ∧
      f (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_vitali_ball_identified_at_center
    (IsingModel.latticeGraph d) Λ p hBED hd hr hbranch hconv

/-- **ℤ^d local-cover branch-family Vitali bridge on `leeYangDomain`**:
if every Lee-Yang point has a ball on which a chosen per-stage branch family
converges locally uniformly to the same `f`, then `f` is holomorphic on the
whole Lee-Yang domain. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_localCover_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {f : ℂ → ℂ}
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ n,
            AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
                    = Ambient.partitionFunctionComplexAlongExhaustion
                        (IsingModel.latticeGraph d) Λ J z β n)
              ∧ F n h₀ = Ambient.freeEnergyComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J h₀ β n)
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_vitali_localCover
    (IsingModel.latticeGraph d) Λ J β hlocal

/-- **ℤ^d open-cover branch-family patching handoff on `leeYangDomain`**:
if a Lee-Yang open cover carries compatible local branch-family limits, then
the limits patch to one differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_openCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {α : Type*} {U : α → Set ℂ}
    {F : α → ℕ → ℂ → ℂ} {f : α → ℂ → ℂ}
    (hUopen : ∀ i, IsOpen (U i))
    (hcover : IsingModel.leeYangDomain ⊆ ⋃ i, U i)
    (hbranch : ∀ i n,
      AnalyticOnNhd ℂ (F i n) (U i)
        ∧ (∀ z ∈ U i,
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F i n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n))
    (hconv : ∀ i, TendstoLocallyUniformlyOn (F i) (f i) Filter.atTop (U i))
    (hcompat : ∀ i j, Set.EqOn (f i) (f j) (U i ∩ U j)) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (f i) (U i)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_openCover_patch
    (IsingModel.latticeGraph d) Λ J β hUopen hcover hbranch hconv hcompat

/-- **ℤ^d pointed local-cover branch-family patching handoff on
`leeYangDomain`**: compatible local limits on Lee-Yang balls centred at every
domain point patch to one differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_localCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (f h₀) (f h₁)
        (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁))) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (f h₀) (Metric.ball (h₀ : ℂ) (r h₀))) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_localCover_patch
    (IsingModel.latticeGraph d) Λ J β hr hsub hbranch hconv hcompat

/-- **ℤ^d structured pointed local-cover branch-limit patching handoff on
`leeYangDomain`**: point-indexed `Ambient.LeeYangLocalBranchLimit` data with
compatible local limits patches to one differentiable function on
`leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_branchLimitData_localCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Ambient.LeeYangLocalBranchLimit (IsingModel.latticeGraph d) Λ J β h₀)
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (data h₀).limitFun (data h₁).limitFun
        (Metric.ball (h₀ : ℂ) (data h₀).radius
          ∩ Metric.ball (h₁ : ℂ) (data h₁).radius)) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLimitData_localCover_patch
    (IsingModel.latticeGraph d) Λ J β data hcompat

/-- **ℤ^d packaged structured local-cover branch-limit patching handoff on
`leeYangDomain`**: a compatible `Ambient.LeeYangLocalBranchLimitFamily` patches
to one differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_branchLimitFamily_localCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (family : Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (family.data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLimitFamily_localCover_patch
    (IsingModel.latticeGraph d) Λ J β family

/-- **ℤ^d structured local-cover branch-limit patching with real-axis
identification**: compatible packaged local-cover data patch to a
differentiable function on `leeYangDomain`, and if the package centred at a
real Lee-Yang field is normalised to the finite-volume free-energy sequence,
the patched function agrees there with `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_branchLimitData_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (data : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Ambient.LeeYangLocalBranchLimit
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ) h₀)
    (hcenter : ∀ n,
      (data ⟨(p.h : ℂ), hp⟩).branchFamily n (p.h : ℂ)
        = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (data h₀).limitFun (data h₁).limitFun
        (Metric.ball (h₀ : ℂ) (data h₀).radius
          ∩ Metric.ball (h₁ : ℂ) (data h₁).radius)) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLimitData_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd hp data hcenter hcompat

/-- **ℤ^d packaged structured local-cover branch-limit patching with real-axis
identification**: a compatible `Ambient.LeeYangLocalBranchLimitFamily` patches
to a differentiable function on `leeYangDomain`, and a real-centre
normalisation identifies the patched value with `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_branchLimitFamily_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (family : Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (hcenter : ∀ n,
      (family.data ⟨(p.h : ℂ), hp⟩).branchFamily n (p.h : ℂ)
        = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (family.data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLimitFamily_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd hp family hcenter

/-- **ℤ^d real-centred packaged structured local-cover branch-limit endpoint**:
a compatible real-centred `Ambient.LeeYangRealBranchLimitFamily` patches to a
differentiable function on `leeYangDomain`, and its packaged centre
normalisation identifies the patched value with `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_realBranchLimitFamily_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (realFamily : Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (realFamily.family.data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_realBranchLimitFamily_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd realFamily

/-- **ℤ^d packaged local-cover branch-limit family from raw branch data**:
raw pointwise Lee-Yang local-cover branch data with locally uniform limits and
pairwise overlap compatibility can be bundled into
`LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_branchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (f h₀) (f h₁)
        (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁))) :
    Nonempty (Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :=
  Ambient.exists_leeYangLocalBranchLimitFamily_of_branchData
    (IsingModel.latticeGraph d) Λ J β hr hsub hbranch hconv hcompat

/-- **ℤ^d real-centred packaged local-cover branch-limit family from raw
branch data**: raw coherent Lee-Yang local-cover branch data, real-centre
membership, and centre normalisation can be bundled into
`LeeYangRealBranchLimitFamily`. -/
theorem exists_leeYangRealBranchLimitFamily_of_branchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (f h₀) (f h₁)
        (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁)))
    (hcenter : ∀ n,
      F ⟨(p.h : ℂ), hp⟩ n (p.h : ℂ)
        = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    Nonempty (Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :=
  Ambient.exists_leeYangRealBranchLimitFamily_of_branchData
    (IsingModel.latticeGraph d) Λ p hp hr hsub hbranch hconv hcompat hcenter

/-- **ℤ^d packaged local-cover branch-limit family from eventual overlap
data**: raw Lee-Yang local-cover branch data whose stage branches are
eventually equal on every overlap can be bundled into
`LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_branchData_eventuallyEqOn_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hoverlap : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      ∀ᶠ n in Filter.atTop,
        Set.EqOn (F h₀ n) (F h₁ n)
          (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁))) :
    Nonempty (Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :=
  Ambient.exists_leeYangLocalBranchLimitFamily_of_branchData_eventuallyEqOn
    (IsingModel.latticeGraph d) Λ J β hr hsub hbranch hconv hoverlap

/-- **ℤ^d real-centred packaged local-cover branch-limit family from eventual
overlap data**: raw Lee-Yang local-cover branch data whose stage branches are
eventually equal on every overlap, plus real-centre normalisation, can be
bundled into `LeeYangRealBranchLimitFamily`. -/
theorem exists_leeYangRealBranchLimitFamily_of_branchData_eventuallyEqOn_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hoverlap : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      ∀ᶠ n in Filter.atTop,
        Set.EqOn (F h₀ n) (F h₁ n)
          (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁)))
    (hcenter : ∀ n,
      F ⟨(p.h : ℂ), hp⟩ n (p.h : ℂ)
        = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    Nonempty (Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :=
  Ambient.exists_leeYangRealBranchLimitFamily_of_branchData_eventuallyEqOn
    (IsingModel.latticeGraph d) Λ p hp hr hsub hbranch hconv hoverlap hcenter

/-- **ℤ^d packaged local-cover branch-limit family from structured
eventual-overlap branch data**: the structured local-cover input packages
directly into `Ambient.LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_eventualOverlapBranchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    Nonempty (Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :=
  Ambient.exists_leeYangLocalBranchLimitFamily_of_eventualOverlapBranchData
    (IsingModel.latticeGraph d) Λ J β data

/-- **ℤ^d packaged local-cover branch-limit family from pointwise-normalised
eventual-overlap branch data**: the pointwise-normalised package exposes the
underlying structured eventual-overlap branch data, which packages directly
into `Ambient.LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_pointwiseNormEventualData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    Nonempty (Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :=
  Ambient.exists_leeYangLocalBranchLimitFamily_of_pointwiseNormEventualData
    (IsingModel.latticeGraph d) Λ J β data

/-- **ℤ^d real-centred packaged local-cover branch-limit family from
structured eventual-overlap branch data**: the real-centred structured
local-cover input packages directly into `Ambient.LeeYangRealBranchLimitFamily`.
-/
theorem exists_leeYangRealBranchLimitFamily_of_realEventualOverlapBranchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (data : Ambient.LeeYangRealEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :=
  Ambient.exists_leeYangRealBranchLimitFamily_of_realEventualOverlapBranchData
    (IsingModel.latticeGraph d) Λ p data

/-- **ℤ^d real-centred packaged local-cover branch-limit family from
pointwise-normalised eventual-overlap branch data**: pointwise-normalised real
eventual-overlap data projects to the structured real package, then packages
directly into `Ambient.LeeYangRealBranchLimitFamily`. -/
theorem exists_leeYangRealBranchLimitFamily_of_pointwiseNormEventualData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (data : Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :=
  Ambient.exists_leeYangRealBranchLimitFamily_of_pointwiseNormEventualData
    (IsingModel.latticeGraph d) Λ p data

/-- **ℤ^d structured eventual-overlap local-cover patching handoff on
`leeYangDomain`**: structured eventual-overlap data patch directly to one
differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (data.limitFun h₀)
          (Metric.ball (h₀ : ℂ) (data.radius h₀))) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_patch
    (IsingModel.latticeGraph d) Λ J β data

/-- **ℤ^d pointwise-normalised eventual-overlap local-cover patching handoff
on `leeYangDomain`**: pointwise-normalised structured data expose the
underlying eventual-overlap package, whose local limits patch to one
differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (data.branchData.limitFun h₀)
          (Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_patch
    (IsingModel.latticeGraph d) Λ J β data

/-- **ℤ^d structured eventual-overlap local-cover family and patching handoff
on `leeYangDomain`**: structured eventual-overlap data produce both the
compatible local-cover family and one differentiable patch. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_family_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ family : Ambient.LeeYangLocalBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_family_patch
    (IsingModel.latticeGraph d) Λ J β data

/-- **ℤ^d pointwise-normalised eventual-overlap local-cover family and
patching handoff on `leeYangDomain`**: pointwise-normalised structured data
produce both the compatible local-cover family and one differentiable patch. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_family_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ family : Ambient.LeeYangLocalBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.branchData.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_family_patch
    (IsingModel.latticeGraph d) Λ J β data

/-- **ℤ^d raw branch-data local-cover patching with real-axis
identification**: raw coherent local-cover branch data package into
`LeeYangRealBranchLimitFamily`, then patch to a function differentiable on
`leeYangDomain` and identified at the real centre. -/
theorem freeEnergyComplexAlongExhaustion_branchData_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (f h₀) (f h₁)
        (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁)))
    (hcenter : ∀ n,
      F ⟨(p.h : ℂ), hp⟩ n (p.h : ℂ)
        = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    ∃ realFamily : Ambient.LeeYangRealBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (f h₀) (Metric.ball (h₀ : ℂ) (r h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchData_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd hp hr hsub hbranch hconv hcompat hcenter

/-- **ℤ^d eventual-overlap raw branch-data local-cover patching with real-axis
identification**: raw local-cover branch data whose stage branches are
eventually equal on every overlap package into `LeeYangRealBranchLimitFamily`,
then patch to a differentiable function identified at the real centre. -/
theorem freeEnergyComplexAlongExhaustion_branchData_eventuallyEqOn_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hoverlap : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      ∀ᶠ n in Filter.atTop,
        Set.EqOn (F h₀ n) (F h₁ n)
          (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁)))
    (hcenter : ∀ n,
      F ⟨(p.h : ℂ), hp⟩ n (p.h : ℂ)
        = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    ∃ realFamily : Ambient.LeeYangRealBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (f h₀) (Metric.ball (h₀ : ℂ) (r h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchData_eventuallyEqOn_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd hp hr hsub hbranch hconv hoverlap hcenter

/-- **ℤ^d structured eventual-overlap branch-data local-cover patching with
real-axis identification**: a real-centred structured local-cover package is
converted to `Ambient.LeeYangRealBranchLimitFamily`, then patched and
identified at the real centre. -/
theorem freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (data : Ambient.LeeYangRealEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    ∃ realFamily : Ambient.LeeYangRealBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.branchData.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd data

/-- **ℤ^d pointwise-normalised eventual-overlap data local-cover patching with
real-axis identification**: pointwise-normalised structured data projects to
the real-centred structured package, then patches and identifies the real
centre. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (data : Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    ∃ realFamily : Ambient.LeeYangRealBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.pointwiseData.branchData.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.pointwiseData.branchData.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd data

/-- **ℤ^d compact finite subcover from a packaged Lee-Yang local-cover
family**: a compact target in `leeYangDomain` is covered by finitely many of
the packaged Lee-Yang local-cover balls. -/
theorem exists_finset_cover_of_isCompact_leeYangLocalBranchLimitFamily_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (family : Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ t : Finset {h : ℂ // h ∈ IsingModel.leeYangDomain},
      K ⊆ ⋃ h₀ ∈ t,
        Metric.ball (h₀ : ℂ) (family.data h₀).radius :=
  Ambient.exists_finset_cover_of_isCompact_leeYangLocalBranchLimitFamily
    (IsingModel.latticeGraph d) Λ J β hK hKsub family

/-- **ℤ^d compact finite subcover from a real-centred packaged Lee-Yang local
cover**: a compact target containing the real field is covered by finitely many
packaged Lee-Yang local-cover balls, with the real centre included in the
finite set. -/
theorem exists_finset_cover_of_isCompact_leeYangRealBranchLimitFamily_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (realFamily : Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :
    ∃ t : Finset {h : ℂ // h ∈ IsingModel.leeYangDomain},
      ⟨(p.h : ℂ), realFamily.centre_mem⟩ ∈ t ∧
      K ⊆ ⋃ h₀ ∈ t,
        Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius :=
  Ambient.exists_finset_cover_of_isCompact_leeYangRealBranchLimitFamily
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK realFamily

/-- **ℤ^d compact local-cover finite geometry from a real-centred packaged
Lee-Yang local cover**: the finite subcover of a compact target is enumerated
over `Fin n`, retaining positive radii, Lee-Yang ball containment, target
coverage, and a selected real-centre index. -/
theorem exists_compactLocalCoverFinGeometry_of_leeYangRealBranchLimitFamily_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (realFamily : Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangCompactLocalCoverFinGeometry
      (IsingModel.latticeGraph d) Λ p K) :=
  Ambient.exists_compactLocalCoverFinGeometry_of_leeYangRealBranchLimitFamily
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK realFamily

/-- **ℤ^d compact local-cover `Fin n` geometry from structured
eventual-overlap branch data**: structured real-centred eventual-overlap branch
data first packages into a real branch-limit family, then compactness extracts
and enumerates a finite local-cover geometry over `K`. -/
theorem exists_compactLocalCoverFinGeometry_of_realEventualOverlapBranchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangRealEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangCompactLocalCoverFinGeometry
      (IsingModel.latticeGraph d) Λ p K) :=
  Ambient.exists_compactLocalCoverFinGeometry_of_realEventualOverlapBranchData
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK data

/-- **ℤ^d compact local-cover `Fin n` geometry from pointwise-normalised
eventual-overlap branch data**: pointwise-normalised real eventual-overlap data
projects to the structured real package, then compactness extracts and
enumerates a finite local-cover geometry over `K`. -/
theorem exists_compactLocalCoverFinGeometry_of_pointwiseNormEventualData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangCompactLocalCoverFinGeometry
      (IsingModel.latticeGraph d) Λ p K) :=
  Ambient.exists_compactLocalCoverFinGeometry_of_pointwiseNormEventualData
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK data

/-- **ℤ^d local-cover branch-family Vitali bridge with real-axis
identification**: a coherent local Lee-Yang ball cover with locally-uniform
convergence to a common `f` makes `f` holomorphic on `leeYangDomain`, and at a
real Lee-Yang centre it agrees with `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {f : ℂ → ℂ}
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ n,
            AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
                    = Ambient.partitionFunctionComplexAlongExhaustion
                        (IsingModel.latticeGraph d) Λ
                        (p.J : ℂ) z (p.β : ℂ) n)
              ∧ F n h₀ = Ambient.freeEnergyComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ
                  (p.J : ℂ) h₀ (p.β : ℂ) n)
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain ∧
      f (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_vitali_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd hp hlocal

/-! #### Subsequence local branch-family Vitali assembly -/

/-- **ℤ^d subsequence local branch-family Vitali bridge on a ball**:
if a Montel-extracted subsequence of per-stage branch witnesses is analytic on
a ball and converges locally uniformly there, then its limit is holomorphic on
that ball. The branch identities are written at stage `σ m`. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {h₀ : ℂ} {r : ℝ}
    {σ : ℕ → ℕ}
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ m,
      AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β (σ m))
        ∧ F m h₀ = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J h₀ β (σ m))
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f (Metric.ball h₀ r) :=
  Ambient.freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
    (IsingModel.latticeGraph d) Λ J β hbranch hconv

/-- **ℤ^d subsequence local branch-family Vitali bridge with centre
identification**: for a ball centred at the real parameter `p.h`, a locally
uniform limit of subsequence branch witnesses is holomorphic on the ball and
agrees at the centre with the real infinite-volume free energy. -/
theorem
freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {r : ℝ} (hr : 0 < r)
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ m,
      AnalyticOnNhd ℂ (F m) (Metric.ball (p.h : ℂ) r)
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) (σ m))
        ∧ F m (p.h : ℂ) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m))
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop
      (Metric.ball (p.h : ℂ) r)) :
    DifferentiableOn ℂ f (Metric.ball (p.h : ℂ) r) ∧
      f (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center
    (IsingModel.latticeGraph d) Λ p hBED hd hr hσ hbranch hconv

/-- **ℤ^d subsequence local-cover branch-family Vitali bridge on
`leeYangDomain`**: if every Lee-Yang point has a ball on which a
subsequence-indexed branch family converges locally uniformly to the same
`f`, then `f` is holomorphic on the whole Lee-Yang domain. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {σ : ℕ → ℕ} {f : ℂ → ℂ}
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ m,
            AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
                    = Ambient.partitionFunctionComplexAlongExhaustion
                        (IsingModel.latticeGraph d) Λ J z β (σ m))
              ∧ F m h₀ = Ambient.freeEnergyComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J h₀ β (σ m))
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover
    (IsingModel.latticeGraph d) Λ J β hlocal

/-- **ℤ^d subsequence local-cover branch-family Vitali bridge with real-axis
identification**: a coherent local Lee-Yang cover of subsequence branch
families converging locally uniformly to a common `f` makes `f` holomorphic on
`leeYangDomain`, and at a real Lee-Yang centre it agrees with
`↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {f : ℂ → ℂ}
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ m,
            AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
                    = Ambient.partitionFunctionComplexAlongExhaustion
                        (IsingModel.latticeGraph d) Λ
                        (p.J : ℂ) z (p.β : ℂ) (σ m))
              ∧ F m h₀ = Ambient.freeEnergyComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ
                  (p.J : ℂ) h₀ (p.β : ℂ) (σ m))
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain ∧
      f (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd hσ hp hlocal

/-- **ℤ^d compact-open extraction plus subsequence Vitali bridge on a ball**:
if local branch witnesses on a ball are represented by continuous maps in a
compact subset of the compact-open function space, then a subsequence
converges locally uniformly and its limit is holomorphic on the ball. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_bridge_ball_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {h₀ : ℂ} {r : ℝ}
    {F : ℕ → ℂ → ℂ}
    {A : Set C(Metric.ball h₀ r, ℂ)}
    {Fc : ℕ → C(Metric.ball h₀ r, ℂ)}
    (hA : IsCompact A)
    (hFc_mem : ∀ n, Fc n ∈ A)
    (hFres : ∀ n z (hz : z ∈ Metric.ball h₀ r),
      F n z = Fc n ⟨z, hz⟩)
    (hbranch : ∀ n,
      AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n)
        ∧ F n h₀ = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J h₀ β n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : ℂ → ℂ,
        (∃ fc : C(Metric.ball h₀ r, ℂ),
          fc ∈ A ∧ ∀ z (hz : z ∈ Metric.ball h₀ r), f z = fc ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F (σ m) z) f Filter.atTop (Metric.ball h₀ r) ∧
        DifferentiableOn ℂ f (Metric.ball h₀ r) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_bridge_ball
    (IsingModel.latticeGraph d) Λ J β hA hFc_mem hFres hbranch

/-- **ℤ^d compact-open extraction plus subsequence Vitali bridge with centre
identification**: for a ball centred at a real Lee-Yang parameter, compact-open
compactness of the branch family yields a locally uniformly convergent
subsequence whose limit is holomorphic and agrees at the centre with the real
infinite-volume free energy. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_ball_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {r : ℝ} (hr : 0 < r)
    {F : ℕ → ℂ → ℂ}
    {A : Set C(Metric.ball (p.h : ℂ) r, ℂ)}
    {Fc : ℕ → C(Metric.ball (p.h : ℂ) r, ℂ)}
    (hA : IsCompact A)
    (hFc_mem : ∀ n, Fc n ∈ A)
    (hFres : ∀ n z (hz : z ∈ Metric.ball (p.h : ℂ) r),
      F n z = Fc n ⟨z, hz⟩)
    (hbranch : ∀ n,
      AnalyticOnNhd ℂ (F n) (Metric.ball (p.h : ℂ) r)
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ
                  (p.J : ℂ) z (p.β : ℂ) n)
        ∧ F n (p.h : ℂ) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : ℂ → ℂ,
        (∃ fc : C(Metric.ball (p.h : ℂ) r, ℂ),
          fc ∈ A ∧
            ∀ z (hz : z ∈ Metric.ball (p.h : ℂ) r), f z = fc ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F (σ m) z) f Filter.atTop (Metric.ball (p.h : ℂ) r) ∧
        DifferentiableOn ℂ f (Metric.ball (p.h : ℂ) r) ∧
        f (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_ball_real
    (IsingModel.latticeGraph d) Λ p hBED hd hr hA hFc_mem hFres hbranch

/-- **ℤ^d two-ball compact-open diagonal extraction plus subsequence Vitali
bridge**: compact-open compactness on two Lee-Yang balls gives one common
subsequence, locally uniform convergence on both balls, and holomorphic limits
on both balls. This does not assert overlap compatibility of the two limits. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_two_ball_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {h01 h02 : ℂ} {r1 r2 : ℝ}
    {F1 F2 : ℕ → ℂ → ℂ}
    {A1 : Set C(Metric.ball h01 r1, ℂ)}
    {A2 : Set C(Metric.ball h02 r2, ℂ)}
    {Fc1 : ℕ → C(Metric.ball h01 r1, ℂ)}
    {Fc2 : ℕ → C(Metric.ball h02 r2, ℂ)}
    (hA1 : IsCompact A1) (hA2 : IsCompact A2)
    (hFc1_mem : ∀ n, Fc1 n ∈ A1)
    (hFc2_mem : ∀ n, Fc2 n ∈ A2)
    (hFres1 : ∀ n z (hz : z ∈ Metric.ball h01 r1),
      F1 n z = Fc1 n ⟨z, hz⟩)
    (hFres2 : ∀ n z (hz : z ∈ Metric.ball h02 r2),
      F2 n z = Fc2 n ⟨z, hz⟩)
    (hbranch1 : ∀ n,
      AnalyticOnNhd ℂ (F1 n) (Metric.ball h01 r1)
        ∧ (∀ z ∈ Metric.ball h01 r1,
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F1 n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n)
        ∧ F1 n h01 = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J h01 β n)
    (hbranch2 : ∀ n,
      AnalyticOnNhd ℂ (F2 n) (Metric.ball h02 r2)
        ∧ (∀ z ∈ Metric.ball h02 r2,
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F2 n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n)
        ∧ F2 n h02 = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J h02 β n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∃ f1 : ℂ → ℂ,
        (∃ fc1 : C(Metric.ball h01 r1, ℂ),
          fc1 ∈ A1 ∧ ∀ z (hz : z ∈ Metric.ball h01 r1), f1 z = fc1 ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F1 (σ m) z) f1 Filter.atTop (Metric.ball h01 r1) ∧
        DifferentiableOn ℂ f1 (Metric.ball h01 r1)) ∧
      (∃ f2 : ℂ → ℂ,
        (∃ fc2 : C(Metric.ball h02 r2, ℂ),
          fc2 ∈ A2 ∧ ∀ z (hz : z ∈ Metric.ball h02 r2), f2 z = fc2 ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F2 (σ m) z) f2 Filter.atTop (Metric.ball h02 r2) ∧
        DifferentiableOn ℂ f2 (Metric.ball h02 r2)) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_two_ball
    (IsingModel.latticeGraph d) Λ J β hA1 hA2 hFc1_mem hFc2_mem
    hFres1 hFres2 hbranch1 hbranch2

/-- **ℤ^d finite-ball compact-open diagonal extraction plus subsequence Vitali
bridge**: compact-open compactness on finitely many Lee-Yang balls gives one
common subsequence, locally uniform convergence on every ball, and holomorphic
limits on every ball. This does not assert overlap compatibility of the local
limits. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β m)
        ∧ F i m (h0 i) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J (h0 i) β m) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i, ∃ f : ℂ → ℂ,
        (∃ fc : C(Metric.ball (h0 i) (r i), ℂ),
          fc ∈ A i ∧
            ∀ z (hz : z ∈ Metric.ball (h0 i) (r i)), f z = fc ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F i (σ m) z) f Filter.atTop (Metric.ball (h0 i) (r i)) ∧
        DifferentiableOn ℂ f (Metric.ball (h0 i) (r i)) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball
    (IsingModel.latticeGraph d) Λ J β n hA hFc_mem hFres hbranch

/-- **ℤ^d finite-ball compact-open diagonal extraction with overlap
compatibility**: if the stage branches in the finite-ball compact-open handoff
are eventually equal on every pairwise overlap, the extracted holomorphic local
limits are pairwise equal on those overlaps. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_fin_ball_overlap_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β m)
        ∧ F i m (h0 i) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J (h0 i) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : Fin n → ℂ → ℂ,
        (∀ i,
          (∃ fc : C(Metric.ball (h0 i) (r i), ℂ),
            fc ∈ A i ∧
              ∀ z (hz : z ∈ Metric.ball (h0 i) (r i)), f i z = fc ⟨z, hz⟩) ∧
          TendstoLocallyUniformlyOn
            (fun m z => F i (σ m) z) (f i) Filter.atTop
              (Metric.ball (h0 i) (r i)) ∧
          DifferentiableOn ℂ (f i) (Metric.ball (h0 i) (r i))) ∧
        ∀ i j, Set.EqOn (f i) (f j)
          (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j)) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_overlap
    (IsingModel.latticeGraph d) Λ J β n hA hFc_mem hFres hbranch hoverlap

/-- **ℤ^d packaged finite compact-open subsequence branch-limit family**:
compact-open compactness on finitely many balls, plus eventual stage-level
overlap equality, produces a structured finite subsequence branch-limit
family. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β m)
        ∧ F i m (h0 i) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J (h0 i) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))) :
    Nonempty (Ambient.LeeYangFiniteSubseqBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β n h0 r) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen
    (IsingModel.latticeGraph d) Λ J β n hA hFc_mem hFres hbranch hoverlap

/-- **ℤ^d pointwise-normalised all-stage data to finite compact-open
subsequence package**: restricts pre-Montel all-stage branch choices to
finitely many Lee-Yang centres, then applies the ambient finite compact-open
diagonal handoff under compact-open compactness and explicit eventual overlap
equality. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCompactOpen_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    Nonempty (Ambient.LeeYangFiniteSubseqBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β n
      (fun i => (center i : ℂ))
      (fun i => data.branchData.radius (center i))) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCompactOpen
    (IsingModel.latticeGraph d) Λ J β n center data hA hFc_mem hFres hoverlap

/-- **ℤ^d packaged finite subsequence branch-limit patching**: a compatible
`Ambient.LeeYangFiniteSubseqBranchLimitFamily` patches to one function
differentiable on the finite union of its balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    (family : Ambient.LeeYangFiniteSubseqBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β n h0 r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
      DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch
    (IsingModel.latticeGraph d) Λ J β n family

/-- **ℤ^d packaged finite subsequence branch-limit patching with real-centre
identification**: if one finite-cover ball is centred at the real field `p.h`,
then a compatible `Ambient.LeeYangFiniteSubseqBranchLimitFamily` patches on the
finite union of balls and the patched value at the real centre agrees with
`↑Ambient.freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    (family : Ambient.LeeYangFiniteSubseqBranchLimitFamily
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ) n h0 r)
    (i₀ : Fin n)
    (hcenter : h0 i₀ = (p.h : ℂ))
    (hr : 0 < r i₀) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
      DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_real
    (IsingModel.latticeGraph d) Λ p hBED hd n family i₀ hcenter hr

/-- **ℤ^d finite Lee-Yang cover branch-limit patching**: a compatible finite
Lee-Yang cover package patches to one differentiable function on the finite
union of its Lee-Yang balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (cover : Ambient.LeeYangFiniteCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β n center r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g
        (⋃ i : Fin n,
          Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch
    (IsingModel.latticeGraph d) Λ J β n cover

/-- **ℤ^d finite Lee-Yang cover branch-limit patching with real-centre
identification**: if one finite-cover ball is centred at the real field `p.h`,
the finite-union patch agrees there with `↑Ambient.freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (cover : Ambient.LeeYangFiniteCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ) n center r)
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g
        (⋃ i : Fin n,
          Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch_real
    (IsingModel.latticeGraph d) Λ p hBED hd n cover i₀ hcenter

/-- **ℤ^d finite real-centred Lee-Yang cover branch-limit patching**: a finite
Lee-Yang cover package with a bundled real-centre index patches to one
differentiable function on the finite union, with value
`↑Ambient.freeEnergyInfinite` at the real centre. -/
theorem freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (realCover : Ambient.LeeYangFiniteRealCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p n center r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (realCover.cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g
        (⋃ i : Fin n,
          Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_patch
    (IsingModel.latticeGraph d) Λ p hBED hd n realCover

/-- **ℤ^d compact finite real-centred Lee-Yang cover patching**: a compact
target set covered by a finite real-centred Lee-Yang cover inherits the
finite-cover patch, restricted to differentiability on the compact target,
while preserving the real-centre identification. -/
theorem freeEnergyComplexAlongExhaustion_compactFiniteRealCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (K : Set ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p K n center r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g K ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_compactFiniteRealCover_patch
    (IsingModel.latticeGraph d) Λ p hBED hd K n compactCover

/-- **ℤ^d finite compact-open extraction to a patched finite family**:
compact-open compactness on finitely many balls and eventual stage-level
overlap equality produce both a packaged finite subsequence branch-limit family
and a patched function on the finite union of balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteCompactOpenBranchLimitFamily_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β m)
        ∧ F i m (h0 i) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J (h0 i) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))) :
    ∃ family : Ambient.LeeYangFiniteSubseqBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β n h0 r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
        DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen_patch
    (IsingModel.latticeGraph d) Λ J β n hA hFc_mem hFres hbranch hoverlap

/-- **ℤ^d pointwise-normalised all-stage data to finite compact-open patch**:
restricts pre-Montel all-stage branch choices to finitely many Lee-Yang
centres, builds the finite compact-open subsequence package, and patches the
compatible local limits on the finite union of selected balls. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCompactOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    ∃ family : Ambient.LeeYangFiniteSubseqBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β n
        (fun i => (center i : ℂ))
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball (center i : ℂ) (data.branchData.radius (center i))) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCompactOpen_patch
    (IsingModel.latticeGraph d) Λ J β n center data hA hFc_mem hFres hoverlap

/-- **ℤ^d pointwise-normalised all-stage data to finite Lee-Yang cover
package**: restricts pre-Montel all-stage branch choices to finitely many
Lee-Yang centres, then packages the finite compact-open subsequence extraction
as a finite Lee-Yang cover branch-limit family. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    Nonempty (Ambient.LeeYangFiniteCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β n center
      (fun i => data.branchData.radius (center i))) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen
    (IsingModel.latticeGraph d) Λ J β n center data hA hFc_mem hFres hoverlap

/-- **ℤ^d pointwise-normalised all-stage data to finite Lee-Yang cover patch**:
restricts pre-Montel all-stage branch choices to finitely many Lee-Yang
centres, builds the finite Lee-Yang cover package, and patches the compatible
local limits on the finite union of selected balls. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    ∃ cover : Ambient.LeeYangFiniteCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β n center
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (cover.family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball (center i : ℂ) (data.branchData.radius (center i))) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen_patch
    (IsingModel.latticeGraph d) Λ J β n center data hA hFc_mem hFres hoverlap

/-- **ℤ^d pointwise-normalised all-stage data to finite real-centred
Lee-Yang cover patch**: restricts all-stage branch choices to finitely many
Lee-Yang centres and uses a selected real-centre index to identify the patched
value with `↑Ambient.freeEnergyInfinite`. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finRealCOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j))))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ realCover : Ambient.LeeYangFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p n center
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (realCover.cover.family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball (center i : ℂ) (data.branchData.radius (center i))) ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finRealCoverCOpen_patch
    (IsingModel.latticeGraph d) Λ p hBED hd n center data hA hFc_mem hFres
    hoverlap i₀ hcenter

/-- **ℤ^d pointwise-normalised all-stage data to compact real-centred
Lee-Yang cover patch**: for a compact target covered by finitely many selected
all-stage Lee-Yang balls, produces the compact finite real-centred cover
package and a patch differentiable on the compact target. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (K : Set ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (hKcover : K ⊆
      ⋃ i : Fin n,
        Metric.ball (center i : ℂ) (data.branchData.radius (center i)))
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j))))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K n center
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCoverCOpen_patch
    (IsingModel.latticeGraph d) Λ p hBED hd K n center data hK hKsub hpK
    hKcover hA hFc_mem hFres hoverlap i₀ hcenter

/-- **ℤ^d compact real finite-cover geometry from pointwise-normalised
all-stage data**: compactness extracts finitely many all-stage Lee-Yang balls
covering `K`, with a selected centre at the real field. -/
theorem
    exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    Nonempty (Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data) :=
  Ambient.exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage compact finite geometry to compact
real-cover patch**: feeds compactness-extracted all-stage centres into the
compact real-cover patch bridge. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormAllStage_compactRealCOpen_patch_geom_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    {A : ∀ i : Fin geom.n,
      Set C(Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i)), ℂ)}
    {Fc : ∀ i : Fin geom.n, ℕ →
      C(Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i))),
      data.branchData.branchFamily (geom.center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (geom.center i) m)
        (data.branchData.branchFamily (geom.center j) m)
        (Metric.ball (geom.center i : ℂ) (data.branchData.radius (geom.center i))
          ∩ Metric.ball (geom.center j : ℂ)
            (data.branchData.radius (geom.center j)))) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCOpen_patch_geom
    (IsingModel.latticeGraph d) Λ p hBED hd data geom hA hFc_mem hFres hoverlap

/-- **ℤ^d pointwise-normalised all-stage compact-open data to compact
real-cover patch**: packaged compact-open data for the selected all-stage
geometry feeds the compact real-cover patch bridge. -/
theorem freeEnergyComplexAlongExhaustion_allStageCOpenData_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (cOpen : Ambient.LeeYangPointwiseNormAllStageCompactRealCOpenData
      (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageCOpenData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom cOpen

/-- **ℤ^d compact target to packaged all-stage compact-open patch input**:
compactness of `K` extracts the finite all-stage geometry, and packaged
compact-open data then yields the compact real-cover patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageCOpenData_patch_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealCOpenData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageCOpenData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage range-closure compact-open data to
compact real-cover patch**: compactness of the closure of the selected
stage-restriction range supplies the compact-open carrier for the all-stage
patch bridge. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (rangeClosure :
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom rangeClosure

/-- **ℤ^d compact target to all-stage range-closure compact-open patch input**:
compactness of `K` extracts the finite all-stage geometry, and compactness of
each closure of the selected stage-restriction range yields the compact
real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage relatively compact range data to
compact real-cover patch**: compact carriers containing the selected
stage-restriction ranges supply compactness of the range closures. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (relCompact :
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom relCompact

/-- **ℤ^d compact target to all-stage relatively compact range patch input**:
compactness of `K` extracts the finite all-stage geometry, and compact
carriers containing each selected stage-restriction range yield the compact
real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage Arzelà-Ascoli data to compact
real-cover patch**: compactness of the pointwise function-space image and
equicontinuity for the selected all-stage geometry supply compact-open
compactness via Arzelà-Ascoli. -/
theorem freeEnergyComplexAlongExhaustion_allStageAscoliData_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (ascoli : Ambient.LeeYangPointwiseNormAllStageCompactRealAscoliData
      (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom ascoli

/-- **ℤ^d compact target to all-stage Arzelà-Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry, and Ascoli-style
compact-open data for that geometry yields the compact real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageAscoliData_patch_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageAscoliData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage closed-product Ascoli data to compact
real-cover patch**: compact pointwise targets, closed pointwise image, and
equicontinuity for the selected all-stage geometry supply the Ascoli input. -/
theorem freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (closedProduct :
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom closedProduct

/-- **ℤ^d compact target to all-stage closed-product Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry, and closed-product
Ascoli data for that geometry yields the compact real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage norm-bounded closed-product Ascoli
data to compact real-cover patch**: pointwise norm bounds supply the compact
closed-ball targets required by the closed-product Ascoli package. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (normBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom normBounded

/-- **ℤ^d compact target to all-stage norm-bounded closed-product Ascoli patch
input**: compactness of `K` extracts the finite all-stage geometry, and
norm-bounded closed-product Ascoli data for that geometry yields the compact
real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage range norm-bounded Ascoli data to
compact real-cover patch**: range carriers reduce the norm-bounded Ascoli
input to stagewise pointwise norm bounds for the selected continuous
restrictions. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (rangeBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom rangeBounded

/-- **ℤ^d compact target to all-stage range norm-bounded Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry, and range
norm-bounded Ascoli data for that geometry yields the compact real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage range norm-bounded Ascoli data to a
relatively compact range patch**: closedness, stagewise norm bounds, and
equicontinuity make the actual stage-restriction range a compact carrier. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (rangeBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom rangeBounded

/-- **ℤ^d compact target to all-stage range norm-bounded relatively compact
patch input**: compactness of `K` extracts the finite all-stage geometry, and
range norm-bounded Ascoli data supplies compact carriers for the actual
stage-restriction ranges. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d branch norm-bounded Ascoli data to a relatively compact range
patch**: branch-family pointwise norm bounds are transported to the selected
continuous restrictions and then fed to the relative-compactness bridge. -/
theorem freeEnergyComplexAlongExhaustion_branchNormBoundedRelCompact_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (branchBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchNormBoundedRelCompact_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom branchBounded

/-- **ℤ^d compact target to branch norm-bounded relatively compact patch
input**: compactness of `K` extracts the finite all-stage geometry, and branch
norm-bounded Ascoli data supplies the relative-compactness input. -/
theorem
    freeEnergyComplexAlongExhaustion_branchNormBoundedRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchNormBoundedRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d branch constant norm-bounded Ascoli data to a relatively compact
range patch**: ballwise constant branch-family bounds are converted to branch
pointwise bounds before applying the relative-compactness bridge. -/
theorem freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (constBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom constBounded

/-- **ℤ^d compact target to branch constant norm-bounded relatively compact
patch input**: compactness of `K` extracts the finite all-stage geometry, and
branch constant norm-bounded data supplies the relative-compactness input. -/
theorem
    freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d branch locally bounded Ascoli data to a relatively compact range
patch**: one branch-family bound is chosen on each selected ball and then fed
through the branch constant relative-compactness bridge. -/
theorem freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (locallyBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom locallyBounded

/-- **ℤ^d compact target to branch locally bounded relatively compact patch
input**: compactness of `K` extracts the finite all-stage geometry, and branch
locally bounded data supplies the relative-compactness input. -/
theorem
    freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d branch-deviation locally bounded Ascoli data to a relatively compact
range patch**: local boundedness of the principal finite-volume free energy
and a uniform branch-deviation bound yield the branch locally bounded input. -/
theorem
    freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (deviationBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom deviationBounded

/-- **ℤ^d compact target to branch-deviation locally bounded relatively compact
patch input**: compactness of `K` extracts the finite all-stage geometry, and
branch-deviation locally bounded data supplies the relative-compactness input.
-/
theorem
    freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d closed-ball branch-deviation data to a relatively compact range
patch**: closed-ball branch radii supply the principal finite-volume
free-energy local boundedness input; the remaining boundedness assumption is a
uniform branch-deviation estimate. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedData :
      Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K closedData.data)
    (closedBallDeviation :
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        (IsingModel.latticeGraph d) Λ p K closedData geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => closedData.data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedData.data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ closedData geom
    closedBallDeviation

/-- **ℤ^d compact target to closed-ball branch-deviation relatively compact
patch input**: compactness extracts the finite all-stage geometry from the
underlying closed-ball branch data, then the branch-deviation data supplies the
relative-compactness input. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (closedData :
      Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K closedData.data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
          (IsingModel.latticeGraph d) Λ p K closedData geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => closedData.data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedData.data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK closedData

/-- **ℤ^d positive-real compact target to closed-ball branch-deviation
relatively compact patch input**: positive real ferromagnetic parameters
construct the closed-ball all-stage branch data, compactness extracts the
finite geometry, and the remaining branch-deviation data supplies the
relative-compactness input. -/
theorem
freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K) :
    ∃ closedData :
        Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
          (IsingModel.latticeGraph d) Λ p K closedData.data,
        Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
            (IsingModel.latticeGraph d) Λ p K closedData geom →
          ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
              (IsingModel.latticeGraph d) Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) =
                ((Ambient.freeEnergyInfinite
                  (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK

/-- **ℤ^d pointwise-normalised all-stage branch norm-bounded Ascoli data to
compact real-cover patch**: branch-family pointwise norm bounds are
transported through the selected restriction identities and then fed to the
range norm-bounded Ascoli package. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchNormBoundedAscoliData_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (branchBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageBranchNormBoundedAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom branchBounded

set_option linter.style.longLine false

/-- **ℤ^d compact target to all-stage branch norm-bounded Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry, and branch
norm-bounded Ascoli data for that geometry yields the compact real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchNormBoundedAscoliData_patch_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageBranchNormBoundedAscoliData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

set_option linter.style.longLine true

/-- **ℤ^d pointwise-normalised all-stage branch constant norm-bounded Ascoli
data to compact real-cover patch**: ballwise constant branch-family norm bounds
are fed through the ambient branch norm-bounded Ascoli package. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchConstNormBoundedAscoliData_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (constBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageBranchConstNormBoundedAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom constBounded

/-- **ℤ^d compact target to all-stage branch constant norm-bounded Ascoli
patch input**: compactness of `K` extracts the finite all-stage geometry, and
branch constant norm-bounded Ascoli data for that geometry yields the compact
real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchConstAscoli_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  by
    exact
      freeEnergyComplexAlongExhaustion_allStageBranchConstNormBoundedAscoliData_patch_of_isCompact
        (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage branch locally bounded Ascoli data
to compact real-cover patch**: existential ballwise branch-family bounds are
chosen as constants and fed through the ambient branch constant norm-bounded
Ascoli package. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchLocallyBoundedAscoliData_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (locallyBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageBranchLocallyBoundedAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom locallyBounded

/-- **ℤ^d compact target to all-stage branch locally bounded Ascoli patch
input**: compactness of `K` extracts the finite all-stage geometry, and branch
locally bounded Ascoli data for that geometry yields the compact real-cover
patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchLocallyBoundedAscoli_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageBranchLocallyBoundedAscoliData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d finite compact-open extraction to a real-centre patch**:
compact-open compactness on finitely many balls, eventual stage-level overlap
equality, and a selected ball centred at the real field `p.h` produce a
patched function on the finite union of balls whose value at `p.h` is
`↑Ambient.freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteCompactOpenBranchLimitFamily_realPatch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m (h0 i) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (p.J : ℂ) (h0 i) (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j)))
    (i₀ : Fin n)
    (hcenter : h0 i₀ = (p.h : ℂ))
    (hr : 0 < r i₀) :
    ∃ family : Ambient.LeeYangFiniteSubseqBranchLimitFamily
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ) n h0 r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
        DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen_patch_real
    (IsingModel.latticeGraph d) Λ p hBED hd n hA hFc_mem hFres hbranch hoverlap
    i₀ hcenter hr

/-- **ℤ^d finite Lee-Yang cover compact-open extraction package**:
compact-open compactness on finitely many Lee-Yang-domain balls, plus eventual
stage-level overlap equality, produces a finite Lee-Yang cover branch-limit
family. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n,
      Set C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    (hr : ∀ i, 0 < r i)
    (hsub : ∀ i,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
        ⊆ IsingModel.leeYangDomain)
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
        ∧ (∀ z ∈ Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = Ambient.freeEnergyComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ J
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j))) :
    Nonempty (Ambient.LeeYangFiniteCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β n center r) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen
    (IsingModel.latticeGraph d) Λ J β n hr hsub hA hFc_mem hFres hbranch hoverlap

/-- **ℤ^d finite Lee-Yang cover compact-open extraction to a patch**:
compact-open compactness and eventual stage-level overlap equality produce
both the finite Lee-Yang cover package and a differentiable patch on the finite
union of its balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n,
      Set C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    (hr : ∀ i, 0 < r i)
    (hsub : ∀ i,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
        ⊆ IsingModel.leeYangDomain)
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
        ∧ (∀ z ∈ Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = Ambient.freeEnergyComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ J
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j))) :
    ∃ cover : Ambient.LeeYangFiniteCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β n center r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (cover.family.limitFun i)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen_patch
    (IsingModel.latticeGraph d) Λ J β n hr hsub hA hFc_mem hFres hbranch hoverlap

/-- **ℤ^d finite Lee-Yang cover compact-open extraction to a real-centre
patch**: compact-open compactness and eventual stage-level overlap equality
produce a finite Lee-Yang cover package and a finite-union patch whose
selected real-centre value is `↑Ambient.freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_realPatch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n,
      Set C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    (hr : ∀ i, 0 < r i)
    (hsub : ∀ i,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
        ⊆ IsingModel.leeYangDomain)
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
        ∧ (∀ z ∈ Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = Ambient.freeEnergyComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ
                (p.J : ℂ)
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j)))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ cover : Ambient.LeeYangFiniteCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ) n center r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (cover.family.limitFun i)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen_patch_real
    (IsingModel.latticeGraph d) Λ p hBED hd n hr hsub hA hFc_mem hFres
    hbranch hoverlap i₀ hcenter

/-- **ℤ^d finite Lee-Yang cover compact-open extraction to a real-centred
package and patch**: compact-open compactness and eventual stage-level overlap
equality produce a finite real-centred Lee-Yang cover package and a
finite-union patch whose selected real-centre value is
`↑Ambient.freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_compactOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n,
      Set C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    (hr : ∀ i, 0 < r i)
    (hsub : ∀ i,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
        ⊆ IsingModel.leeYangDomain)
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
        ∧ (∀ z ∈ Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = Ambient.freeEnergyComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ
                (p.J : ℂ)
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j)))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ realCover : Ambient.LeeYangFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p n center r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (realCover.cover.family.limitFun i)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_compactOpen_patch
    (IsingModel.latticeGraph d) Λ p hBED hd n hr hsub hA hFc_mem hFres
    hbranch hoverlap i₀ hcenter

/-- **ℤ^d compact finite Lee-Yang cover compact-open extraction to a
real-centred package and compact-target patch**: compact-open compactness and
eventual stage-level overlap equality produce a compact finite real-centred
Lee-Yang cover package and a patch differentiable on the compact target. -/
theorem freeEnergyComplexAlongExhaustion_compactFiniteRealCover_cOpenPatch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (K : Set ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n,
      Set C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (hKcover : K ⊆
      ⋃ i : Fin n,
        Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
    (hr : ∀ i, 0 < r i)
    (hsub : ∀ i,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
        ⊆ IsingModel.leeYangDomain)
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
        ∧ (∀ z ∈ Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = Ambient.freeEnergyComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ
                (p.J : ℂ)
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j)))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K n center r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_compactFiniteRealCover_cOpenPatch
    (IsingModel.latticeGraph d) Λ p hBED hd K n hK hKsub hpK hKcover hr hsub
    hA hFc_mem hFres hbranch hoverlap i₀ hcenter

/-- **ℤ^d compact local-cover `Fin n` geometry compact-open extraction to a
compact-target patch**: once the compact local-cover geometry has been
enumerated, compact-open compactness and eventual stage-level overlap equality
produce a compact finite real-centred Lee-Yang cover package and a patch
differentiable on the compact target. -/
theorem freeEnergyComplexAlongExhaustion_compactLocalCoverFinGeometry_cOpenPatch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (K : Set ℂ)
    (geometry :
      Ambient.LeeYangCompactLocalCoverFinGeometry (IsingModel.latticeGraph d) Λ p K)
    {F : Fin geometry.n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin geometry.n,
      Set C(Metric.ball
        ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
          (geometry.r i), ℂ)}
    {Fc : ∀ i : Fin geometry.n, ℕ →
      C(Metric.ball
        ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
          (geometry.r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
          (geometry.r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i))
        ∧ (∀ z ∈ Metric.ball
              ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (geometry.r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = Ambient.freeEnergyComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ
                (p.J : ℂ)
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i)
          ∩ Metric.ball
            ((geometry.center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r j))) :
    ∃ compactCover :
        Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
          (IsingModel.latticeGraph d) Λ p K geometry.n geometry.center geometry.r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_compactLocalCoverFinGeometry_cOpenPatch
    (IsingModel.latticeGraph d) Λ p hBED hd K geometry hA hFc_mem hFres hbranch
    hoverlap

/-- **ℤ^d structured eventual-overlap data to compact-open compact-target
patch**: structured real eventual-overlap data first yields a compact
local-cover `Fin n` geometry over `K`; for that geometry, compact-open
compactness of the selected restrictions of the data's branch family, together
with centre normalisation at every selected finite-cover centre, produces a
compact finite real-centred Lee-Yang cover package and a patch differentiable
on `K`. -/
theorem freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_cOpenPatch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangRealEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    ∃ geometry :
        Ambient.LeeYangCompactLocalCoverFinGeometry
          (IsingModel.latticeGraph d) Λ p K,
      ∀ {A : ∀ i : Fin geometry.n,
          Set C(Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i), ℂ)}
        {Fc : ∀ i : Fin geometry.n, ℕ →
          C(Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i), ℂ)},
        (∀ i, IsCompact (A i)) →
        (∀ i m, Fc i m ∈ A i) →
        (∀ i m z
          (hz : z ∈ Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i)),
          data.branchData.branchFamily (geometry.center i) m z =
            Fc i m ⟨z, hz⟩) →
        (∀ i m,
          data.branchData.branchFamily (geometry.center i) m
              ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = Ambient.freeEnergyComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ
                (p.J : ℂ)
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m) →
        ∃ compactCover :
            Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
              (IsingModel.latticeGraph d) Λ p K geometry.n geometry.center geometry.r,
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                  (geometry.r i))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_cOpenPatch
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised eventual-overlap data to compact-open
compact-target patch**: pointwise normalisation supplies the selected-centre
normalisation needed by the structured compact-open patch bridge, leaving only
compact-open compactness and continuous representatives as explicit
compact-open inputs. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_cOpenPatch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    ∃ geometry :
        Ambient.LeeYangCompactLocalCoverFinGeometry
          (IsingModel.latticeGraph d) Λ p K,
      ∀ {A : ∀ i : Fin geometry.n,
          Set C(Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i), ℂ)}
        {Fc : ∀ i : Fin geometry.n, ℕ →
          C(Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i), ℂ)},
        (∀ i, IsCompact (A i)) →
        (∀ i m, Fc i m ∈ A i) →
        (∀ i m z
          (hz : z ∈ Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i)),
          data.pointwiseData.branchData.branchFamily (geometry.center i) m z =
            Fc i m ⟨z, hz⟩) →
        ∃ compactCover :
            Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
              (IsingModel.latticeGraph d) Λ p K geometry.n geometry.center geometry.r,
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                  (geometry.r i))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_cOpenPatch
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d finite-ball compact-open diagonal extraction with local patching**:
if the selected stage branches are eventually equal on every pairwise overlap,
the extracted holomorphic local limits patch to one differentiable function on
the finite union of balls. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_fin_ball_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β m)
        ∧ F i m (h0 i) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J (h0 i) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : Fin n → ℂ → ℂ, ∃ g : ℂ → ℂ,
        (∀ i,
          (∃ fc : C(Metric.ball (h0 i) (r i), ℂ),
            fc ∈ A i ∧
              ∀ z (hz : z ∈ Metric.ball (h0 i) (r i)), f i z = fc ⟨z, hz⟩) ∧
          TendstoLocallyUniformlyOn
            (fun m z => F i (σ m) z) (f i) Filter.atTop
              (Metric.ball (h0 i) (r i)) ∧
          DifferentiableOn ℂ (f i) (Metric.ball (h0 i) (r i))) ∧
        (∀ i, Set.EqOn g (f i) (Metric.ball (h0 i) (r i))) ∧
        DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) ∧
        ∀ i j, Set.EqOn (f i) (f j)
          (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j)) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_patch
    (IsingModel.latticeGraph d) Λ J β n hA hFc_mem hFres hbranch hoverlap

end Ambient

end IsingModel
