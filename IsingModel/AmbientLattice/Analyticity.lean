import IsingModel.AmbientLattice.Defs
import IsingModel.ClusterExpansion
import IsingModel.AmbientLattice.AnalyticityLambdaJoint
import IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep
import IsingModel.AmbientLattice.AnalyticityLambdaPerDirection
import IsingModel.AmbientLattice.AnalyticityLambdaPolymer
import IsingModel.AmbientLattice.AnalyticityLambdaSandwich
import IsingModel.AmbientLattice.AnalyticityLambdaRegularity
import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds
import IsingModel.AmbientLattice.AnalyticityLambdaMayer
import IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff
import IsingModel.AmbientLattice.AnalyticityLambdaTanhFerroIff
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# Joint analyticity for AmbientLattice finite-volume Λ-restricted Ising

Lifts the joint analyticity of `partitionFunction` and `freeEnergy` in
`(β, J, h) ∈ ℝ × ℝ × ℝ` (Glimm-Jaffe §18.6 capstone, established in
`IsingModel/ClusterExpansion.lean` via direct sum-of-exp analyticity)
to the finite-volume Λ-restricted versions defined in
`IsingModel/AmbientLattice/Defs.lean`. Each theorem is a thin wrapper
around the corresponding theorem on `inducedGraph G Λ`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-! ## Moved: Λ-level joint analyticity wrappers

The 10 Λ-level joint analyticity wrappers (partitionFunctionΛ +
freeEnergyΛ + correlationΛ AnalyticAt / AnalyticOnNhd / Continuous /
Differentiable joint) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaJoint`.
The legacy import path is preserved by re-importing the new child.
-/



/-! ## Moved: magnetizationΛ + susceptibilityΛ analyticity wrappers

The 14 magnetizationΛ + susceptibilityΛ + correlationΛ
continuousAt/differentiableAt/analyticAt/analyticOnNhd joint wrappers
now live in
`IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: Λ partitionFunction per-direction regularity wrappers

The 6 partitionFunctionΛ per-direction Continuous / Differentiable
wrappers at general h now live in
`IsingModel.AmbientLattice.AnalyticityLambdaPerDirection`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## §18.4-§18.5 polymerFreeEnergy / vdSum / ε wrappers (now split)

The Λ-layer wrappers for the §18.4-§18.5 polymerFreeEnergy /
vdPolymerFamilies_sum / mayerPartialSum / mayerExpansionTerm /
ε(t) / log_vdPolymerFamilies_sum / Mayer identity / strict-mono /
iff family bundles originally lived inline below this header. They
have been refactored out into narrow child modules
(`AnalyticityLambdaPolymer`, `AnalyticityLambdaSandwich`,
`AnalyticityLambdaPolymerBounds`, `AnalyticityLambdaMayer`,
`AnalyticityLambdaVdPolymer`, `AnalyticityLambdaMayerIdentity`,
`AnalyticityLambdaBasicIdentities`,
`AnalyticityLambdaMayerPfeEdgeBounds`,
`AnalyticityLambdaMayerRecurrenceEpsilon`,
`AnalyticityLambdaEpsilonIff`, ...) re-imported at the top of this
file, so the legacy import path is preserved while the per-PR
narrow Moved doc blocks below list the exact destinations. -/

/-! ## Moved: polymerFreeEnergy_Λ basic wrappers

The 16 §18.4 polymerFreeEnergy_Λ / vdPolymerFamilies_sum_Λ / mayer*_Λ
basic wrappers now live in
`IsingModel.AmbientLattice.AnalyticityLambdaPolymer`.
The legacy import path is preserved by re-importing the new child.
-/



/-! ## Moved: polymerFreeEnergy_Λ sandwich + hasSum wrappers

The 10 §18.4 / §18.5 polymerFreeEnergy_Λ high_temp_sandwich, tanh
sandwich, hasSum_via_log, and vdPolymerFamilies_sum_Λ sandwich wrappers
(with ferromagnetic variants) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaSandwich`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: Λ regularity wrappers

The 10 Λ-layer freeEnergyΛ correction + polymerFreeEnergy_Λ
continuous/differentiable + tanh analyticAt/analyticOnNhd wrappers
now live in
`IsingModel.AmbientLattice.AnalyticityLambdaRegularity`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: polymerFreeEnergy_Λ bounds wrappers

The 12 Λ-layer polymerFreeEnergy_Λ nonneg / bounds / monotone / eq_zero
/ tanh sandwich / tanh double bound wrappers now live in
`IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: mayer wrappers

The 23 §18.6 mayerPartialSum_Λ + mayerExpansionTerm_Λ
continuous/differentiable/analyticAt/analyticOnNhd wrappers (raw and
tanh-composed variants) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaMayer`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: vdPolymerFamilies_sum + log_vdPolymerFamilies_sum wrappers

The 14 §18.5-18.6 vdPolymerFamilies_sum_Λ + log_vdPolymerFamilies_sum_Λ
continuous / differentiable / analyticAt / hasDerivAt wrappers
(raw and tanh-composed variants) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: §18.5 Mayer identity edge-case wrappers

The 19 §18.5 Λ-layer Mayer identity / polymerFreeEnergy =
mayerPartialSum edge-case wrappers (parameter slices `t = 0`, `β·J =
0`, `β = 0`, `J = 0`; polymer_free_energy form; mayerPartialSum 0 ≤
polymerFreeEnergy bounds; no-polymer / trivial / edgeless induced
graphs) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity`. The
legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: §18.5 basic identities + bounds + iff wrappers

The 17 §18.5 Λ-layer wrappers covering `at_zero` / `at_one` basic
identities, tanh iff characterizations, the bound family
(`le_two_pow`, `le_one_plus_tanh_pow`, `one_le_vdPolymerFamilies_sum_Λ`),
and generic-`t` bounds + `_eq_one_add` decomposition now live in
`IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities`. The
legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: §18.5 Mayer expansion + polymerFreeEnergy bound wrappers

The 17 §18.5 Λ-layer wrappers covering Mayer expansion edge-cases
(`n = 2`, `_two_filter`, `mayerPartialSum at N = 2`,
`_eq_zero_of_no_polymers`, `_eq_zero_of_edgeFinset_empty`,
`mayerExpansionTerm_abs_le`), polymerFreeEnergy at_zero / at_one +
analyticAt + analyticOnNhd_Ici_zero + sandwich_of_nonneg, and
polymerFreeEnergy tanh-bound + ferromagnetic + hasDerivAt +
`_eq_log_one_add_eps` now live in
`IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds`. The
legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: §18.5 Mayer recurrence + ε infrastructure wrappers

The 12 §18.5 Λ-layer wrappers covering Mayer recurrence
(`mayerPartialSum_Λ_succ`,
`mayerExpansionTerm_Λ_eq_mayerPartialSum_diff`),
`polymerFreeEnergy_Λ_hasSum_via_log` / `_hasSum_via_log_eventually`,
`vdPolymerFamilies_sum_Λ_minus_one_tendsto_zero`, Mayer term sign at
`n = 1, 2` (`mayerExpansionTerm_Λ_one_nonneg_of_nonneg`,
`_two_nonpos_of_nonneg`), `vdPolymerFamilies_sum_Λ_minus_one_{at_zero,
continuous, analyticAt, lt_one_eventually}`, and
`allPolymers_Λ_eq_empty_of_edgeFinset_empty` now live in
`IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: §18.5 ε(t) positivity-iff + strict-mono wrappers

The 16 §18.5 Λ-layer wrappers covering ε(t) / polymerFreeEnergy
positivity / zero iff family (`_minus_one_{pos_iff, eq_zero_iff,
tanh_pos_iff, tanh_eq_zero_iff}`, `polymerFreeEnergy_Λ_tanh_{pos_iff,
eq_zero_iff}`) and strict-mono / strict-pos under polymers ≠ ∅
(`_lt_of_lt`, `_strictMonoOn`, `_pos_of_t_pos`, `_gt_one_of_t_pos`,
`_minus_one_pos_of_t_pos`, `_tanh_pos_of_tanh_pos`,
`_tanh_gt_one_of_tanh_pos`, `_minus_one_tanh_pos_of_tanh_pos`,
`_strictMonoOn_Ioi_zero`, both for `polymerFreeEnergy_Λ` and
`vdPolymerFamilies_sum_Λ`) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff`. The legacy
import path is preserved by re-importing the new child.
-/


/-! ## Moved: §18.5 tanh ferromagnetic iff wrappers

The 9 §18.5 Λ-layer wrappers covering
`polymerFreeEnergy_Λ_tanh_{lt_eps_iff_eps_pos,
eq_zero_iff_eps_eq_zero, pos_iff_eps_pos, pos_iff, eq_zero_iff,
lt_pow_sub_one_of_eps_pos, lt_eps_of_eps_pos}_ferro` and
`vdPolymerFamilies_sum_Λ_tanh_{gt_one_iff, eq_one_iff}_ferro`
(under `0 ≤ β`, `0 ≤ J`) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaTanhFerroIff`. The
legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: §18.5 polymerFreeEnergy sharpening + vdSum sandwich wrappers

The 21 §18.5 Λ-layer wrappers covering polymerFreeEnergy tanh
sharpening (non-ferromagnetic) + β/J strict-mono, ε(t) nonneg +
non-tanh polymerFreeEnergy sharpening, and vdSum sandwich/monotone
+ ε bound + pFE(tanh) bound + `log 2` (covering Λ-direct
`polymerFreeEnergy_Λ_tanh_*` sharpening, β/J strict-mono under
`polymers_nonempty`, `vdPolymerFamilies_sum_Λ_minus_one` nonneg
and pow_at_zero, non-tanh `polymerFreeEnergy_Λ` sharpening,
`vdPolymerFamilies_sum_Λ` sandwich/monotone/`minus_one_le`, and
`polymerFreeEnergy_Λ_tanh_{le_eps, le_pow_sub_one, lt_log_two}`)
now live in
`IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening`. The
legacy import path is preserved by re-importing the new child.
-/


/-! ### §18.6 partitionFunctionΛ regularity at `h = 0` Λ-layer wraps -/

/-- **Λ-layer: partitionFunction Continuous in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_continuous_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Continuous (fun β : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_continuous_beta_h_zero
    (inducedGraph G Λ) J

/-- **Λ-layer: partitionFunction Continuous in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_continuous_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Continuous (fun J : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_continuous_J_h_zero
    (inducedGraph G Λ) β

/-- **Λ-layer: partitionFunction Differentiable in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_differentiable_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Differentiable ℝ
      (fun β : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_differentiable_beta_h_zero
    (inducedGraph G Λ) J

/-- **Λ-layer: partitionFunction Differentiable in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_differentiable_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Differentiable ℝ
      (fun J : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_differentiable_J_h_zero
    (inducedGraph G Λ) β

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_analyticAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticAt ℝ
      (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β'⟩) β := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_beta_h_zero
    (inducedGraph G Λ) J β

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_analyticAt_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) :
    AnalyticAt ℝ
      (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', 0, β⟩) J := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_J_h_zero
    (inducedGraph G Λ) β J

/-- **Λ-layer: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `β`
at `h = 0`**. -/
theorem partitionFunctionΛ_analyticOnNhd_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β'⟩) Set.univ := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticOnNhd_beta_h_zero
    (inducedGraph G Λ) J

/-- **Λ-layer: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `J`
at `h = 0`**. -/
theorem partitionFunctionΛ_analyticOnNhd_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', 0, β⟩) Set.univ := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticOnNhd_J_h_zero
    (inducedGraph G Λ) β

/-! ### §18.6 freeEnergyΛ per-direction analyticity Λ-layer wraps -/

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem freeEnergyΛ_analyticAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, 0, β'⟩) β :=
  IsingModel.freeEnergy_analyticAt_beta_h_zero (inducedGraph G Λ) J β

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem freeEnergyΛ_analyticAt_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', 0, β⟩) J :=
  IsingModel.freeEnergy_analyticAt_J_h_zero (inducedGraph G Λ) β J

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β`
at `h = 0`**. -/
theorem freeEnergyΛ_analyticOnNhd_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, 0, β'⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_beta_h_zero (inducedGraph G Λ) J

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J`
at `h = 0`**. -/
theorem freeEnergyΛ_analyticOnNhd_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', 0, β⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_J_h_zero (inducedGraph G Λ) β

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `β` at general `h`**. -/
theorem freeEnergyΛ_analyticAt_beta_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, h, β'⟩) β :=
  IsingModel.freeEnergy_analyticAt_beta_general_h
    (inducedGraph G Λ) J h β

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `J` at general `h`**. -/
theorem freeEnergyΛ_analyticAt_J_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', h, β⟩) J :=
  IsingModel.freeEnergy_analyticAt_J_general_h
    (inducedGraph G Λ) β h J

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `h`**. -/
theorem freeEnergyΛ_analyticAt_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ => freeEnergyΛ G Λ ⟨J, h', β⟩) h :=
  IsingModel.freeEnergy_analyticAt_h (inducedGraph G Λ) J β h

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
general `h`**. -/
theorem freeEnergyΛ_analyticOnNhd_beta_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, h, β'⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_beta_general_h
    (inducedGraph G Λ) J h

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
general `h`**. -/
theorem freeEnergyΛ_analyticOnNhd_J_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h : ℝ) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', h, β⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_J_general_h
    (inducedGraph G Λ) β h

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `h`**. -/
theorem freeEnergyΛ_analyticOnNhd_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticOnNhd ℝ
      (fun h' : ℝ => freeEnergyΛ G Λ ⟨J, h', β⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_h (inducedGraph G Λ) J β

/-! ### §18.6 partitionFunction joint + general-h analyticity
Λ-layer wraps -/

/-- **Λ-layer: partitionFunction jointly `Continuous` in
`(β, J, h)`**. -/
theorem partitionFunctionΛ_continuous_joint
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionΛ G Λ ⟨p.2.1, p.2.2, p.1⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_continuous_joint (inducedGraph G Λ)

/-- **Λ-layer: partitionFunction jointly `Differentiable ℝ` in
`(β, J, h)`**. -/
theorem partitionFunctionΛ_differentiable_joint
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionΛ G Λ ⟨p.2.1, p.2.2, p.1⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_differentiable_joint
    (inducedGraph G Λ)

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `β` at general
`h`**. -/
theorem partitionFunctionΛ_analyticAt_beta_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, h, β'⟩) β := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_beta_general_h
    (inducedGraph G Λ) J h β

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `J` at general
`h`**. -/
theorem partitionFunctionΛ_analyticAt_J_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', h, β⟩) J := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_J_general_h
    (inducedGraph G Λ) β h J

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `h`**. -/
theorem partitionFunctionΛ_analyticAt_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ => partitionFunctionΛ G Λ ⟨J, h', β⟩) h := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_h
    (inducedGraph G Λ) J β h

/-! ### §18.4-§18.6 capstones Λ-layer wraps -/

/-- **Λ-layer: §18.4 partitionFunction polymer-family form** capstone:
`Z_Λ(J, 0, β) = 2^|Λ| · cosh(β·J)^|E_Λ| · ∑_Γ ∏ tanh(β·J)^|P|`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_polymer_family
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    partitionFunctionΛ G Λ ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ↑(Λ : Finset V) *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card *
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_polymer_family
    (inducedGraph G Λ) J β

/-- **Λ-layer: §18.4 partitionFunction even-subgraph form** (FV (3.45))**:
`Z_Λ = 2^|Λ| · cosh(β·J)^|E_Λ| · ∑_X tanh(β·J)^|X|`. -/
theorem
partitionFunctionΛ_high_temp_expansion_h_zero_closed_evenSubgraphs
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    partitionFunctionΛ G Λ ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ↑(Λ : Finset V) *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card *
        ∑ X ∈ IsingModel.evenSubgraphs (inducedGraph G Λ),
          Real.tanh (β * J) ^ X.card := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_closed_evenSubgraphs
    (inducedGraph G Λ) J β

/-- **Λ-layer: §18.6 freeEnergy decomposition** under `0 ≤ β·J` and
`Λ.Nonempty`. -/
theorem freeEnergyΛ_eq_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : Λ.Nonempty) :
    freeEnergyΛ G Λ ⟨J, 0, β⟩ =
      Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ : Finset V) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ : Finset V) :=
  IsingModel.freeEnergy_eq_polymerFreeEnergy
    (inducedGraph G Λ) J β hβJ (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Λ-layer: §18.6 ferromagnetic freeEnergy decomposition** under
`0 ≤ J, 0 < β` and `Λ.Nonempty`. -/
theorem freeEnergyΛ_eq_polymerFreeEnergy_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : Λ.Nonempty) :
    freeEnergyΛ G Λ ⟨J, 0, β⟩ =
      Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ : Finset V) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ : Finset V) :=
  IsingModel.freeEnergy_eq_polymerFreeEnergy_ferromagnetic
    (inducedGraph G Λ) J β hJ hβ (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Λ-layer: freeEnergy = log 2** at `β·J = 0`, under
`Λ.Nonempty`. -/
theorem freeEnergyΛ_eq_log_two_at_betaJ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (hne : Λ.Nonempty) :
    freeEnergyΛ G Λ ⟨J, 0, β⟩ = Real.log 2 :=
  IsingModel.freeEnergy_eq_log_two_at_betaJ_zero
    (inducedGraph G Λ) hβJ (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Λ-layer: mayerPartialSum at N=1, t=1 = |allPolymers|**. -/
theorem mayerPartialSum_Λ_one_at_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 1 1 =
      (IsingModel.allPolymers (inducedGraph G Λ)).card :=
  IsingModel.mayerPartialSum_one_at_one (inducedGraph G Λ)

/-! ### §18.5 Mayer filter-connected + ε^n + mayerPartialSum
analyticOnNhd Λ-layer wraps -/

/-- **Λ-layer: mayerPartialSum `AnalyticOnNhd ℝ _ Set.univ`**. -/
theorem mayerPartialSum_Λ_analyticOnNhd
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    AnalyticOnNhd ℝ
      (fun s : ℝ => IsingModel.mayerPartialSum
          (inducedGraph G Λ) N s) Set.univ :=
  IsingModel.mayerPartialSum_analyticOnNhd (inducedGraph G Λ) N

/-- **Λ-layer: ε(t)^n as multi-Γ piFinset sum**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_pow
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ^ n =
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin n =>
                (IsingModel.vdCompatiblePolymerFamilies
                  (inducedGraph G Λ)).erase ∅),
        ∏ i : Fin n, ∏ P ∈ ω i, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pow
    (inducedGraph G Λ) t n

/-- **Λ-layer: mayerExpansionTerm filter-connected at n=0 = ∅**. -/
theorem mayerExpansionTerm_Λ_filter_connected_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    (Fintype.piFinset
        (fun _ : Fin 0 =>
          IsingModel.allPolymers (inducedGraph G Λ))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) = ∅ :=
  IsingModel.mayerExpansionTerm_filter_connected_zero
    (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm filter-connected at n=1 = full
piFinset**. -/
theorem mayerExpansionTerm_Λ_filter_connected_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers (inducedGraph G Λ))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers (inducedGraph G Λ)) :=
  IsingModel.mayerExpansionTerm_filter_connected_one (inducedGraph G Λ)

/-- **Λ-layer: filter-connected = filter-incompatible at n=2**. -/
theorem mayerExpansionTerm_Λ_two_filter_connected_eq_incompat
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (Fintype.piFinset
        (fun _ : Fin 2 =>
          IsingModel.allPolymers (inducedGraph G Λ))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      (Fintype.piFinset
          (fun _ : Fin 2 =>
            IsingModel.allPolymers (inducedGraph G Λ))).filter
          (fun ω => IsingModel.PolymersIncompatible (ω 0) (ω 1)) :=
  IsingModel.mayerExpansionTerm_two_filter_connected_eq_incompat
    (inducedGraph G Λ)

end Ambient
end IsingModel
