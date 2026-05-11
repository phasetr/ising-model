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

/-! ## §18.4 polymerFreeEnergy / vdSum / ε iff Λ-layer wrappers

Direct lifts of the iff / strict-mono / strict-pos GJ-命題-bundle from
`IsingModel/ClusterExpansion.lean` (PRs #1547-#1562) to the
finite-volume Λ-restricted setting via `inducedGraph G Λ`. -/

variable {V : Type*} [DecidableEq V]


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

/-! ### §18.6 vdPolymerFamilies_sum regularity in t Λ wraps -/

/-- **Λ-layer: `vdPolymerFamilies_sum` is `Continuous` in `t`** (§18.6). -/
theorem vdPolymerFamilies_sum_Λ_continuous
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Continuous (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_continuous (inducedGraph G Λ)

/-- **Λ-layer: `vdPolymerFamilies_sum` is `Differentiable ℝ` in `t`**. -/
theorem vdPolymerFamilies_sum_Λ_differentiable
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Differentiable ℝ (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_differentiable (inducedGraph G Λ)

/-- **Λ-layer: `vdPolymerFamilies_sum` is `AnalyticAt ℝ` in `t`**. -/
theorem vdPolymerFamilies_sum_Λ_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, s ^ P.card) t :=
  IsingModel.vdPolymerFamilies_sum_analyticAt (inducedGraph G Λ) t

/-- **Λ-layer: `vdPolymerFamilies_sum` `HasDerivAt` (explicit
polynomial derivative)**. -/
theorem vdPolymerFamilies_sum_Λ_hasDerivAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, s ^ P.card)
      (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
          ((Q.card : ℝ) * t ^ (Q.card - 1))) t :=
  IsingModel.vdPolymerFamilies_sum_hasDerivAt (inducedGraph G Λ) t

/-! ### §18.5 vdPolymerFamilies_sum tanh β/J Λ wraps -/

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Continuous (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_continuous_beta (inducedGraph G Λ) J

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Continuous (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_continuous_J (inducedGraph G Λ) β

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Differentiable ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_differentiable_beta
    (inducedGraph G Λ) J

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Differentiable ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_differentiable_J
    (inducedGraph G Λ) β

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) β :=
  IsingModel.vdPolymerFamilies_sum_tanh_analyticAt_beta
    (inducedGraph G Λ) J β

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) J :=
  IsingModel.vdPolymerFamilies_sum_tanh_analyticAt_J
    (inducedGraph G Λ) β J

/-! ### §18.5 log_vdPolymerFamilies_sum analyticity Λ wraps -/

/-- **Λ-layer: `log_vdPolymerFamilies_sum` AnalyticAt for `t ≥ 0`**. -/
theorem log_vdPolymerFamilies_sum_Λ_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ (fun s : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ), ∏ P ∈ Γ, s ^ P.card)) t :=
  IsingModel.log_vdPolymerFamilies_sum_analyticAt (inducedGraph G Λ) ht

/-- **Λ-layer: `log_vdPolymerFamilies_sum` AnalyticOnNhd over `[0, ∞)`**. -/
theorem log_vdPolymerFamilies_sum_Λ_analyticOnNhd_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    AnalyticOnNhd ℝ (fun s : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ), ∏ P ∈ Γ, s ^ P.card)) (Set.Ici 0) :=
  IsingModel.log_vdPolymerFamilies_sum_analyticOnNhd_Ici_zero
    (inducedGraph G Λ)

/-- **Λ-layer: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in β under
`0 ≤ β·J`**. -/
theorem log_vdPolymerFamilies_sum_Λ_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun β' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card)) β :=
  IsingModel.log_vdPolymerFamilies_sum_tanh_analyticAt_beta
    (inducedGraph G Λ) J β hβJ

/-- **Λ-layer: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in J under
`0 ≤ β·J`**. -/
theorem log_vdPolymerFamilies_sum_Λ_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun J' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card)) J :=
  IsingModel.log_vdPolymerFamilies_sum_tanh_analyticAt_J
    (inducedGraph G Λ) β J hβJ

/-! ### §18.5 mayer_identity_at edge-case Λ wraps -/

/-- **Λ-layer: Mayer identity at `t = 0`** (Step 600). -/
theorem mayer_identity_at_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ),
              ∏ P ∈ Γ, (0 : ℝ) ^ P.card) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N 0 :=
  IsingModel.mayer_identity_at_zero (inducedGraph G Λ) N

/-- **Λ-layer: Mayer identity at `β·J = 0`** (Step 609). -/
theorem mayer_identity_at_betaJ_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ),
              ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.mayer_identity_at_betaJ_zero (inducedGraph G Λ) hβJ N

/-- **Λ-layer: Mayer identity at `β = 0`** (Step 609 specialisation). -/
theorem mayer_identity_at_beta_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ),
              ∏ P ∈ Γ, Real.tanh ((0 : ℝ) * J) ^ P.card) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh ((0 : ℝ) * J)) :=
  IsingModel.mayer_identity_at_beta_zero (inducedGraph G Λ) J N

/-- **Λ-layer: Mayer identity at `J = 0`** (Step 609 specialisation). -/
theorem mayer_identity_at_J_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ),
              ∏ P ∈ Γ, Real.tanh (β * (0 : ℝ)) ^ P.card) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * (0 : ℝ))) :=
  IsingModel.mayer_identity_at_J_zero (inducedGraph G Λ) β N

/-! ### §18.5 polymerFreeEnergy_eq_mayerPartialSum_at edge-case Λ wraps -/

/-- **Λ-layer: polymerFreeEnergy = mayerPartialSum at t = 0**
(Step 611). -/
theorem polymerFreeEnergy_Λ_eq_mayerPartialSum_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) 0 =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N 0 :=
  IsingModel.polymerFreeEnergy_eq_mayerPartialSum_at_zero
    (inducedGraph G Λ) N

/-- **Λ-layer: polymerFreeEnergy = mayerPartialSum at β·J = 0**
(Step 617). -/
theorem polymerFreeEnergy_Λ_eq_mayerPartialSum_at_betaJ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero
    (inducedGraph G Λ) hβJ N

/-- **Λ-layer: polymerFreeEnergy = mayerPartialSum at β = 0**. -/
theorem polymerFreeEnergy_Λ_eq_mayerPartialSum_at_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh ((0 : ℝ) * J)) :=
  IsingModel.polymerFreeEnergy_eq_mayerPartialSum_at_beta_zero
    (inducedGraph G Λ) J N

/-- **Λ-layer: polymerFreeEnergy = mayerPartialSum at J = 0**. -/
theorem polymerFreeEnergy_Λ_eq_mayerPartialSum_at_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * (0 : ℝ))) :=
  IsingModel.polymerFreeEnergy_eq_mayerPartialSum_at_J_zero
    (inducedGraph G Λ) β N

/-! ### §18.5 mayer_identity polymer_free_energy variants Λ wraps -/

/-- **Λ-layer: Mayer identity at `J = 0` (polymer_free_energy form)**. -/
theorem mayer_identity_at_J_zero_polymer_free_energy_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * (0 : ℝ))) :=
  IsingModel.mayer_identity_at_J_zero_polymer_free_energy
    (inducedGraph G Λ) β N

/-- **Λ-layer: Mayer identity at `β = 0` (polymer_free_energy form)**. -/
theorem mayer_identity_at_beta_zero_polymer_free_energy_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh ((0 : ℝ) * J)) :=
  IsingModel.mayer_identity_at_beta_zero_polymer_free_energy
    (inducedGraph G Λ) J N

/-- **Λ-layer: Mayer identity at `J = β = 0` (polymer_free_energy form)**. -/
theorem mayer_identity_at_either_zero_polymer_free_energy_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) :=
  IsingModel.mayer_identity_at_either_zero_polymer_free_energy
    (inducedGraph G Λ) N

/-! ### §18.5 mayerPartialSum_zero ≤ polymerFreeEnergy Λ wraps -/

/-- **Λ-layer: mayerPartialSum 0 ≤ polymerFreeEnergy under `t ≥ 0`**. -/
theorem mayerPartialSum_zero_Λ_le_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0 t ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ) t :=
  IsingModel.mayerPartialSum_zero_le_polymerFreeEnergy
    (inducedGraph G Λ) ht

/-- **Λ-layer: mayerPartialSum 0 ≤ polymerFreeEnergy(tanh(β·J))**. -/
theorem mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) :=
  IsingModel.mayerPartialSum_zero_tanh_le_polymerFreeEnergy
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: ferromagnetic mayerPartialSum 0 ≤
polymerFreeEnergy(tanh(β·J))**. -/
theorem mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) :=
  IsingModel.mayerPartialSum_zero_tanh_le_polymerFreeEnergy_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-! ### §18.5 mayer_identity_of edge-case Λ wraps -/

/-- **Λ-layer: Mayer identity for empty-polymer graphs**. -/
theorem mayer_identity_of_no_polymers_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N t :=
  IsingModel.mayer_identity_of_no_polymers (inducedGraph G Λ) h_no t N

/-- **Λ-layer: Mayer identity for empty-polymer graphs (tanh form)**. -/
theorem mayer_identity_of_no_polymers_tanh_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.mayer_identity_of_no_polymers_tanh
    (inducedGraph G Λ) h_no β J N

/-- **Λ-layer: Mayer identity under disjunctive trivial conditions**. -/
theorem mayer_identity_of_trivial_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ}
    (h : β * J = 0 ∨
      IsingModel.allPolymers (inducedGraph G Λ) = ∅) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.mayer_identity_of_trivial (inducedGraph G Λ) h N

/-- **Λ-layer: Mayer identity for edgeless induced graphs**. -/
theorem mayer_identity_of_edgeFinset_empty_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N t :=
  IsingModel.mayer_identity_of_edgeFinset_empty
    (inducedGraph G Λ) h_empty t N

/-- **Λ-layer: Mayer identity for edgeless induced graphs (tanh form)**. -/
theorem mayer_identity_of_edgeFinset_empty_tanh_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.mayer_identity_of_edgeFinset_empty_tanh
    (inducedGraph G Λ) h_empty β J N

/-! ### §18.5 basic identities at_zero / at_one Λ wraps -/

/-- **Λ-layer: vdPolymerFamilies_sum at t = 0 = 1**. -/
theorem vdPolymerFamilies_sum_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 :=
  IsingModel.vdPolymerFamilies_sum_at_zero (inducedGraph G Λ)

/-- **Λ-layer: vdPolymerFamilies_sum at t = 1 = #vdCompatPoly families**. -/
theorem vdPolymerFamilies_sum_Λ_at_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).card :=
  IsingModel.vdPolymerFamilies_sum_at_one (inducedGraph G Λ)

/-- **Λ-layer: mayerPartialSum at N = 0 = 0**. -/
theorem mayerPartialSum_Λ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0 t = 0 :=
  IsingModel.mayerPartialSum_zero (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum at N = 1 = ∑_P t^|P|**. -/
theorem mayerPartialSum_Λ_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 1 t =
      ∑ P ∈ IsingModel.allPolymers (inducedGraph G Λ), t ^ P.card :=
  IsingModel.mayerPartialSum_one (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum at t = 0 = 0**. -/
theorem mayerPartialSum_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) N 0 = 0 :=
  IsingModel.mayerPartialSum_at_zero (inducedGraph G Λ) N

/-- **Λ-layer: mayerExpansionTerm at n = 0 = 0**. -/
theorem mayerExpansionTerm_Λ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 0 t = 0 :=
  IsingModel.mayerExpansionTerm_zero (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm at n = 1 = ∑_P t^|P|**. -/
theorem mayerExpansionTerm_Λ_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 1 t =
      ∑ P ∈ IsingModel.allPolymers (inducedGraph G Λ), t ^ P.card :=
  IsingModel.mayerExpansionTerm_one (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm at t = 0 = 0**. -/
theorem mayerExpansionTerm_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) n 0 = 0 :=
  IsingModel.mayerExpansionTerm_at_zero (inducedGraph G Λ) n

/-! ### §18.5 vdPolymerFamilies_sum tanh iff characterizations Λ wraps -/

/-- **Λ-layer: vdSum_tanh > 1 ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_gt_one_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_tanh_gt_one_iff
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: vdSum_tanh = 1 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_eq_one_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph G Λ),
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_tanh_eq_one_iff
    (inducedGraph G Λ) hβJ

/-! ### §18.5 vdPolymerFamilies_sum bound family Λ-layer wraps -/

/-- **Λ-layer: vdSum_tanh ≤ 2^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_le_two_pow
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_le_two_pow (inducedGraph G Λ) hβJ

/-- **Λ-layer: vdSum_tanh ≤ (1+tanh)^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_le_one_plus_tanh_pow
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_le_one_plus_tanh_pow
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: 1 ≤ vdSum_tanh** under `0 ≤ β·J`. -/
theorem one_le_vdPolymerFamilies_sum_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  IsingModel.one_le_vdPolymerFamilies_sum (inducedGraph G Λ) hβJ

/-! ### §18.5 vdPolymerFamilies_sum generic-t bounds Λ-layer -/

/-- **Λ-layer: 1 ≤ vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_ge_one_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_ge_one_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: vdSum ≤ (1+t)^|E|** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_le_one_plus_pow_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card)
      ≤ (1 + t) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: 0 < vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_pos_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_pos_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: vdSum = 1 + ε(t)** decomposition. -/
theorem vdPolymerFamilies_sum_Λ_eq_one_add
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) =
      1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_eq_one_add (inducedGraph G Λ) t

/-! ### §18.5 Mayer expansion edge-cases + n=2 + abs_le Λ-layer -/

/-- **Λ-layer: mayerExpansionTerm at `n = 2`**. -/
theorem mayerExpansionTerm_Λ_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 2 t =
      ∑ pq ∈ (IsingModel.allPolymers (inducedGraph G Λ)) ×ˢ
              (IsingModel.allPolymers (inducedGraph G Λ)),
        (if IsingModel.PolymersIncompatible pq.1 pq.2 then (-1/2 : ℝ)
          else 0) *
          (t ^ pq.1.card * t ^ pq.2.card) :=
  IsingModel.mayerExpansionTerm_two (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm at `n = 2`, filter form**. -/
theorem mayerExpansionTerm_Λ_two_filter
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 2 t =
      (-1/2 : ℝ) *
        ∑ pq ∈ ((IsingModel.allPolymers (inducedGraph G Λ)) ×ˢ
                (IsingModel.allPolymers (inducedGraph G Λ))).filter
            (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
          (t ^ pq.1.card * t ^ pq.2.card) :=
  IsingModel.mayerExpansionTerm_two_filter (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum at `N = 2`**. -/
theorem mayerPartialSum_Λ_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 2 t =
      (∑ P ∈ IsingModel.allPolymers (inducedGraph G Λ), t ^ P.card) +
        (-1/2 : ℝ) *
          ∑ pq ∈ ((IsingModel.allPolymers (inducedGraph G Λ)) ×ˢ
                  (IsingModel.allPolymers (inducedGraph G Λ))).filter
              (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card) :=
  IsingModel.mayerPartialSum_two (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum = 0 on no-polymer graphs**. -/
theorem mayerPartialSum_Λ_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) N t = 0 :=
  IsingModel.mayerPartialSum_eq_zero_of_no_polymers
    (inducedGraph G Λ) h_no t N

/-- **Λ-layer: mayerPartialSum = 0 on edgeless graphs**. -/
theorem mayerPartialSum_Λ_eq_zero_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) N t = 0 :=
  IsingModel.mayerPartialSum_eq_zero_of_edgeFinset_empty
    (inducedGraph G Λ) h_empty t N

/-- **Λ-layer: mayerExpansionTerm absolute bound**. -/
theorem mayerExpansionTerm_Λ_abs_le
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) (t : ℝ) :
    |IsingModel.mayerExpansionTerm (inducedGraph G Λ) n t| ≤
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin n => IsingModel.allPolymers (inducedGraph G Λ)),
        |IsingModel.ursellCoefficient ω| *
          |IsingModel.clusterSeqActivity t ω| :=
  IsingModel.mayerExpansionTerm_abs_le (inducedGraph G Λ) n t

/-! ### §18.5 polymerFreeEnergy at-zero/at-one + analytic + sandwich Λ -/

/-- **Λ-layer: polymerFreeEnergy at `t = 0`** = 0. -/
theorem polymerFreeEnergy_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) 0 = 0 :=
  IsingModel.polymerFreeEnergy_at_zero (inducedGraph G Λ)

/-- **Λ-layer: polymerFreeEnergy at `t = 1`** =
`log |vdCompatiblePolymerFamilies|`. -/
theorem polymerFreeEnergy_Λ_at_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) 1 =
      Real.log (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph G Λ)).card :=
  IsingModel.polymerFreeEnergy_at_one (inducedGraph G Λ)

/-- **Λ-layer: polymerFreeEnergy is `AnalyticAt ℝ` for `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph G Λ) s) t :=
  IsingModel.polymerFreeEnergy_analyticAt (inducedGraph G Λ) ht

/-- **Λ-layer: polymerFreeEnergy AnalyticOnNhd over `[0, ∞)`**. -/
theorem polymerFreeEnergy_Λ_analyticOnNhd_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    AnalyticOnNhd ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph G Λ) s) (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_analyticOnNhd_Ici_zero (inducedGraph G Λ)

/-- **Λ-layer: polymerFreeEnergy sandwich for `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_sandwich_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log (1 + t) :=
  IsingModel.polymerFreeEnergy_sandwich_of_nonneg (inducedGraph G Λ) ht

/-! ### §18.5 polymerFreeEnergy tanh-bound + ferro + hasDerivAt +
eq_log_one_add Λ-layer wraps -/

/-- **Λ-layer: polymerFreeEnergy tanh ≤ |E| · tanh** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_le_card_mul
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.tanh (β * J) :=
  IsingModel.polymerFreeEnergy_tanh_le_card_mul (inducedGraph G Λ) hβJ

/-- **Λ-layer: ferromagnetic polymerFreeEnergy_tanh_le_card_mul**. -/
theorem polymerFreeEnergy_Λ_tanh_le_card_mul_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.tanh (β * J) :=
  IsingModel.polymerFreeEnergy_tanh_le_card_mul_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-- **Λ-layer: ferromagnetic polymerFreeEnergy_tanh_sandwich**. -/
theorem polymerFreeEnergy_Λ_tanh_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  IsingModel.polymerFreeEnergy_tanh_sandwich_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-- **Λ-layer: ferromagnetic polymerFreeEnergy_tanh ≤ |E| · log 2**. -/
theorem polymerFreeEnergy_Λ_tanh_le_card_log_two_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_le_card_log_two_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-- **Λ-layer: polymerFreeEnergy = log(1 + ε(t))** decomposition. -/
theorem polymerFreeEnergy_Λ_eq_log_one_add_eps
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t =
      Real.log (1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.polymerFreeEnergy_eq_log_one_add_eps (inducedGraph G Λ) t

/-- **Λ-layer: polymerFreeEnergy hasDerivAt at `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_hasDerivAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G Λ) s)
      ((∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
            ((Q.card : ℝ) * t ^ (Q.card - 1))) /
        (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
            ∏ P ∈ Γ, t ^ P.card)) t :=
  IsingModel.polymerFreeEnergy_hasDerivAt (inducedGraph G Λ) ht

/-! ### §18.5 Mayer recurrence + hasSum + tendsto Λ-layer wraps -/

/-- **Λ-layer: mayerPartialSum recurrence** in `N`. -/
theorem mayerPartialSum_Λ_succ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) (N + 1) t =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N t +
        IsingModel.mayerExpansionTerm (inducedGraph G Λ) (N + 1) t :=
  IsingModel.mayerPartialSum_succ (inducedGraph G Λ) N t

/-- **Λ-layer: mayerExpansionTerm = mayerPartialSum diff**. -/
theorem mayerExpansionTerm_Λ_eq_mayerPartialSum_diff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) (N + 1) t =
      IsingModel.mayerPartialSum (inducedGraph G Λ) (N + 1) t -
        IsingModel.mayerPartialSum (inducedGraph G Λ) N t :=
  IsingModel.mayerExpansionTerm_eq_mayerPartialSum_diff
    (inducedGraph G Λ) N t

/-- **Λ-layer: polymerFreeEnergy hasSum via log under `|ε(t)| < 1`**. -/
theorem polymerFreeEnergy_Λ_hasSum_via_log
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ}
    (h_abs : |∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                        (inducedGraph G Λ)).erase ∅,
                ∏ P ∈ Γ, t ^ P.card| < 1) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                    (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G Λ) t) :=
  IsingModel.polymerFreeEnergy_hasSum_via_log (inducedGraph G Λ) h_abs

/-- **Λ-layer: polymerFreeEnergy hasSum eventually as `t → 0`**. -/
theorem polymerFreeEnergy_Λ_hasSum_via_log_eventually
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      HasSum (fun n : ℕ =>
          (-1 : ℝ) ^ n *
            (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                      (inducedGraph G Λ)).erase ∅,
                ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
            (n + 1))
        (IsingModel.polymerFreeEnergy (inducedGraph G Λ) t) :=
  IsingModel.polymerFreeEnergy_hasSum_via_log_eventually
    (inducedGraph G Λ)

/-- **Λ-layer: ε(t) → 0 as t → 0**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_tendsto_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Filter.Tendsto (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) (nhds 0) (nhds 0) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tendsto_zero
    (inducedGraph G Λ)

/-! ### §18.5 ε(t) infrastructure + Mayer term sign + allPolymers
empty Λ-layer wraps -/

/-- **Λ-layer: 0 ≤ mayerExpansionTerm at n = 1** under `0 ≤ t`. -/
theorem mayerExpansionTerm_Λ_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.mayerExpansionTerm (inducedGraph G Λ) 1 t :=
  IsingModel.mayerExpansionTerm_one_nonneg_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: mayerExpansionTerm at n = 2 ≤ 0** under `0 ≤ t`. -/
theorem mayerExpansionTerm_Λ_two_nonpos_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 2 t ≤ 0 :=
  IsingModel.mayerExpansionTerm_two_nonpos_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: ε(0) = 0**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 :=
  IsingModel.vdPolymerFamilies_sum_minus_one_at_zero (inducedGraph G Λ)

/-- **Λ-layer: ε(t) is `Continuous`**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_continuous
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_continuous
    (inducedGraph G Λ)

/-- **Λ-layer: ε(t) is `AnalyticAt ℝ` at every `t`**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, s ^ P.card) t :=
  IsingModel.vdPolymerFamilies_sum_minus_one_analyticAt
    (inducedGraph G Λ) t

/-- **Λ-layer: ε(t) < 1 eventually as t → 0**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_lt_one_eventually
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) < 1 :=
  IsingModel.vdPolymerFamilies_sum_minus_one_lt_one_eventually
    (inducedGraph G Λ)

/-- **Λ-layer: allPolymers = ∅ on edgeless induced graphs**. -/
theorem allPolymers_Λ_eq_empty_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅) :
    IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.allPolymers_eq_empty_of_edgeFinset_empty
    (inducedGraph G Λ) h_empty

/-! ### §18.5 ε(t) / polymerFreeEnergy positivity-iff Λ-layer wraps -/

/-- **Λ-layer: 0 < ε(t) ↔ 0 < t ∧ allPolymers ≠ ∅** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ↔
      0 < t ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pos_iff
    (inducedGraph G Λ) ht

/-- **Λ-layer: ε(t) = 0 ↔ t = 0 ∨ allPolymers = ∅** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 ↔
      t = 0 ∨ IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_minus_one_eq_zero_iff
    (inducedGraph G Λ) ht

/-- **Λ-layer: 0 < ε(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅** under
`0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tanh_pos_iff
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: ε(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_tanh_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tanh_eq_zero_iff
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: 0 < polymerFreeEnergy(tanh) ↔ 0 < tanh ∧
allPolymers ≠ ∅** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff (inducedGraph G Λ) hβJ

/-- **Λ-layer: polymerFreeEnergy(tanh) = 0 ↔ tanh = 0 ∨
allPolymers = ∅** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff
    (inducedGraph G Λ) hβJ

/-! ### §18.5 strict-mono / strict-pos under polymers ≠ ∅
Λ-layer wraps -/

/-- **Λ-layer: vdSum(s) < vdSum(t) for `0 ≤ s < t`** under polymers
exist. -/
theorem vdPolymerFamilies_sum_Λ_lt_of_lt_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, s ^ P.card) <
      ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_lt_of_lt_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hs hst

/-- **Λ-layer: vdSum is `StrictMonoOn (Set.Ici 0)`** under polymers
exist. -/
theorem vdPolymerFamilies_sum_Λ_strictMonoOn_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  IsingModel.vdPolymerFamilies_sum_strictMonoOn_of_polymers_nonempty
    (inducedGraph G Λ) h_poly

/-- **Λ-layer: 0 < pFE under `0 < t` and polymers exist**. -/
theorem polymerFreeEnergy_Λ_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ) t :=
  IsingModel.polymerFreeEnergy_pos_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: 1 < vdSum under `0 < t` and polymers exist**. -/
theorem vdPolymerFamilies_sum_Λ_gt_one_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
            ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_gt_one_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: 0 < ε(t) under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_minus_one_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pos_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: 0 < pFE(tanh) under `0 < tanh` and polymers exist**. -/
theorem polymerFreeEnergy_Λ_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) :=
  IsingModel.polymerFreeEnergy_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_tanh_pos h_poly

/-- **Λ-layer: 1 < vdSum(tanh) under `0 < tanh` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_tanh_pos h_poly

/-- **Λ-layer: 0 < ε(tanh) under `0 < tanh` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_tanh_pos h_poly

/-- **Λ-layer: pFE is `StrictMonoOn (Set.Ioi 0)`** under polymers
exist. -/
theorem polymerFreeEnergy_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn (fun t : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G Λ) t) (Set.Ioi 0) :=
  IsingModel.polymerFreeEnergy_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (inducedGraph G Λ) h_poly

/-- **Λ-layer: vdSum is `StrictMonoOn (Set.Ioi 0)`** under polymers
exist. -/
theorem
vdPolymerFamilies_sum_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ioi 0) :=
  IsingModel.vdPolymerFamilies_sum_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (inducedGraph G Λ) h_poly

/-! ### §18.5 polymerFreeEnergy/vdSum tanh ferromagnetic iff family
Λ-layer wraps (under `0 ≤ β, 0 ≤ J`) -/

/-- **Λ-layer: pFE(tanh) < ε(tanh) ↔ ε(tanh) > 0** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_iff_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: pFE(tanh) = 0 ↔ ε(tanh) = 0** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: 0 < pFE(tanh) ↔ 0 < ε(tanh)** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: 0 < pFE(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: pFE(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: 1 < vdSum(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅**
(ferro). -/
theorem vdPolymerFamilies_sum_Λ_tanh_gt_one_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_tanh_gt_one_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: vdSum(tanh) = 1 ↔ tanh = 0 ∨ allPolymers = ∅**
(ferro). -/
theorem vdPolymerFamilies_sum_Λ_tanh_eq_one_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_tanh_eq_one_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: pFE(tanh) < (1 + tanh)^|E| - 1** under ε(tanh) > 0
(ferro). -/
theorem polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ h_eps_pos

/-- **Λ-layer: pFE(tanh) < ε(tanh)** under ε(tanh) > 0 (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_of_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ h_eps_pos

/-! ### §18.5 polymerFreeEnergy tanh sharpening + β/J strict-mono
Λ-layer wraps -/

/-- **Λ-layer: pFE(tanh) < ε(tanh) ↔ 0 < ε(tanh)** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_iff_eps_pos
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: pFE(tanh) = 0 ↔ ε(tanh) = 0** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: 0 < pFE(tanh) ↔ 0 < ε(tanh)** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff_eps_pos
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: pFE(tanh) < ε(tanh)** under ε(tanh) > 0 (`0 ≤ β·J`). -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_of_eps_pos
    (inducedGraph G Λ) hβJ h_eps_pos

/-- **Λ-layer: pFE(tanh) < (1+tanh)^|E| - 1** under ε(tanh) > 0
(`0 ≤ β·J`). -/
theorem polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos
    (inducedGraph G Λ) hβJ h_eps_pos

/-- **Λ-layer: pFE(tanh(β₁·J)) < pFE(tanh(β₂·J))** under `J > 0`,
`0 ≤ β₁ < β₂`, polymers nonempty. -/
theorem polymerFreeEnergy_Λ_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {β₁ β₂ J : ℝ} (hβ₁ : 0 ≤ β₁) (hJ : 0 < J) (hβ : β₁ < β₂) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β₁ * J)) <
      IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β₂ * J)) :=
  IsingModel.polymerFreeEnergy_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hβ₁ hJ hβ

/-- **Λ-layer: pFE(tanh(β·J₁)) < pFE(tanh(β·J₂))** under `β > 0`,
`0 ≤ J₁ < J₂`, polymers nonempty. -/
theorem polymerFreeEnergy_Λ_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {β J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hβ : 0 < β) (hJ : J₁ < J₂) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J₁)) <
      IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J₂)) :=
  IsingModel.polymerFreeEnergy_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hJ₁ hβ hJ

/-- **Λ-layer: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in β**
under `J > 0` and polymers nonempty. -/
theorem
polymerFreeEnergy_Λ_tanh_strictMonoOn_beta_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {J : ℝ} (hJ : 0 < J) :
    StrictMonoOn (fun β : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G Λ) (Real.tanh (β * J))) (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_tanh_strictMonoOn_beta_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hJ

/-- **Λ-layer: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in J**
under `β > 0` and polymers nonempty. -/
theorem polymerFreeEnergy_Λ_tanh_strictMonoOn_J_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun J : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G Λ) (Real.tanh (β * J))) (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_tanh_strictMonoOn_J_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hβ

/-! ### §18.5 ε(t) nonneg + non-tanh polymerFreeEnergy sharpening
Λ-layer wraps -/

/-- **Λ-layer: 0 ≤ ε(t)** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: ε(0)^n = 0** for `n ≥ 1`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_pow_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ n = 0 :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pow_at_zero
    (inducedGraph G Λ) hn

/-- **Λ-layer: pFE(t) = 0 ↔ ε(t) = 0** under `0 ≤ t`. -/
theorem polymerFreeEnergy_Λ_eq_zero_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 :=
  IsingModel.polymerFreeEnergy_eq_zero_iff_eps_eq_zero
    (inducedGraph G Λ) ht

/-- **Λ-layer: 0 < pFE(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergy_Λ_pos_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.polymerFreeEnergy_pos_iff_eps_pos (inducedGraph G Λ) ht

/-- **Λ-layer: pFE(t) < ε(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergy_Λ_lt_eps_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.polymerFreeEnergy_lt_eps_iff_eps_pos
    (inducedGraph G Λ) ht

/-- **Λ-layer: pFE(t) < (1+t)^|E| - 1** under `0 ≤ t` and ε(t) > 0. -/
theorem polymerFreeEnergy_Λ_lt_pow_sub_one_of_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t <
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_lt_pow_sub_one_of_eps_pos
    (inducedGraph G Λ) ht h_eps_pos

/-! ### §18.5 vdSum sandwich/monotone + ε bound + pFE(tanh) bound +
log2 Λ-layer wraps -/

/-- **Λ-layer: vdSum sandwich for `t ≥ 0`**: `1 ≤ vdSum ≤
(1+t)^|E|`. -/
theorem vdPolymerFamilies_sum_Λ_sandwich_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: vdSum is `MonotoneOn (Set.Ici 0)`**. -/
theorem vdPolymerFamilies_sum_Λ_monotoneOn_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    MonotoneOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  IsingModel.vdPolymerFamilies_sum_monotoneOn_Ici_zero (inducedGraph G Λ)

/-- **Λ-layer: ε(t) ≤ (1+t)^|E| - 1** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_le_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.vdPolymerFamilies_sum_minus_one_le_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: pFE(tanh) ≤ ε(tanh) under `0 ≤ β·J`**. -/
theorem polymerFreeEnergy_Λ_tanh_le_eps_of_betaJ_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_le_eps_of_betaJ_nonneg
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: pFE(tanh) ≤ (1+tanh)^|E| - 1 under `0 ≤ β·J`**. -/
theorem polymerFreeEnergy_Λ_tanh_le_pow_sub_one_of_betaJ_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_tanh_le_pow_sub_one_of_betaJ_nonneg
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: pFE(tanh) < log 2** under `(1+tanh)^|E| < 2` and
`0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_lt_log_two_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) < Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_lt_log_two_of_pow_lt_two
    (inducedGraph G Λ) hβJ h_pow

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
