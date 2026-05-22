import IsingModel.AmbientLattice.Defs.Core
import IsingModel.Conditioning.CorrelationClosed

/-!
# Ambient lattice high-temperature partition bounds

High-temperature partition-function and free-energy wrappers at the ambient
finite-volume layer.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Λ-level partition-function closed form at `J = 0`**:
`Z_Λ(⟨0, h, β⟩) = (2 · cosh(β·h))^|Λ|`. Direct lift of
`IsingModel.partitionFunction_J_zero` through
`partitionFunctionΛ = partitionFunction (inducedGraph G Λ)`; the
`Fintype.card (↑Λ : Type _)` of the induced vertex type coincides with
`Λ.card` by `Fintype.card_coe`. -/
theorem partitionFunctionΛ_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) :
    partitionFunctionΛ G Λ (⟨0, h, β⟩ : IsingParams ℝ)
      = (2 * Real.cosh (β * h)) ^ Λ.card := by
  change IsingModel.partitionFunction (inducedGraph G Λ)
      (⟨0, h, β⟩ : IsingParams ℝ) = _
  rw [IsingModel.partitionFunction_J_zero, Fintype.card_coe]

/-- **Λ-level partition-function closed form at `β = 0`**:
`Z_Λ(⟨J, h, 0⟩) = 2^|Λ|`. Direct lift of
`IsingModel.partitionFunction_beta_zero` and
`IsingModel.card_config_eq_two_pow`; the Boltzmann prefactor `-β`
kills the Hamiltonian entirely, leaving a counting measure. -/
theorem partitionFunctionΛ_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    partitionFunctionΛ G Λ (⟨J, h, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card := by
  change IsingModel.partitionFunction (inducedGraph G Λ)
      (⟨J, h, 0⟩ : IsingParams ℝ) = _
  rw [IsingModel.partitionFunction_beta_zero,
      IsingModel.card_config_eq_two_pow]
  push_cast
  rw [Fintype.card_coe]

/-- **Λ-level partition-function closed form at `J = 0, h = 0`**:
`Z_Λ(⟨0, 0, β⟩) = 2^|Λ|`. Direct lift of
`IsingModel.partitionFunction_zero_params` and
`IsingModel.card_config_eq_two_pow`. -/
theorem partitionFunctionΛ_zero_params
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card := by
  change IsingModel.partitionFunction (inducedGraph G Λ)
      (⟨0, 0, β⟩ : IsingParams ℝ) = _
  rw [IsingModel.partitionFunction_zero_params,
      IsingModel.card_config_eq_two_pow]
  push_cast
  rw [Fintype.card_coe]

/-- **Λ-level partition function high-temperature expansion at `h = 0`**:
`Z_Λ(⟨J, 0, β⟩) = (cosh βJ)^|E_Λ| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j)`.
Direct lift of `IsingModel.partitionFunction_high_temp_expansion_h_zero`
(Step 282). -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) =
      Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card *
      ∑ σ : Config ↑Λ,
        ∏ e ∈ (inducedGraph G Λ).edgeFinset,
          (1 + Real.tanh (β * J) * edgeSpin σ e) := by
  rw [partitionFunctionΛ_apply,
      IsingModel.partitionFunction_high_temp_expansion_h_zero]

/-- **Λ-level FV (3.45) at `J = 0` consistency check**:
`Z_Λ(⟨0, 0, β⟩) = 2^|Λ|`. Direct lift of Step 310. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card := by
  rw [partitionFunctionΛ_apply,
      IsingModel.partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero,
      Fintype.card_coe]

/-- **Λ-level FV (3.45) at `β = 0` consistency check**:
`Z_Λ(⟨J, 0, 0⟩) = 2^|Λ|`. Direct lift of Step 324. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card := by
  rw [partitionFunctionΛ_apply,
      IsingModel.partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero,
      Fintype.card_coe]

/-- **Λ-level FV (3.46) at `A = ∅` consistency check**:
under `0 ≤ β·J`, `correlationΛ G Λ ⟨J, 0, β⟩ ∅ = 1`.
Direct lift of Step 313. -/
theorem correlationΛ_high_temp_h_zero_at_empty_A
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) (∅ : Finset ↑Λ) = 1 := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_at_empty_A
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level partition function high-temperature expansion (general h)**:
for any parameter `p = (J, h, β)`,
`Z_Λ(p) = (cosh βJ)^|E_Λ| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j) · exp(βh ∑_i σ_i)`.
Direct lift of `IsingModel.partitionFunction_high_temp_expansion`
(Step 281). -/
theorem partitionFunctionΛ_high_temp_expansion
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) :
    partitionFunctionΛ G Λ p =
      Real.cosh (p.β * p.J) ^ (inducedGraph G Λ).edgeFinset.card *
      ∑ σ : Config ↑Λ,
        (∏ e ∈ (inducedGraph G Λ).edgeFinset,
          (1 + Real.tanh (p.β * p.J) * edgeSpin σ e)) *
        Real.exp (p.β * p.h * ∑ i : ↑Λ, Spin.sign ℝ (σ i)) := by
  rw [partitionFunctionΛ_apply,
      IsingModel.partitionFunction_high_temp_expansion]

/-- **Λ-level high-temperature partition function closed form (FV §3.7.3 eq. (3.45))**:
on the induced subgraph `inducedGraph G Λ` at zero external field,
`Z_Λ(⟨J, 0, β⟩) = 2^|Λ| · (cosh(β J))^|E_Λ| · ∑_{X ⊆ E_Λ, even-degree} tanh(β J)^|X|`.
Direct lift of `IsingModel.partitionFunction_high_temp_expansion_h_zero_closed`
through `partitionFunctionΛ = partitionFunction (inducedGraph G Λ)`,
using `Fintype.card_coe` to rewrite `Fintype.card ↑Λ = Λ.card`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_closed
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card *
        ∑ X ∈ (inducedGraph G Λ).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card := by
  rw [partitionFunctionΛ_apply,
      IsingModel.partitionFunction_high_temp_expansion_h_zero_closed,
      Fintype.card_coe]

/-- **Λ-level general-h subset expansion (GJ §18.3)**: for any
parameter `p = (J, h, β)`,
`Z_Λ(p) = (cosh βJ)^|E_Λ| · ∑_{X ⊆ E_Λ} tanh(βJ)^|X| · ∑_σ (∏_{e ∈ X} σ_iσ_j) exp(βh ∑ σ_i)`.
Direct lift of `IsingModel.partitionFunction_high_temp_expansion_subset_form`
(Step 300). -/
theorem partitionFunctionΛ_high_temp_expansion_subset_form
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) :
    partitionFunctionΛ G Λ p =
      Real.cosh (p.β * p.J) ^ (inducedGraph G Λ).edgeFinset.card *
      ∑ X ∈ (inducedGraph G Λ).edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ↑Λ,
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h * ∑ i : ↑Λ, Spin.sign ℝ (σ i)) := by
  rw [partitionFunctionΛ_apply,
      IsingModel.partitionFunction_high_temp_expansion_subset_form]

/-- **Λ-level high-temperature correlation closed form (FV §3.7.3 eq. (3.46))**:
on the induced subgraph `inducedGraph G Λ` at zero external field,
`⟨σ_A⟩^Λ_{β,0} = (∑_{X : ∂X=A} tanh^|X|) / (∑_{X : ∂X=∅} tanh^|X|)`.
Direct lift of `IsingModel.correlation_high_temp_expansion_h_zero_closed`
through `correlationΛ = correlation (inducedGraph G Λ)`. -/
theorem correlationΛ_high_temp_expansion_h_zero_closed
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A
      = (∑ X ∈ (inducedGraph G Λ).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑Λ,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) /
        (∑ X ∈ (inducedGraph G Λ).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_expansion_h_zero_closed
    (inducedGraph G Λ) J β A

/-- **Λ-level high-temperature partition function lower bound (GJ §18.3 / FV (3.45))**:
under `0 ≤ β * J`, `Z_Λ(⟨J, 0, β⟩) ≥ 2^|Λ| · (cosh(βJ))^|E_Λ|`.
Direct lift of `IsingModel.partitionFunction_high_temp_expansion_h_zero_lower_bound`
(Step 286) through `partitionFunctionΛ_apply` and `Fintype.card_coe`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  rw [partitionFunctionΛ_apply, ← Fintype.card_coe]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_lower_bound
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level log Z high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J`,
`log Z_Λ(⟨J, 0, β⟩) = |Λ| · log 2 + |E_Λ| · log(cosh βJ) + log(∑_{X even} tanh^|X|)`.
Direct lift of `IsingModel.log_partitionFunction_high_temp_expansion_h_zero_closed`
(Step 315) via `partitionFunctionΛ_apply` + `Fintype.card_coe`. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_closed
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2
        + ((inducedGraph G Λ).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ (inducedGraph G Λ).edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ↑Λ) =>
                  ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) := by
  rw [partitionFunctionΛ_apply,
      IsingModel.log_partitionFunction_high_temp_expansion_h_zero_closed
        (inducedGraph G Λ) J β hβJ,
      Fintype.card_coe]

/-- **Λ-level sharper log Z high-temperature upper bound**: under
`0 ≤ β·J`, `log Z_Λ ≤ |Λ| · log 2 + β·J·|E_Λ|`. Λ-layer wrapper of
`log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp` (Step 403). -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ (Λ.card : ℝ) * Real.log 2
        + β * J * (inducedGraph G Λ).edgeFinset.card := by
  rw [partitionFunctionΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level sharper log Z high-temperature sandwich**: under `0 ≤ β·J`,
`|Λ|·log 2 + |E_Λ|·log cosh(βJ) ≤ log Z_Λ ≤ |Λ|·log 2 + β·J·|E_Λ|`.
Λ-layer wrapper of
`log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp` (Step 403). -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (Λ.card : ℝ) * Real.log 2
        + ((inducedGraph G Λ).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ (Λ.card : ℝ) * Real.log 2
        + β * J * (inducedGraph G Λ).edgeFinset.card := by
  rw [partitionFunctionΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level freeEnergy high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 < |Λ|` and `0 ≤ β·J`,
`f_Λ = log 2 + (|E_Λ|/|Λ|) · log(cosh βJ) + log(∑_{X even} tanh^|X|) / |Λ|`.
Direct lift of `IsingModel.freeEnergy_high_temp_expansion_h_zero_closed`
(Step 317) via `freeEnergyΛ_apply` and `Fintype.card_coe`. -/
theorem freeEnergyΛ_high_temp_expansion_h_zero_closed
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      = Real.log 2
        + ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
            Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ (inducedGraph G Λ).edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ↑Λ) =>
                  ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) / Λ.card := by
  rw [freeEnergyΛ_apply]
  have hcoe : (Λ.card : ℝ) = (Fintype.card ↑Λ : ℝ) := by rw [Fintype.card_coe]
  rw [hcoe]
  exact IsingModel.freeEnergy_high_temp_expansion_h_zero_closed
    (inducedGraph G Λ) J β hβJ
    (by rw [Fintype.card_coe]; exact hne)

/-- **Λ-level Z high-temperature upper bound (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J`,
`Z_Λ(⟨J, 0, β⟩) ≤ 2^(|Λ|+|E_Λ|) · (cosh(βJ))^|E_Λ|`. ℤ^d wrapper of Step 320. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ (Λ.card + (inducedGraph G Λ).edgeFinset.card) *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card := by
  rw [partitionFunctionΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_upper_bound
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level sharper Z high-temperature upper bound**: under `0 ≤ β·J`,
`Z_Λ(⟨J, 0, β⟩) ≤ 2^|Λ| · exp(β·J·|E_Λ|)`. Λ-layer wrapper of
`partitionFunction_high_temp_expansion_h_zero_upper_bound_exp` (Step 393). -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) := by
  rw [partitionFunctionΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level sharper freeEnergy high-temperature upper bound**: under
`0 < |Λ|` and `0 ≤ β·J`,
`f_Λ(⟨J, 0, β⟩) ≤ log 2 + β·J·|E_Λ|/|Λ|`. Λ-layer wrapper of
`freeEnergy_high_temp_h_zero_upper_bound_exp` (Step 394). -/
theorem freeEnergyΛ_high_temp_h_zero_upper_bound_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.freeEnergy_high_temp_h_zero_upper_bound_exp
    (inducedGraph G Λ) J β hβJ hcard

/-- **Λ-level ferromagnetic Z sharper upper bound**: under `0 ≤ J, 0 < β`,
`Z_Λ ≤ 2^|Λ| · exp(β·J·|E_Λ|)`. Λ-layer ferromagnetic wrapper. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level ferromagnetic log Z sharper upper bound**: under `0 ≤ J, 0 < β`,
`log Z_Λ ≤ |Λ|·log 2 + β·J·|E_Λ|`. Λ-layer ferromagnetic wrapper. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ (Λ.card : ℝ) * Real.log 2
        + β * J * (inducedGraph G Λ).edgeFinset.card :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level ferromagnetic f sharper upper bound**: under `0 < |Λ|`,
`0 ≤ J, 0 < β`, `f_Λ ≤ log 2 + β·J·|E_Λ|/|Λ|`. -/
theorem freeEnergyΛ_high_temp_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_upper_bound_exp
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level sharper Z high-temperature sandwich**: under `0 ≤ β·J`,
`2^|Λ|·cosh^|E_Λ| ≤ Z_Λ ≤ 2^|Λ|·exp(β·J·|E_Λ|)`. Λ-layer wrapper of
`partitionFunction_high_temp_expansion_h_zero_sandwich_exp`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound G Λ J β hβJ,
   partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp G Λ J β hβJ⟩

/-- **Λ-level freeEnergy high-temperature upper bound (FV (3.45))**:
under `0 < |Λ|` and `0 ≤ β·J`,
`f_Λ(⟨J, 0, β⟩) ≤ log 2 + (|E_Λ|/|Λ|) · log(2 · cosh(βJ))`.
Direct lift of Step 322. -/
theorem freeEnergyΛ_high_temp_h_zero_upper_bound
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2
        + ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
            Real.log (2 * Real.cosh (β * J)) := by
  rw [freeEnergyΛ_apply]
  have hcoe : (Λ.card : ℝ) = (Fintype.card ↑Λ : ℝ) := by rw [Fintype.card_coe]
  rw [hcoe]
  exact IsingModel.freeEnergy_high_temp_h_zero_upper_bound
    (inducedGraph G Λ) J β hβJ
    (by rw [Fintype.card_coe]; exact hne)

omit [DecidableEq V] in
/-- **Λ-level Z bounds consistency**: lower ≤ upper. -/
theorem partitionFunctionΛ_high_temp_h_zero_lower_le_upper
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ (2 : ℝ) ^ (Λ.card + (inducedGraph G Λ).edgeFinset.card) *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card := by
  have := IsingModel.partitionFunction_high_temp_h_zero_lower_le_upper
    (inducedGraph G Λ) J β
  rwa [Fintype.card_coe] at this

omit [DecidableEq V] in
/-- **Λ-level freeEnergy bounds consistency**: lower ≤ upper. -/
theorem freeEnergyΛ_high_temp_h_zero_lower_le_upper
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ Real.log 2
        + ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
            Real.log (2 * Real.cosh (β * J)) := by
  have := IsingModel.freeEnergy_high_temp_h_zero_lower_le_upper
    (inducedGraph G Λ) J β hβJ
  rwa [Fintype.card_coe] at this

/-- **Λ-level free-energy lower bound from FV (3.45)** at zero external field:
under `0 < |Λ|` and `0 ≤ β * J`,
`f_Λ(⟨J, 0, β⟩) ≥ log 2 + (|E_Λ|/|Λ|) · log(cosh(β·J))`.
Direct lift of `IsingModel.freeEnergy_high_temp_h_zero_lower_bound`
(Step 288) through `freeEnergyΛ_apply` and `Fintype.card_coe`. -/
theorem freeEnergyΛ_high_temp_h_zero_lower_bound
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  rw [freeEnergyΛ_apply]
  have hcoe : (Λ.card : ℝ) = (Fintype.card ↑Λ : ℝ) := by
    rw [Fintype.card_coe]
  rw [hcoe]
  exact IsingModel.freeEnergy_high_temp_h_zero_lower_bound
    (inducedGraph G Λ) J β hβJ
    (by rw [Fintype.card_coe]; exact hne)

/-- **Λ-level sharper f high-temperature sandwich**: under `0 < |Λ|`,
`0 ≤ β·J`, `log 2 + (|E_Λ|/|Λ|)·log cosh(β·J) ≤ f_Λ ≤ log 2 + β·J·|E_Λ|/|Λ|`.
Λ-layer wrapper of `freeEnergy_high_temp_h_zero_sandwich_exp`. -/
theorem freeEnergyΛ_high_temp_h_zero_sandwich_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  ⟨freeEnergyΛ_high_temp_h_zero_lower_bound G Λ J β hβJ hne,
   freeEnergyΛ_high_temp_h_zero_upper_bound_exp G Λ J β hβJ hne⟩

/-- **Λ-level ferromagnetic Z sharper sandwich**: under `0 ≤ J, 0 < β`,
`2^|Λ|·cosh^|E_Λ| ≤ Z_Λ ≤ 2^|Λ|·exp(β·J·|E_Λ|)`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level ferromagnetic f sharper sandwich**: under `0 < |Λ|`,
`0 ≤ J, 0 < β`,
`log 2 + (|E_Λ|/|Λ|)·log cosh(β·J) ≤ f_Λ ≤ log 2 + β·J·|E_Λ|/|Λ|`. -/
theorem freeEnergyΛ_high_temp_h_zero_sandwich_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_sandwich_exp G Λ J β
    (mul_nonneg hβ.le hJ) hne

/-- **Λ-level sharper f complete-summary exp bundle**: under `0 < |Λ|`,
`0 ≤ β·J`, single statement bundling sharper sandwich + trivial-slice
values at the Λ-layer. -/
theorem freeEnergyΛ_high_temp_h_zero_complete_summary_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card ∧
    freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
    freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  obtain ⟨h1, h2⟩ := freeEnergyΛ_high_temp_h_zero_sandwich_exp
    G Λ J β hβJ hne
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [freeEnergyΛ_apply]
    have := IsingModel.freeEnergy_J_zero (inducedGraph G Λ) (0 : ℝ) β hcard
    simpa [mul_zero, Real.cosh_zero] using this
  · rw [freeEnergyΛ_apply]
    exact IsingModel.freeEnergy_beta_zero (inducedGraph G Λ) J 0 hcard

/-- **Λ-level sharper Z complete-summary exp bundle**: under `0 ≤ β·J`,
single statement bundling sharper sandwich + trivial-slice values. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card := by
  obtain ⟨h1, h2⟩ := partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    G Λ J β hβJ
  exact ⟨h1, h2,
    partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero G Λ β,
    partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero G Λ J⟩

/-- **Λ-level sharper log Z complete-summary exp bundle**: under
`0 ≤ β·J`, single statement bundling sharper sandwich + trivial-slice
values. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (Λ.card : ℝ) * Real.log 2
        + ((inducedGraph G Λ).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ (Λ.card : ℝ) * Real.log 2
        + β * J * (inducedGraph G Λ).edgeFinset.card ∧
    Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 := by
  obtain ⟨h1, h2⟩ := log_partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    G Λ J β hβJ
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero,
        Real.log_pow]
  · rw [partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero,
        Real.log_pow]

/-- **Λ-level ferromagnetic Z complete-summary exp bundle**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level ferromagnetic log Z complete-summary exp bundle**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (Λ.card : ℝ) * Real.log 2
        + ((inducedGraph G Λ).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ (Λ.card : ℝ) * Real.log 2
        + β * J * (inducedGraph G Λ).edgeFinset.card ∧
    Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level ferromagnetic f complete-summary exp bundle**. -/
theorem freeEnergyΛ_high_temp_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card ∧
    freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
    freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  freeEnergyΛ_high_temp_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level sharper f deviation bound**: under `0 < |Λ|`, `0 ≤ β·J`,
`f_Λ - log 2 ≤ β·J·|E_Λ|/|Λ|`. -/
theorem freeEnergyΛ_high_temp_h_zero_deviation_bound_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card := by
  have h := freeEnergyΛ_high_temp_h_zero_upper_bound_exp
    G Λ J β hβJ hne
  linarith

/-- **Λ-level ferromagnetic f deviation bound**: under `0 ≤ J, 0 < β`,
`f_Λ - log 2 ≤ β·J·|E_Λ|/|Λ|`. -/
theorem freeEnergyΛ_high_temp_h_zero_deviation_bound_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_deviation_bound_exp
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level f continuity at `J = 0`**: under `0 < |Λ|` and `0 ≤ β·J`,
`|f_Λ(⟨J,0,β⟩) - f_Λ(⟨0,0,β⟩)| ≤ β·J·|E_Λ|/|Λ|`. -/
theorem freeEnergyΛ_high_temp_h_zero_continuity_at_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    |freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)|
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply, freeEnergyΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.freeEnergy_high_temp_h_zero_continuity_at_J_zero
    (inducedGraph G Λ) J β hβJ hcard

/-- **Λ-level f continuity at `β = 0`**. -/
theorem freeEnergyΛ_high_temp_h_zero_continuity_at_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    |freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)|
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply, freeEnergyΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.freeEnergy_high_temp_h_zero_continuity_at_beta_zero
    (inducedGraph G Λ) J β hβJ hcard

/-- **Λ-level f continuity bundle at trivial slices**. -/
theorem freeEnergyΛ_high_temp_h_zero_continuity_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    |freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)|
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card ∧
    |freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)|
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  ⟨freeEnergyΛ_high_temp_h_zero_continuity_at_J_zero G Λ J β hβJ hne,
   freeEnergyΛ_high_temp_h_zero_continuity_at_beta_zero G Λ J β hβJ hne⟩

/-- **Λ-level ferromagnetic f continuity bundle**: under `0 ≤ J, 0 < β`
and `0 < |Λ|`. -/
theorem freeEnergyΛ_high_temp_h_zero_continuity_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    |freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)|
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card ∧
    |freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)|
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_continuity_bundle
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level f deviation sandwich**: under `0 < |Λ|` and `0 ≤ β·J`,
`0 ≤ f_Λ - log 2 ≤ β·J·|E_Λ|/|Λ|`. -/
theorem freeEnergyΛ_high_temp_h_zero_deviation_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    0 ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.freeEnergy_high_temp_h_zero_deviation_sandwich
    (inducedGraph G Λ) J β hβJ hcard

/-- **Λ-level ferromagnetic f deviation sandwich**. -/
theorem freeEnergyΛ_high_temp_h_zero_deviation_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    0 ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_deviation_sandwich
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level log Z deviation sandwich**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    0 ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card := by
  rw [partitionFunctionΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.log_partitionFunction_high_temp_expansion_h_zero_deviation_sandwich
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level ferromagnetic log Z deviation sandwich**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_sandwich
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level Z relative-deviation sandwich**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_relative_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        (2 : ℝ) ^ Λ.card
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) := by
  rw [partitionFunctionΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_relative_sandwich
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level ferromagnetic Z relative-deviation sandwich**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_relative_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        (2 : ℝ) ^ Λ.card
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_relative_sandwich
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level f strict deviation**: under `0 < β·J`, `0 < |Λ|`,
`0 < |E_Λ|`, `0 < f_Λ - log 2`. -/
theorem freeEnergyΛ_high_temp_h_zero_deviation_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (hne : 0 < Λ.card)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    0 < freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply]
  exact IsingModel.freeEnergy_high_temp_h_zero_deviation_pos
    (inducedGraph G Λ) J β hβJ hcard hEpos

/-- **Λ-level ferromagnetic f strict deviation**. -/
theorem freeEnergyΛ_high_temp_h_zero_deviation_pos_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (hne : 0 < Λ.card)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    0 < freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 :=
  freeEnergyΛ_high_temp_h_zero_deviation_pos
    G Λ J β (mul_pos hβ hJ) hne hEpos

/-- **Λ-level Z strict deviation**: under `0 < β·J`, `0 < |E_Λ|`,
`2^|Λ| < Z_Λ`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_pow_two_lt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    (2 : ℝ) ^ Λ.card
      < partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  rw [partitionFunctionΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_pow_two_lt
    (inducedGraph G Λ) J β hβJ hEpos

/-- **Λ-level log Z strict deviation**: under `0 < β·J`, `0 < |E_Λ|`,
`0 < log Z_Λ - |Λ|·log 2`. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    0 < Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2 := by
  rw [partitionFunctionΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.log_partitionFunction_high_temp_expansion_h_zero_deviation_pos
    (inducedGraph G Λ) J β hβJ hEpos

/-- **Λ-level Z + log Z + f strict deviation bundle**: under `0 < β·J`,
`0 < |E_Λ|`, `0 < |Λ|`, single statement bundling all three strict deviations. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_strict_deviation_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (hne : 0 < Λ.card)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    (2 : ℝ) ^ Λ.card < partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    0 < Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2 ∧
    0 < freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_pow_two_lt G Λ J β hβJ hEpos,
   log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_pos
     G Λ J β hβJ hEpos,
   freeEnergyΛ_high_temp_h_zero_deviation_pos G Λ J β hβJ hne hEpos⟩

/-- **Λ-level ferromagnetic Z + log Z + f strict deviation bundle**:
under `0 < J, 0 < β`, the same triple via `mul_pos hβ hJ`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_strict_deviation_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (hne : 0 < Λ.card)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    (2 : ℝ) ^ Λ.card < partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    0 < Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2 ∧
    0 < freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 :=
  partitionFunctionΛ_high_temp_expansion_h_zero_strict_deviation_bundle
    G Λ J β (mul_pos hβ hJ) hne hEpos

/-- **Λ-level ferromagnetic Z strict deviation**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    (2 : ℝ) ^ Λ.card
      < partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_pow_two_lt
    G Λ J β (mul_pos hβ hJ) hEpos

/-- **Λ-level ferromagnetic log Z strict deviation**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_pos_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    0 < Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_pos
    G Λ J β (mul_pos hβ hJ) hEpos

/-- **Λ-level Z ratio sandwich at J=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) := by
  rw [partitionFunctionΛ_apply, partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_ratio_sandwich
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level Z ratio sandwich at β=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) := by
  rw [partitionFunctionΛ_apply, partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level Z ratio sandwich bundle**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) ∧
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich G Λ J β hβJ,
   partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
     G Λ J β hβJ⟩

/-- **Λ-level ferromagnetic Z ratio sandwich bundle**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) ∧
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level Z ratio bound at J=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  (partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich G Λ J β hβJ).2

/-- **Λ-level Z ratio bound at β=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  (partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    G Λ J β hβJ).2

/-- **Λ-level ferromagnetic Z ratio upper bound at J=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level ferromagnetic Z ratio upper bound at β=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level Z ratio upper bound bundle**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound G Λ J β hβJ,
   partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
     G Λ J β hβJ⟩

/-- **Λ-level ferromagnetic Z ratio upper bound bundle**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level log Z ratio sandwich bundle**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) := by
  rw [partitionFunctionΛ_apply, partitionFunctionΛ_apply,
      partitionFunctionΛ_apply]
  exact IsingModel.log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level ferromagnetic log Z ratio sandwich bundle**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level log Z ratio bound at J=0**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card := by
  rw [partitionFunctionΛ_apply, partitionFunctionΛ_apply]
  exact IsingModel.log_partitionFunction_high_temp_expansion_h_zero_ratio_bound
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level log Z ratio bound at β=0**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card := by
  rw [partitionFunctionΛ_apply, partitionFunctionΛ_apply]
  exact IsingModel.log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level log Z ratio bound bundle**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card :=
  ⟨log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound G Λ J β hβJ,
   log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
     G Λ J β hβJ⟩

/-- **Λ-level ferromagnetic log Z ratio bound bundle**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level f ratio sandwich bundle**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply, freeEnergyΛ_apply, freeEnergyΛ_apply,
      ← Fintype.card_coe (s := Λ)]
  exact IsingModel.freeEnergy_high_temp_h_zero_ratio_sandwich_bundle
    (inducedGraph G Λ) J β hβJ hcard

/-- **Λ-level ferromagnetic f ratio sandwich bundle**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) :=
  freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level f ratio bound at J=0**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_bound
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply, freeEnergyΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.freeEnergy_high_temp_h_zero_ratio_bound
    (inducedGraph G Λ) J β hβJ hcard

/-- **Λ-level f ratio bound at β=0**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply, freeEnergyΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.freeEnergy_high_temp_h_zero_ratio_bound_beta_zero
    (inducedGraph G Λ) J β hβJ hcard

/-- **Λ-level f ratio bound bundle**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_bound_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  ⟨freeEnergyΛ_high_temp_h_zero_ratio_bound G Λ J β hβJ hne,
   freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero G Λ J β hβJ hne⟩

/-- **Λ-level ferromagnetic f ratio bound bundle**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound_bundle
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level triple (Z + log Z + f) ratio sandwich bundle at J=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich G Λ J β hβJ,
   (log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
     G Λ J β hβJ).1,
   (freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle G Λ J β hβJ hne).1⟩

/-- **Λ-level triple ratio sandwich bundle at β=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
     G Λ J β hβJ,
   (log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
     G Λ J β hβJ).2,
   (freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle G Λ J β hβJ hne).2⟩

/-- **Λ-level ferromagnetic triple ratio sandwich bundle at β=0**. -/
theorem
partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level ferromagnetic triple ratio sandwich bundle at J=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level triple (Z + log Z + f) ratio bound bundle at J=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound G Λ J β hβJ,
   log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound G Λ J β hβJ,
   freeEnergyΛ_high_temp_h_zero_ratio_bound G Λ J β hβJ hne⟩

/-- **Λ-level triple ratio bound bundle at β=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_bound_bundle_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
     G Λ J β hβJ,
   log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
     G Λ J β hβJ,
   freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero G Λ J β hβJ hne⟩

/-- **Λ-level ferromagnetic triple ratio bound bundle at J=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level ferromagnetic f ratio bound at J=0**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level ferromagnetic f ratio bound at β=0**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level Z high-temp sandwich (FV (3.45))**: under `0 ≤ β·J`,
`2^|Λ| · cosh^|E_Λ| ≤ Z_Λ ≤ 2^(|Λ|+|E_Λ|) · cosh^|E_Λ|`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
    ∧ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ (Λ.card + (inducedGraph G Λ).edgeFinset.card) *
          Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound G Λ J β hβJ,
   partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound G Λ J β hβJ⟩

/-- **Λ-level Z complete-summary bundle at h = 0**: under `0 ≤ β·J`,
single statement bundling Λ-level Z lower bound, upper bound, and
trivial-slice values at `J = 0` / `β = 0`. Λ-layer wrapper of
`partitionFunction_high_temp_expansion_h_zero_complete_summary`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        ≤ (2 : ℝ) ^ (Λ.card + (inducedGraph G Λ).edgeFinset.card) *
            Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card ∧
      partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        = (2 : ℝ) ^ Λ.card ∧
      partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
        = (2 : ℝ) ^ Λ.card :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound G Λ J β hβJ,
   partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound G Λ J β hβJ,
   partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero G Λ β,
   partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero G Λ J⟩

/-- **Λ-level freeEnergy complete-summary bundle at h = 0**: under
`0 < |Λ|` and `0 ≤ β·J`, single statement bundling Λ-level lower /
upper bounds and trivial-slice values at `J = 0` / `β = 0` (both =
`log 2`). Λ-layer wrapper of
`freeEnergy_high_temp_h_zero_complete_summary`. -/
theorem freeEnergyΛ_high_temp_h_zero_complete_summary
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        ≤ Real.log 2 +
            ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
              Real.log (2 * Real.cosh (β * J)) ∧
      freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
      freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  ⟨freeEnergyΛ_high_temp_h_zero_lower_bound G Λ J β hβJ hne,
   freeEnergyΛ_high_temp_h_zero_upper_bound G Λ J β hβJ hne,
   by
     have := IsingModel.freeEnergy_J_zero (inducedGraph G Λ) (0 : ℝ) β hcard
     simpa [freeEnergyΛ, mul_zero, Real.cosh_zero] using this,
   by
     have := IsingModel.freeEnergy_beta_zero (inducedGraph G Λ) J 0 hcard
     simpa [freeEnergyΛ] using this⟩

/-- **Λ-level freeEnergy high-temp sandwich (FV (3.45))**: under
`0 < |Λ|` and `0 ≤ β·J`,
`log 2 + (|E_Λ|/|Λ|) log cosh(βJ) ≤ f_Λ ≤ log 2 + (|E_Λ|/|Λ|) log(2·cosh βJ)`. -/
theorem freeEnergyΛ_high_temp_h_zero_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
    ∧ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2
        + ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
            Real.log (2 * Real.cosh (β * J)) :=
  ⟨freeEnergyΛ_high_temp_h_zero_lower_bound G Λ J β hβJ hne,
   freeEnergyΛ_high_temp_h_zero_upper_bound G Λ J β hβJ hne⟩

end Ambient

end IsingModel
