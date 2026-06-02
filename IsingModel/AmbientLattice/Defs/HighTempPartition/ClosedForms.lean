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

/-- **Λ-level general external-field high-temperature correlation expansion
(GJ §18.3/§18.5)**: on the induced subgraph `inducedGraph G Λ` and any Ising
parameter `p = (J, h, β)`,
\[
\langle \sigma_A \rangle^\Lambda_{p}
  = \frac{\sum_{X \subseteq E_\Lambda} (\tanh\beta J)^{|X|}
      \sum_\sigma \sigma_A (\prod_{e \in X} \sigma_e) \exp(\beta h \sum_i \sigma_i)}
         {\sum_{X \subseteq E_\Lambda} (\tanh\beta J)^{|X|}
      \sum_\sigma (\prod_{e \in X} \sigma_e) \exp(\beta h \sum_i \sigma_i)}.
\]
General external-field counterpart of
`correlationΛ_high_temp_expansion_h_zero_closed`; direct lift of
`IsingModel.correlation_high_temp_expansion_general_h_subset_form`
through `correlationΛ = correlation (inducedGraph G Λ)`. -/
theorem correlationΛ_high_temp_expansion_general_h_subset_form
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (A : Finset ↑Λ) :
    correlationΛ G Λ p A
      = (∑ X ∈ (inducedGraph G Λ).edgeFinset.powerset,
          Real.tanh (p.β * p.J) ^ X.card *
            ∑ σ : Config ↑Λ,
              spinProduct A σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (p.β * p.h * ∑ i : ↑Λ, Spin.sign ℝ (σ i))) /
        (∑ X ∈ (inducedGraph G Λ).edgeFinset.powerset,
          Real.tanh (p.β * p.J) ^ X.card *
            ∑ σ : Config ↑Λ,
              (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (p.β * p.h * ∑ i : ↑Λ, Spin.sign ℝ (σ i))) := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_expansion_general_h_subset_form
    (inducedGraph G Λ) p A


end Ambient

end IsingModel
