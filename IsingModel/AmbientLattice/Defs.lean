import IsingModel.InfiniteVolume
import IsingModel.FreeEnergy
import IsingModel.Inequalities.GHS
import IsingModel.Conditioning
import IsingModel.PhaseTransition
import IsingModel.FieldDerivative

/-!
# Basic finite-volume definitions for the ambient lattice framework

Foundational Λ-level wrappers forwarding the existing `IsingModel` definitions
(`partitionFunction`, `correlation`, `freeEnergy`, `magnetization`, `susceptibility`)
to arbitrary finite volumes `Λ : Finset V` of an ambient lattice `V`.

These definitions are the building blocks for the thermodynamic-limit framework
developed in `IsingModel.AmbientLattice`.

## Definitions

* `IsingModel.Ambient.ConfigOn` — configurations on `Λ`.
* `IsingModel.Ambient.inducedGraph` — induced subgraph of `G` on `Λ`.
* `IsingModel.Ambient.partitionFunctionΛ` — `Z_Λ = Z` on the induced graph.
* `IsingModel.Ambient.correlationΛ` — `⟨σ^A⟩_Λ`.
* `IsingModel.Ambient.freeEnergyΛ` — free energy per site on `Λ`.
* `IsingModel.Ambient.magnetizationΛ` — single-site magnetization on `Λ`.
* `IsingModel.Ambient.susceptibilityΛ` — susceptibility on `Λ`.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.2, §4.6.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Finite-volume configuration on `Λ`

Use `(↑Λ : Type _)` as the finite index type; this is a `Fintype`
(via `Finset.instFintypeCoe`). -/

/-- A configuration on a finite volume `Λ : Finset V`:
a function from `Λ` to `Spin`. -/
abbrev ConfigOn (Λ : Finset V) : Type _ := (↑Λ : Type _) → Spin

/-! ## Induced subgraph on `Λ`

For `G : SimpleGraph V`, the induced subgraph on `(↑Λ : Set V)` is a
`SimpleGraph (↑Λ : Type _)`. -/

/-- The induced subgraph of `G` on `Λ : Finset V`. -/
noncomputable def inducedGraph (G : SimpleGraph V) (Λ : Finset V) :
    SimpleGraph (↑Λ : Type _) :=
  G.induce (↑Λ : Set V)

omit [DecidableEq V] in
/-- **Unfolding of `inducedGraph`**:
`inducedGraph G Λ = G.induce (↑Λ : Set V)` by definition. -/
theorem inducedGraph_apply (G : SimpleGraph V) (Λ : Finset V) :
    inducedGraph G Λ = G.induce (↑Λ : Set V) := rfl

omit [DecidableEq V] in
/-- **Helper**: if `Λ : Finset V` is nonempty then the induced subtype
`↑Λ : Type _` has positive `Fintype.card`. Used throughout the Λ- and
along-exhaustion wrappers of base-layer `freeEnergy` / `freeEnergyΛ`
theorems that require `0 < Fintype.card ι`. Factors out the common
`rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne` chain. -/
theorem Finset.Nonempty.fintype_card_coe_pos {Λ : Finset V}
    (hne : Λ.Nonempty) : 0 < Fintype.card (↑Λ : Type _) := by
  rw [Fintype.card_coe]
  exact Finset.card_pos.mpr hne

/-! ## Partition function and correlation on `Λ`

Forward the existing `partitionFunction`, `correlation`, `freeEnergy`
definitions to the induced subgraph on `Λ`. -/

/-- The partition function on a finite volume `Λ`, instantiating the
existing `IsingModel.partitionFunction` on the induced subgraph. -/
noncomputable def partitionFunctionΛ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) : ℝ :=
  IsingModel.partitionFunction (inducedGraph G Λ) p

/-- **Unfolding of `partitionFunctionΛ`**: by construction, equal to
`IsingModel.partitionFunction (inducedGraph G Λ) p`. -/
theorem partitionFunctionΛ_apply (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) :
    partitionFunctionΛ G Λ p = IsingModel.partitionFunction (inducedGraph G Λ) p :=
  rfl

/-- The correlation function on a finite volume `Λ`, for a subset
`A : Finset (↑Λ)` of sites. -/
noncomputable def correlationΛ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) : ℝ :=
  IsingModel.correlation (inducedGraph G Λ) p A

/-- **Unfolding of `correlationΛ`**: by construction, equal to
`IsingModel.correlation (inducedGraph G Λ) p A`. -/
theorem correlationΛ_apply (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ G Λ p A = IsingModel.correlation (inducedGraph G Λ) p A := rfl

/-- The free energy per site on a finite volume `Λ`. -/
noncomputable def freeEnergyΛ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) : ℝ :=
  IsingModel.freeEnergy (inducedGraph G Λ) p

/-- **Unfolding of `freeEnergyΛ`**: by construction, equal to
`IsingModel.freeEnergy (inducedGraph G Λ) p`. -/
theorem freeEnergyΛ_apply (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) :
    freeEnergyΛ G Λ p = IsingModel.freeEnergy (inducedGraph G Λ) p := rfl

/-- **`freeEnergyΛ` as `|Λ|⁻¹ · log Z_Λ`** (named restatement of the
definition unfolding `IsingModel.freeEnergy := (Fintype.card ι)⁻¹ ·
log Z`). The ambient `Fintype.card` is taken on the subtype `↑Λ`, which
coincides with `Λ.card` via `Fintype.card_coe`. -/
theorem freeEnergyΛ_eq_inv_card_mul_log
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) :
    freeEnergyΛ G Λ p
      = (Fintype.card (↑Λ : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionΛ G Λ p) := rfl

/-- **`freeEnergyΛ` with `Λ.card` cast**: using `Fintype.card_coe`,
`freeEnergyΛ G Λ p = (Λ.card : ℝ)⁻¹ · log (partitionFunctionΛ G Λ p)`.
Convenient form when working with the Finset cardinality directly. -/
theorem freeEnergyΛ_eq_inv_Λcard_mul_log
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) :
    freeEnergyΛ G Λ p
      = (Λ.card : ℝ)⁻¹ * Real.log (partitionFunctionΛ G Λ p) := by
  rw [freeEnergyΛ_eq_inv_card_mul_log, Fintype.card_coe]

/-- The **magnetization** on a finite volume `Λ` at site `i : ↑Λ`:
`M_Λ(i) = ⟨σ_i⟩ = correlationΛ G Λ p {i}`. Direct analog of
`IsingModel.magnetization` at the ambient-lattice Λ layer, matching
the `correlationΛ` / `partitionFunctionΛ` / `freeEnergyΛ` pattern. -/
noncomputable def magnetizationΛ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (i : ↑Λ) : ℝ :=
  correlationΛ G Λ p {i}

/-! ## Basic lemmas (forwarded from existing framework)

Since the definitions are direct instantiations, the existing theorems
apply automatically under the appropriate instances. -/

/-- The partition function on `Λ` is positive. -/
theorem partitionFunctionΛ_pos (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) :
    0 < partitionFunctionΛ G Λ p :=
  IsingModel.partitionFunction_pos _ _

/-- **Λ-level partition-function h-evenness**:
`Z_Λ(J, -h, β) = Z_Λ(J, h, β)`. Direct lift of
`IsingModel.partitionFunction_neg_h` (GibbsMeasure.lean) through
`partitionFunctionΛ = partitionFunction (inducedGraph G Λ)`. The
flip involution `σ ↦ σ.flip` on `Config (↑Λ)` reindexes the sum. -/
theorem partitionFunctionΛ_neg_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    partitionFunctionΛ G Λ (⟨J, -h, β⟩ : IsingParams ℝ)
      = partitionFunctionΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_neg_h _ J h β

/-- **Λ-level J-monotonicity of `partitionFunctionΛ`** (pointwise form).
Direct lift of `IsingModel.partitionFunction_monotone_J`. -/
theorem partitionFunctionΛ_monotone_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) :
    partitionFunctionΛ G Λ (⟨J₁, h, β⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ G Λ (⟨J₂, h, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_monotone_J _ h β hh hβ J₁ J₂ hJ₁ hJ

/-- **Λ-level h-monotonicity of `partitionFunctionΛ`** (pointwise form).
Direct lift of `IsingModel.partitionFunction_monotone_h`. -/
theorem partitionFunctionΛ_monotone_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) :
    partitionFunctionΛ G Λ (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_monotone_h _ J β hJ hβ h₁ h₂ hh₁ hh

/-- **Λ-level β-monotonicity of `partitionFunctionΛ`** (pointwise form).
Direct lift of `IsingModel.partitionFunction_monotone_beta`. -/
theorem partitionFunctionΛ_monotone_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    partitionFunctionΛ G Λ (⟨J, h, β₁⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ G Λ (⟨J, h, β₂⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_monotone_beta _ J h hJ hh β₁ β₂ hβ₁ hβ

/-- **Λ-level partition-function `|h|`-rewrite**:
`Z_Λ(J, h, β) = Z_Λ(J, |h|, β)`. Direct lift of
`IsingModel.partitionFunction_eq_abs_h`. -/
theorem partitionFunctionΛ_eq_abs_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    partitionFunctionΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ)
      = partitionFunctionΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_eq_abs_h _ J h β

/-- **Λ-level ferromagnetic `|h|`-monotonicity of `partitionFunctionΛ`**:
for `J ≥ 0`, `β > 0`, `|h₁| ≤ |h₂|`,
`Z_Λ(J, h₁, β) ≤ Z_Λ(J, h₂, β)`. Direct lift of
`IsingModel.partitionFunction_monotone_abs_h`. -/
theorem partitionFunctionΛ_monotone_abs_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    partitionFunctionΛ G Λ (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_monotone_abs_h _ J β hJ hβ hh

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

/-- **Λ-level FV (3.46) numerator vanishes for odd-cardinality A** at `h = 0`:
for `A : Finset ↑Λ` of odd cardinality,
`∑_{X ⊆ E_Λ : ∂X = A} tanh(β J)^|X| = 0`.
Direct lift of `IsingModel.sum_high_temp_numerator_h_zero_odd_card_eq_zero`
(Step 291) through the induced subgraph on `Λ`. -/
theorem sum_high_temp_numerator_h_zero_odd_card_eq_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset ↑Λ) (hA_odd : Odd A.card) :
    ∑ X ∈ (inducedGraph G Λ).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑Λ) => ∀ v : ↑Λ,
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card = 0 :=
  IsingModel.sum_high_temp_numerator_h_zero_odd_card_eq_zero
    (inducedGraph G Λ) J β A hA_odd

/-- **Λ-level correlation nonnegativity from FV (3.46)** at `h = 0`:
under `0 ≤ β * J`, `0 ≤ correlationΛ G Λ ⟨J, 0, β⟩ A`.
Direct lift of `IsingModel.correlation_high_temp_h_zero_nonneg`
(Step 293) through `correlationΛ_apply`. -/
theorem correlationΛ_high_temp_h_zero_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (A : Finset ↑Λ) :
    0 ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_nonneg
    (inducedGraph G Λ) J β hβJ A

/-- **Λ-level high-temperature even-subgraph sum is `≥ 1`**: under
`0 ≤ β * J`,
`∑_{X ⊆ E_Λ, even-degree at every v ∈ ↑Λ} tanh(β J)^|X| ≥ 1`.
Direct lift of `IsingModel.one_le_sum_pow_tanh_even_subgraph`
(Step 295) through the induced subgraph on `Λ`. -/
theorem one_le_sum_pow_tanh_even_subgraph_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (1 : ℝ) ≤ ∑ X ∈ (inducedGraph G Λ).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑Λ) =>
          ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card :=
  IsingModel.one_le_sum_pow_tanh_even_subgraph (inducedGraph G Λ) J β hβJ

/-- **Λ-level FV (3.46) numerator filter is empty for odd-cardinality A**:
the filtered powerset over which the FV (3.46) numerator sums is
*literally empty* whenever `|A|` is odd.
Direct lift of `IsingModel.high_temp_numerator_filter_eq_empty_of_odd_card`
(Step 297). -/
theorem high_temp_numerator_filter_eq_empty_of_odd_card_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (A : Finset ↑Λ) (hA_odd : Odd A.card) :
    (inducedGraph G Λ).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑Λ) => ∀ v : ↑Λ,
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)) = ∅ :=
  IsingModel.high_temp_numerator_filter_eq_empty_of_odd_card
    (inducedGraph G Λ) A hA_odd

/-- **Λ-level Z₂ symmetry of correlation at h = 0 from FV (3.46) + handshake**:
for `A : Finset ↑Λ` of odd cardinality,
`correlationΛ G Λ ⟨J, 0, β⟩ A = 0`.
Direct lift of `IsingModel.correlation_high_temp_h_zero_odd_card_eq_zero`
(Step 298). -/
theorem correlationΛ_high_temp_h_zero_odd_card_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset ↑Λ) (hA_odd : Odd A.card) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A = 0 := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_odd_card_eq_zero
    (inducedGraph G Λ) J β A hA_odd

/-- The correlation on `Λ` is bounded: `|⟨σ^A⟩| ≤ 1`. -/
theorem abs_correlationΛ_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    |correlationΛ G Λ p A| ≤ 1 :=
  IsingModel.abs_correlation_le_one _ _ _

/-- The correlation on `Λ` is at most `1`. -/
theorem correlationΛ_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ G Λ p A ≤ 1 :=
  IsingModel.correlation_le_one _ _ _

/-- The correlation on `Λ` is at least `-1`. Lower side of
`abs_correlationΛ_le_one`. -/
theorem neg_one_le_correlationΛ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    -1 ≤ correlationΛ G Λ p A :=
  (abs_le.mp (abs_correlationΛ_le_one G Λ p A)).1

/-- **`correlationΛ² ≤ 1`** unconditionally. -/
theorem correlationΛ_sq_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ G Λ p A ^ 2 ≤ 1 :=
  IsingModel.correlation_sq_le_one _ p A

/-- For ferromagnetic `p`, the correlation on `Λ` is non-negative
(GKS-I, lifted to the ambient framework). -/
theorem correlationΛ_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (A : Finset (↑Λ : Type _)) :
    0 ≤ correlationΛ G Λ p A :=
  gks_first _ _ hf _

/-- **Unfolding of `magnetizationΛ`**:
`magnetizationΛ G Λ p i = correlationΛ G Λ p {i}`, by definition. -/
theorem magnetizationΛ_apply (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (i : ↑Λ) :
    magnetizationΛ G Λ p i = correlationΛ G Λ p {i} := rfl

/-- **`magnetizationΛ ≤ 1`** at any site `i : ↑Λ`, for any parameters.
Direct from `correlationΛ_le_one` at `A = {i}`. -/
theorem magnetizationΛ_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) (i : ↑Λ) :
    magnetizationΛ G Λ p i ≤ 1 :=
  correlationΛ_le_one G Λ p {i}

/-- **`|magnetizationΛ| ≤ 1`** at any site `i : ↑Λ`, for any parameters.
Direct from `abs_correlationΛ_le_one` at `A = {i}`. -/
theorem abs_magnetizationΛ_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) (i : ↑Λ) :
    |magnetizationΛ G Λ p i| ≤ 1 :=
  abs_correlationΛ_le_one G Λ p {i}

/-- **`-1 ≤ magnetizationΛ`** at any site `i : ↑Λ`, for any parameters. -/
theorem neg_one_le_magnetizationΛ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) (i : ↑Λ) :
    -1 ≤ magnetizationΛ G Λ p i :=
  neg_one_le_correlationΛ G Λ p {i}

/-- **`magnetizationΛ² ≤ 1`** unconditionally. From
`abs_magnetizationΛ_le_one` via `sq_le_one'`. -/
theorem magnetizationΛ_sq_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) (i : ↑Λ) :
    magnetizationΛ G Λ p i ^ 2 ≤ 1 := by
  have h := abs_magnetizationΛ_le_one G Λ p i
  have : |magnetizationΛ G Λ p i| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **`magnetizationΛ ≥ 0`** for ferromagnetic `p` at any site `i : ↑Λ`.
Direct from `correlationΛ_nonneg` at `A = {i}` (GKS-I). -/
theorem magnetizationΛ_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (i : ↑Λ) :
    0 ≤ magnetizationΛ G Λ p i :=
  correlationΛ_nonneg G Λ p hf {i}

/-- The **susceptibility** on a finite volume `Λ` at site `i : ↑Λ`:
`χ_Λ(i) = Σ_{j : ↑Λ} ⟨σ_i; σ_j⟩ = IsingModel.susceptibility (inducedGraph G Λ) p i`.
Direct analog of `IsingModel.susceptibility` at the ambient-lattice Λ layer,
matching the `correlationΛ` / `magnetizationΛ` / `partitionFunctionΛ` pattern.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
noncomputable def susceptibilityΛ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (i : ↑Λ) : ℝ :=
  IsingModel.susceptibility (inducedGraph G Λ) p i

/-- **Unfolding of `susceptibilityΛ`**:
`susceptibilityΛ G Λ p i = IsingModel.susceptibility (inducedGraph G Λ) p i`,
by definition. -/
theorem susceptibilityΛ_apply (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) (i : ↑Λ) :
    susceptibilityΛ G Λ p i = IsingModel.susceptibility (inducedGraph G Λ) p i :=
  rfl

/-- **`susceptibilityΛ ≥ 0`** for ferromagnetic `p` at any site `i : ↑Λ`.
Direct lift of `IsingModel.susceptibility_nonneg` through
`susceptibilityΛ := IsingModel.susceptibility (inducedGraph G Λ)`. -/
theorem susceptibilityΛ_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (i : ↑Λ) :
    0 ≤ susceptibilityΛ G Λ p i :=
  IsingModel.susceptibility_nonneg (inducedGraph G Λ) p hf i

/-! ## Step 258: Λ-layer regularity wrappers (β/h/J at general h) -/

/-- **freeEnergyΛ Continuous in β at general h** (Step 258, general G, Λ). -/
theorem freeEnergyΛ_continuous_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    Continuous (fun β' => freeEnergyΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ)) :=
  IsingModel.freeEnergy_continuous_beta_general_h _ J h

/-- **freeEnergyΛ Differentiable in β at general h** (Step 258, general G, Λ). -/
theorem freeEnergyΛ_differentiable_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    Differentiable ℝ (fun β' => freeEnergyΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ)) :=
  IsingModel.freeEnergy_differentiable_beta_general_h _ J h

/-- **freeEnergyΛ Continuous in h** (Step 258, general G, Λ). -/
theorem freeEnergyΛ_continuous_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    Continuous (fun h' => freeEnergyΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ)) :=
  IsingModel.freeEnergy_continuous_field _ J β

/-- **freeEnergyΛ Differentiable in h** (Step 258, general G, Λ). -/
theorem freeEnergyΛ_differentiable_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    Differentiable ℝ (fun h' => freeEnergyΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ)) :=
  IsingModel.freeEnergy_differentiable_field _ J β

/-- **freeEnergyΛ Continuous in J** (Step 258, general G, Λ). -/
theorem freeEnergyΛ_continuous_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) :
    Continuous (fun J' => freeEnergyΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ)) :=
  IsingModel.freeEnergy_continuous_J _ h β

/-- **freeEnergyΛ Differentiable in J** (Step 258, general G, Λ). -/
theorem freeEnergyΛ_differentiable_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) :
    Differentiable ℝ (fun J' => freeEnergyΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ)) :=
  IsingModel.freeEnergy_differentiable_J _ h β

/-- **magnetizationΛ Continuous in β at general h** (Step 258, general G, Λ). -/
theorem magnetizationΛ_continuous_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) (i : ↑Λ) :
    Continuous (fun β' => magnetizationΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_beta_general_h _ J h _

/-- **magnetizationΛ Differentiable in β at general h** (Step 258, general G, Λ). -/
theorem magnetizationΛ_differentiable_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun β' => magnetizationΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_beta_general_h _ J h _

/-- **susceptibilityΛ Continuous in β at general h** (Step 258, general G, Λ). -/
theorem susceptibilityΛ_continuous_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) (i : ↑Λ) :
    Continuous (fun β' => susceptibilityΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_continuous_beta_general_h _ J h _

/-- **susceptibilityΛ Differentiable in β at general h** (Step 258, general G, Λ). -/
theorem susceptibilityΛ_differentiable_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun β' => susceptibilityΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_differentiable_beta_general_h _ J h _

end Ambient
end IsingModel
