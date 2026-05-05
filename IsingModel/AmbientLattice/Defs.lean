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

/-- **Λ-level §18.7 capstone: high-temperature exponential decay of
the pair correlation in graph distance**. Under `0 ≤ β·J`, for
`i, j : ↑Λ`,
`⟨σ_iσ_j⟩^{Λ}_{β,0} ≤ 2^{|E_Λ|} · tanh(β·J)^{(inducedGraph G Λ).dist i j}`.
Direct lift of `IsingModel.correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist`
(Step 574) through `correlationΛ_apply`. -/
theorem
correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card *
        Real.tanh (β * J) ^ (inducedGraph G Λ).dist i j := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (inducedGraph G Λ) J β hβJ i j

/-- **Λ-level §18.7 ferromagnetic capstone**: under `0 ≤ J, 0 < β`,
the same exponential-decay bound as the non-ferromagnetic Λ wrap. -/
theorem
correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card *
        Real.tanh (β * J) ^ (inducedGraph G Λ).dist i j :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    G Λ J β (mul_nonneg hβ.le hJ) i j

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

/-- **Λ-level magnetization vanishes at h = 0**:
`correlationΛ G Λ ⟨J, 0, β⟩ {i} = 0` for any single site `i : ↑Λ`.
Specialization at `A = {i}`. -/
theorem correlationΛ_high_temp_h_zero_at_singleton
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 := by
  refine correlationΛ_high_temp_h_zero_odd_card_eq_zero G Λ J β {i} ?_
  rw [Finset.card_singleton]; exact ⟨0, rfl⟩

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

/-- **Λ-level pair correlation nonneg at h = 0**:
under `0 ≤ β·J`, `0 ≤ correlationΛ G Λ ⟨J, 0, β⟩ {i, j}`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    0 ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_nonneg G Λ J β hβJ {i, j}

/-- **Λ-level pair correlation ≤ 1**:
`correlationΛ G Λ ⟨J, 0, β⟩ {i, j} ≤ 1`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_le_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_le_one G Λ _ {i, j}

/-- **Λ-level singleton at β=0,h=0**: `correlationΛ G Λ ⟨J,0,0⟩ {i} = 0`. -/
theorem correlationΛ_high_temp_h_zero_at_singleton_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) (i : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_at_singleton_beta_zero
    (inducedGraph G Λ) J i

/-- **Λ-level pair at β=0,h=0**: `correlationΛ G Λ ⟨J,0,0⟩ {i,j} = 0`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_at_pair_beta_zero
    (inducedGraph G Λ) J i j

/-- **Λ-level singleton at J=0,h=0**: `correlationΛ G Λ ⟨0,0,β⟩ {i} = 0`. -/
theorem correlationΛ_high_temp_h_zero_at_singleton_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (i : ↑Λ) :
    correlationΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_at_singleton_J_zero
    (inducedGraph G Λ) β i

/-- **Λ-level pair at J=0,h=0**: `correlationΛ G Λ ⟨0,0,β⟩ {i,j} = 0`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (i j : ↑Λ) :
    correlationΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_at_pair_J_zero
    (inducedGraph G Λ) β i j

/-- **Λ-pair sandwich at h=0**: `0 ≤ correlationΛ G Λ ⟨J,0,β⟩ {i,j} ≤ 1`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    0 ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  ⟨correlationΛ_high_temp_h_zero_at_pair_nonneg G Λ J β hβJ i j,
   correlationΛ_high_temp_h_zero_at_pair_le_one G Λ J β i j⟩

/-- **Λ-pair ferromagnetic at h=0**: `0 ≤ J, 0 < β` → pair sandwich. -/
theorem correlationΛ_high_temp_h_zero_at_pair_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    0 ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_high_temp_h_zero_at_pair_sandwich G Λ J β
    (mul_nonneg hβ.le hJ) i j

/-- **Λ singleton ferromagnetic vanish**: `0 ≤ J, 0 < β` → `⟨σ_i⟩^Λ = 0`. -/
theorem correlationΛ_high_temp_h_zero_at_singleton_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (_hJ : 0 ≤ J) (_hβ : 0 < β) (i : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_singleton G Λ J β i

/-- **Λ singleton sandwich at h = 0**: `⟨σ_i⟩^Λ = 0 ∧ ≤ 1`. -/
theorem correlationΛ_high_temp_h_zero_at_singleton_eq_zero_le_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) ≤ 1 :=
  ⟨correlationΛ_high_temp_h_zero_at_singleton G Λ J β i,
   (correlationΛ_high_temp_h_zero_at_singleton G Λ J β i).symm ▸ zero_le_one⟩

/-- **Λ pair+singleton bundle at h=0**: combines pair sandwich and
singleton vanishing. -/
theorem correlationΛ_high_temp_h_zero_at_pair_singleton_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      0 ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  ⟨correlationΛ_high_temp_h_zero_at_singleton G Λ J β i,
   correlationΛ_high_temp_h_zero_at_pair_nonneg G Λ J β hβJ i j,
   correlationΛ_high_temp_h_zero_at_pair_le_one G Λ J β i j⟩

/-- **Λ pair+singleton bundle under ferromagnetic at h = 0**: under
`0 ≤ J, 0 < β`, packages `⟨σ_i⟩^Λ = 0`, `0 ≤ ⟨σ_iσ_j⟩^Λ`, and
`⟨σ_iσ_j⟩^Λ ≤ 1` into a single triple. Λ-layer wrapper of
`correlation_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      0 ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_high_temp_h_zero_at_pair_singleton_bundle G Λ J β
    (mul_nonneg hβ.le hJ) i j

/-- **Λ pair + singleton complete-summary bundle at h = 0**: under
`0 ≤ β·J`, single statement bundling pair upper bound, pair sandwich
lower, singleton vanishing, and pair vanishing at `J = 0` / `β = 0`
trivial slices. Λ-layer wrapper of
`correlation_high_temp_h_zero_at_pair_singleton_complete_summary`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_singleton_complete_summary
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 ∧
      0 ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      correlationΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 ∧
      correlationΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 :=
  ⟨correlationΛ_high_temp_h_zero_at_pair_le_one G Λ J β i j,
   correlationΛ_high_temp_h_zero_at_pair_nonneg G Λ J β hβJ i j,
   correlationΛ_high_temp_h_zero_at_singleton G Λ J β i,
   correlationΛ_high_temp_h_zero_at_pair_J_zero G Λ β i j,
   correlationΛ_high_temp_h_zero_at_pair_beta_zero G Λ J i j⟩

/-- **Λ pair + singleton trivial-slices full bundle at h = 0**:
at `J = 0` and `β = 0`, both Λ-pair and Λ-singleton correlations vanish.
Λ-layer wrapper of
`correlation_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (i j : ↑Λ) :
    correlationΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      correlationΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      correlationΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 ∧
      correlationΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 :=
  ⟨correlationΛ_high_temp_h_zero_at_singleton_J_zero G Λ β i,
   correlationΛ_high_temp_h_zero_at_singleton_beta_zero G Λ J i,
   correlationΛ_high_temp_h_zero_at_pair_J_zero G Λ β i j,
   correlationΛ_high_temp_h_zero_at_pair_beta_zero G Λ J i j⟩

/-- **Λ pair correlation single-edge tanh lower bound (GJ §18.3 / FV (3.46))**:
under `0 ≤ β·J` and an edge `s(i, j) ∈ (inducedGraph G Λ).edgeSet`,
`⟨σ_iσ_j⟩^Λ ≥ tanh(β·J) / 2^|E_Λ|` where `i, j : ↑Λ`. Λ-layer wrapper
of `correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G Λ).edgeSet) :
    Real.tanh (β * J) / (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          ({i, j} : Finset ↑Λ) := by
  rw [correlationΛ_apply]
  exact correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (inducedGraph G Λ) J β hβJ i j hij he

/-- **Λ pair correlation strict positivity under edge (GJ §18.3 / FV (3.46))**:
under `0 < β·J` and an edge `s(i, j) ∈ (inducedGraph G Λ).edgeSet`,
`0 < ⟨σ_iσ_j⟩^Λ`. Λ-layer wrapper of
`correlation_high_temp_h_zero_at_pair_pos_of_edge`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_pos_of_edge
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G Λ).edgeSet) :
    0 < correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑Λ) := by
  rw [correlationΛ_apply]
  exact correlation_high_temp_h_zero_at_pair_pos_of_edge
    (inducedGraph G Λ) J β hβJ i j hij he

/-- **Λ ferromagnetic pair single-edge tanh lower bound (GJ §18.3 / FV (3.46))**:
under `0 ≤ J, 0 < β` and an edge `s(i, j) ∈ (inducedGraph G Λ).edgeSet`,
`⟨σ_iσ_j⟩^Λ ≥ tanh(β·J) / 2^|E_Λ|`. Λ-layer wrapper of
`correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G Λ).edgeSet) :
    Real.tanh (β * J) / (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    G Λ J β (mul_nonneg hβ.le hJ) i j hij he

/-- **Λ ferromagnetic pair strict positivity under edge (GJ §18.3 / FV (3.46))**:
under `0 < J, 0 < β` and an edge `s(i, j) ∈ (inducedGraph G Λ).edgeSet`,
`0 < ⟨σ_iσ_j⟩^Λ`. Λ-layer wrapper of
`correlation_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G Λ).edgeSet) :
    0 < correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_pos_of_edge
    G Λ J β (mul_pos hβ hJ) i j hij he

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

/-- **magnetizationΛ Continuous in `h`**. -/
theorem magnetizationΛ_continuous_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) (i : ↑Λ) :
    Continuous (fun h' => magnetizationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_continuous_field _ J β _

/-- **magnetizationΛ Differentiable in `h`**. -/
theorem magnetizationΛ_differentiable_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ)
    (i : ↑Λ) :
    Differentiable ℝ
      (fun h' => magnetizationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_differentiable_field _ J β _

/-- **magnetizationΛ Continuous in `J`**. -/
theorem magnetizationΛ_continuous_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) (i : ↑Λ) :
    Continuous (fun J' => magnetizationΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_continuous_J _ h β _

/-- **magnetizationΛ Differentiable in `J`**. -/
theorem magnetizationΛ_differentiable_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) (i : ↑Λ) :
    Differentiable ℝ
      (fun J' => magnetizationΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_differentiable_J _ h β _

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

/-- **susceptibilityΛ Continuous in `h`**. -/
theorem susceptibilityΛ_continuous_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) (i : ↑Λ) :
    Continuous (fun h' => susceptibilityΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_continuous_field _ J β _

/-- **susceptibilityΛ Differentiable in `h`**. -/
theorem susceptibilityΛ_differentiable_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ)
    (i : ↑Λ) :
    Differentiable ℝ
      (fun h' => susceptibilityΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_differentiable_field _ J β _

/-- **susceptibilityΛ Continuous in `J`**. -/
theorem susceptibilityΛ_continuous_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) (i : ↑Λ) :
    Continuous (fun J' => susceptibilityΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_continuous_J _ h β _

/-- **susceptibilityΛ Differentiable in `J`**. -/
theorem susceptibilityΛ_differentiable_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) (i : ↑Λ) :
    Differentiable ℝ
      (fun J' => susceptibilityΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_differentiable_J _ h β _

/-- **magnetizationΛ β → ∞ convergence** under ferromagnetic
`J, h ≥ 0`. -/
theorem magnetizationΛ_convergent_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => magnetizationΛ G Λ
        (⟨J, h, (n + 1 : ℝ)⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_convergent_beta _ J hJ h hh _

/-- **magnetizationΛ h → ∞ convergence** under `J ≥ 0, β > 0`. -/
theorem magnetizationΛ_convergent_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => magnetizationΛ G Λ
        (⟨J, (n : ℝ), β⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_convergent_h _ J hJ β hβ _

/-- **magnetizationΛ J → ∞ convergence** under `h ≥ 0, β > 0`. -/
theorem magnetizationΛ_convergent_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => magnetizationΛ G Λ
        (⟨(n : ℝ), h, β⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_convergent_J _ h hh β hβ _

/-- **susceptibilityΛ β → ∞ convergence** under `J, h ≥ 0`. -/
theorem susceptibilityΛ_convergent_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibilityΛ G Λ
        (⟨J, h, (n + 1 : ℝ)⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_convergent_beta _ J hJ h hh _

/-- **susceptibilityΛ h → ∞ convergence** under `J ≥ 0, β > 0`. -/
theorem susceptibilityΛ_convergent_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibilityΛ G Λ
        (⟨J, (n : ℝ), β⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_convergent_h _ J hJ β hβ _

/-- **susceptibilityΛ J → ∞ convergence** under `h ≥ 0, β > 0`. -/
theorem susceptibilityΛ_convergent_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibilityΛ G Λ
        (⟨(n : ℝ), h, β⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_convergent_J _ h hh β hβ _

/-- **susceptibilityΛ HasDerivAt β at h = 0** with explicit derivative
as sum over induced-graph sites. -/
theorem susceptibilityΛ_hasDerivAt_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun β' => susceptibilityΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i)
      (∑ j : ↑Λ, deriv (fun β' =>
        IsingModel.truncated2 (inducedGraph G Λ)
          (⟨J, 0, β'⟩ : IsingParams ℝ) i j) β) β := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_hasDerivAt_beta _ J β _

/-- **susceptibilityΛ HasDerivAt β at general h** with explicit
derivative. -/
theorem susceptibilityΛ_hasDerivAt_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun β' => susceptibilityΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i)
      (∑ j : ↑Λ, deriv (fun β' =>
        IsingModel.truncated2 (inducedGraph G Λ)
          (⟨J, h, β'⟩ : IsingParams ℝ) i j) β) β := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_hasDerivAt_beta_general_h _ J h β _

/-- **susceptibilityΛ HasDerivAt J** with explicit derivative. -/
theorem susceptibilityΛ_hasDerivAt_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun J' => susceptibilityΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) i)
      (∑ j : ↑Λ, deriv (fun J' =>
        IsingModel.truncated2 (inducedGraph G Λ)
          (⟨J', h, β⟩ : IsingParams ℝ) i j) J) J := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_hasDerivAt_J _ J h β _

/-- **magnetizationΛ HasDerivAt J** with explicit derivative as sum
over induced-graph edges. -/
theorem magnetizationΛ_hasDerivAt_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun J' => magnetizationΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) i)
      (β * ∑ e ∈ (inducedGraph G Λ).edgeFinset,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff {i} {u, v}) -
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {i} *
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e)
      J := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_hasDerivAt_J _ J h β _

/-- **correlationΛ Continuous in β at h = 0**. -/
theorem correlationΛ_continuous_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (A : Finset (↑Λ : Type _)) :
    Continuous
      (fun β' => correlationΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_beta _ J A

/-- **correlationΛ Continuous in β at general h**. -/
theorem correlationΛ_continuous_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h : ℝ) (A : Finset (↑Λ : Type _)) :
    Continuous
      (fun β' => correlationΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_beta_general_h _ J h A

/-- **correlationΛ Differentiable in β at h = 0**. -/
theorem correlationΛ_differentiable_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun β' => correlationΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_beta _ J A

/-- **correlationΛ Differentiable in β at general h**. -/
theorem correlationΛ_differentiable_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h : ℝ) (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun β' => correlationΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_beta_general_h _ J h A

/-- **correlationΛ Continuous in `h`**. -/
theorem correlationΛ_continuous_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) :
    Continuous
      (fun h' => correlationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_field _ J β A

/-- **correlationΛ Differentiable in `h`**. -/
theorem correlationΛ_differentiable_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun h' => correlationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_field _ J β A

/-- **correlationΛ Continuous in `J`**. -/
theorem correlationΛ_continuous_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h β : ℝ) (A : Finset (↑Λ : Type _)) :
    Continuous
      (fun J' => correlationΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_J _ h β A

/-- **correlationΛ Differentiable in `J`**. -/
theorem correlationΛ_differentiable_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h β : ℝ) (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun J' => correlationΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_J _ h β A

/-- **correlationΛ ContinuousAt β at h = 0** at a specific point. -/
theorem correlationΛ_continuousAt_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) :
    ContinuousAt
      (fun β' => correlationΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A) β := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuousAt_beta _ J β A

/-- **correlationΛ ContinuousAt h** at a specific point. -/
theorem correlationΛ_continuousAt_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    ContinuousAt
      (fun h' => correlationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) A) h := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuousAt_field _ J h β A

/-- **correlationΛ DifferentiableAt h** at a specific point. -/
theorem correlationΛ_differentiableAt_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    DifferentiableAt ℝ
      (fun h' => correlationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) A) h := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiableAt_field _ J h β A

/-- **susceptibilityΛ ContinuousAt β at h = 0**. -/
theorem susceptibilityΛ_continuousAt_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    ContinuousAt
      (fun β' => susceptibilityΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i)
      β := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_continuousAt_beta _ J β _

/-- **susceptibilityΛ DifferentiableAt β at h = 0**. -/
theorem susceptibilityΛ_differentiableAt_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    DifferentiableAt ℝ
      (fun β' => susceptibilityΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i)
      β := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_differentiableAt_beta _ J β _

/-- **susceptibilityΛ ContinuousAt h**. -/
theorem susceptibilityΛ_continuousAt_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    ContinuousAt
      (fun h' => susceptibilityΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i)
      h := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_continuousAt_field _ J h β _

/-- **susceptibilityΛ DifferentiableAt h**. -/
theorem susceptibilityΛ_differentiableAt_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    DifferentiableAt ℝ
      (fun h' => susceptibilityΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i)
      h := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_differentiableAt_field _ J h β _

/-- **HasDerivAt for `freeEnergyΛ` in β at general h** with explicit
derivative `(|↑Λ|)⁻¹ · ⟨−H⟩`. -/
theorem hasDerivAt_freeEnergyΛ_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun β' => freeEnergyΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ))
      ((Fintype.card ↑(Λ : Finset V) : ℝ)⁻¹ *
        IsingModel.gibbsExpectation (inducedGraph G Λ)
          (⟨J, h, β⟩ : IsingParams ℝ)
          (fun σ => - IsingModel.hamiltonian (inducedGraph G Λ)
                      (⟨J, h, β⟩ : IsingParams ℝ) σ)) β := by
  simp_rw [freeEnergyΛ_apply]
  exact IsingModel.hasDerivAt_freeEnergy_beta_general_h _ J h β

/-- **HasDerivAt for `freeEnergyΛ` in J** with explicit derivative
`(|↑Λ|)⁻¹ · ⟨β·∑_e edgeSpin⟩`. -/
theorem hasDerivAt_freeEnergyΛ_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    HasDerivAt (fun J' => freeEnergyΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ))
      ((Fintype.card ↑(Λ : Finset V) : ℝ)⁻¹ *
        IsingModel.gibbsExpectation (inducedGraph G Λ)
          (⟨J, h, β⟩ : IsingParams ℝ)
          (fun σ => β * (∑ e ∈ (inducedGraph G Λ).edgeFinset,
            IsingModel.edgeSpin (K := ℝ) σ e))) J := by
  simp_rw [freeEnergyΛ_apply]
  exact IsingModel.hasDerivAt_freeEnergy_J _ J h β

/-- **HasDerivAt for `freeEnergyΛ` in h** with explicit derivative
`(|↑Λ|)⁻¹ · ⟨β · M⟩` (magnetization per site). -/
theorem hasDerivAt_freeEnergyΛ_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    HasDerivAt (fun h' => freeEnergyΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ))
      ((Fintype.card ↑(Λ : Finset V) : ℝ)⁻¹ *
        IsingModel.gibbsExpectation (inducedGraph G Λ)
          (⟨J, h, β⟩ : IsingParams ℝ)
          (fun σ => β * IsingModel.totalMagnetization σ)) h := by
  simp_rw [freeEnergyΛ_apply]
  exact IsingModel.hasDerivAt_freeEnergy_field _ J h β

/-- **HasDerivAt for `partitionFunctionΛ` in β** with explicit
derivative as Boltzmann-weighted Hamiltonian sum. -/
theorem hasDerivAt_partitionFunctionΛ_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun β' => partitionFunctionΛ G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ))
      (∑ σ : IsingModel.Config ↑(Λ : Finset V),
        - IsingModel.hamiltonian (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ *
          IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) β := by
  simp_rw [partitionFunctionΛ_apply]
  exact IsingModel.hasDerivAt_partitionFunction_beta _ J h β

/-- **HasDerivAt for `partitionFunctionΛ` in J** with explicit
derivative as Boltzmann-weighted edge-spin sum. -/
theorem hasDerivAt_partitionFunctionΛ_J (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun J' => partitionFunctionΛ G Λ
        (⟨J', h, β⟩ : IsingParams ℝ))
      (∑ σ : IsingModel.Config ↑(Λ : Finset V),
        β * (∑ e ∈ (inducedGraph G Λ).edgeFinset,
              IsingModel.edgeSpin (K := ℝ) σ e) *
          IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) J := by
  simp_rw [partitionFunctionΛ_apply]
  exact IsingModel.hasDerivAt_partitionFunction_J _ J h β

/-- **HasDerivAt for `partitionFunctionΛ` in h** with explicit
derivative as Boltzmann-weighted total-magnetization sum. -/
theorem hasDerivAt_partitionFunctionΛ_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun h' => partitionFunctionΛ G Λ
        (⟨J, h', β⟩ : IsingParams ℝ))
      (∑ σ : IsingModel.Config ↑(Λ : Finset V),
        β * IsingModel.totalMagnetization σ *
          IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) h := by
  simp_rw [partitionFunctionΛ_apply]
  exact IsingModel.hasDerivAt_partitionFunction_field _ J h β

omit [DecidableEq V] in
/-- **HasDerivAt for ambient-induced Boltzmann weight in β** at a
single configuration `σ : Config ↑Λ`. -/
theorem hasDerivAt_boltzmannWeightΛ_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (σ : IsingModel.Config ↑(Λ : Finset V)) :
    HasDerivAt
      (fun β' => IsingModel.boltzmannWeight (inducedGraph G Λ)
        (⟨J, h, β'⟩ : IsingParams ℝ) σ)
      (- IsingModel.hamiltonian (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ *
         IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) β :=
  IsingModel.hasDerivAt_boltzmannWeight_beta _ J h β σ

omit [DecidableEq V] in
/-- **HasDerivAt for ambient-induced Boltzmann weight in J** at a
single configuration. -/
theorem hasDerivAt_boltzmannWeightΛ_J (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (σ : IsingModel.Config ↑(Λ : Finset V)) :
    HasDerivAt
      (fun J' => IsingModel.boltzmannWeight (inducedGraph G Λ)
        (⟨J', h, β⟩ : IsingParams ℝ) σ)
      (β * (∑ e ∈ (inducedGraph G Λ).edgeFinset,
              IsingModel.edgeSpin (K := ℝ) σ e) *
         IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) J :=
  IsingModel.hasDerivAt_boltzmannWeight_J _ J h β σ

omit [DecidableEq V] in
/-- **HasDerivAt for ambient-induced Boltzmann weight in h** at a
single configuration. -/
theorem hasDerivAt_boltzmannWeightΛ_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (σ : IsingModel.Config ↑(Λ : Finset V)) :
    HasDerivAt
      (fun h' => IsingModel.boltzmannWeight (inducedGraph G Λ)
        (⟨J, h', β⟩ : IsingParams ℝ) σ)
      (β * IsingModel.totalMagnetization σ *
         IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) h :=
  IsingModel.hasDerivAt_boltzmannWeight_field _ J h β σ

/-- **HasDerivAt for `correlationΛ` in β at h = 0** with explicit
covariance derivative. -/
theorem hasDerivAt_correlationΛ_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) :
    HasDerivAt (fun β' => correlationΛ G Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) A)
      (J * ∑ e ∈ (inducedGraph G Λ).edgeFinset,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff A {u, v}) -
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) A *
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e)
      β := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.hasDerivAt_correlation_beta _ J β A

/-- **HasDerivAt for `correlationΛ` in β at general h** with explicit
covariance derivative. -/
theorem hasDerivAt_correlationΛ_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    HasDerivAt (fun β' => correlationΛ G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) A)
      (J * ∑ e ∈ (inducedGraph G Λ).edgeFinset,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff A {u, v}) -
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) A *
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e
       + h * ∑ i : ↑(Λ : Finset V),
          (IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff A {i}) -
           IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) A *
           IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {i}))
      β := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.hasDerivAt_correlation_beta_general_h _ J h β A

/-- **HasDerivAt for `correlationΛ` in J** with explicit covariance
derivative. -/
theorem hasDerivAt_correlationΛ_J (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    HasDerivAt (fun J' => correlationΛ G Λ
        (⟨J', h, β⟩ : IsingParams ℝ) A)
      (β * ∑ e ∈ (inducedGraph G Λ).edgeFinset,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff A {u, v}) -
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) A *
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e)
      J := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.hasDerivAt_correlation_J _ J h β A

/-- **HasDerivAt for `correlationΛ` in h** with explicit covariance
derivative. -/
theorem hasDerivAt_correlationΛ_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    HasDerivAt (fun h' => correlationΛ G Λ
        (⟨J, h', β⟩ : IsingParams ℝ) A)
      (β * (IsingModel.gibbsExpectation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ)
              (fun σ => IsingModel.spinProduct A σ *
                          IsingModel.totalMagnetization σ) -
            IsingModel.correlation (inducedGraph G Λ)
                (⟨J, h, β⟩ : IsingParams ℝ) A *
            IsingModel.gibbsExpectation (inducedGraph G Λ)
                (⟨J, h, β⟩ : IsingParams ℝ)
                IsingModel.totalMagnetization)) h := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.hasDerivAt_correlation_field _ J h β A


/-- **magnetizationΛ HasDerivAt β at general h** with explicit
derivative. -/
theorem magnetizationΛ_hasDerivAt_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun β' => magnetizationΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i)
      (J * ∑ e ∈ (inducedGraph G Λ).edgeFinset,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff {i} {u, v}) -
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {i} *
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e
       + h * ∑ j : ↑Λ,
          (IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff {i} {j}) -
           IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {i} *
           IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {j}))
      β := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_hasDerivAt_beta_general_h _ J h β _

/-- **magnetizationΛ HasDerivAt h** with explicit covariance derivative
on the induced graph. -/
theorem magnetizationΛ_hasDerivAt_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun h' => magnetizationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i)
      (β * (IsingModel.gibbsExpectation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ)
              (fun σ => IsingModel.spinProduct {i} σ *
                          IsingModel.totalMagnetization σ) -
            IsingModel.correlation (inducedGraph G Λ)
                (⟨J, h, β⟩ : IsingParams ℝ) {i} *
            IsingModel.gibbsExpectation (inducedGraph G Λ)
                (⟨J, h, β⟩ : IsingParams ℝ)
                IsingModel.totalMagnetization)) h := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_hasDerivAt_field _ J h β _

/-- **magnetizationΛ HasDerivAt β at h = 0** with explicit derivative
as sum over induced-graph edges. -/
theorem magnetizationΛ_hasDerivAt_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun β' => magnetizationΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i)
      (J * ∑ e ∈ (inducedGraph G Λ).edgeFinset,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff {i} {u, v}) -
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) {i} *
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e)
      β := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_hasDerivAt_beta _ J β _

/-- **susceptibilityΛ HasDerivAt h** with explicit derivative
as sum of `truncated2` h-derivatives over induced-graph sites. -/
theorem susceptibilityΛ_hasDerivAt_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun h' => susceptibilityΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i)
      (∑ j : ↑Λ, deriv (fun h' =>
        IsingModel.truncated2 (inducedGraph G Λ)
          (⟨J, h', β⟩ : IsingParams ℝ) i j) h) h := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_hasDerivAt_field _ J h β _

end Ambient
end IsingModel
