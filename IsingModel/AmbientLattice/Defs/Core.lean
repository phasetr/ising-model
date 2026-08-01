import IsingModel.Basic
import IsingModel.GibbsMeasure
import IsingModel.FreeEnergy.Basic
import IsingModel.FreeEnergy.ParameterMonotonicity
import IsingModel.FreeEnergy.SpecialValues
import IsingModel.Conditioning.Bounds

/-!
# Ambient lattice core finite-volume definitions

Core finite-volume definitions and basic partition-function wrappers for the
ambient lattice framework.
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

end Ambient

end IsingModel
