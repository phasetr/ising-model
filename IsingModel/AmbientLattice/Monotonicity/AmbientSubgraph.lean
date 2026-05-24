import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion

/-!
# Monotonicity for the ambient lattice Ising model

Two monotonicity directions for the finite-volume Ising model on `Λ`:

1. **Ambient-subgraph monotonicity**: if `G₁ ≤ G₂` then
   `partitionFunctionΛ G₁ Λ p ≤ partitionFunctionΛ G₂ Λ p` (and similarly
   for correlations and free energy).

2. **Volume-direction monotonicity**: if `Λ₁ ⊆ Λ₂` then
   `correlationΛ G Λ₁ p A ≤ correlationΛ G Λ₂ p A` (ferromagnetic).
   This is the core monotone convergence result underlying the
   thermodynamic limit.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.2–4.6.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Monotonicity in the ambient subgraph direction

For a fixed finite volume `Λ : Finset V`, if `G₁ ≤ G₂` as
`SimpleGraph V`, then the induced subgraphs satisfy
`G₁.induce Λ ≤ G₂.induce Λ` as `SimpleGraph (↑Λ)`.  Applying the
existing `partitionFunction_monotone_subgraph`,
`correlation_monotone_subgraph`, and `freeEnergy_monotone_subgraph`
on the finite `Fintype (↑Λ)` then gives monotonicity on `Λ` in the
ambient subgraph direction. -/

omit [DecidableEq V] in
/-- The induced subgraph is monotone in the ambient graph. -/
theorem inducedGraph_mono {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂)
    (Λ : Finset V) : inducedGraph G₁ Λ ≤ inducedGraph G₂ Λ := by
  intro u v hadj
  exact h hadj

/-- **Partition function ambient-subgraph monotonicity**:
for `G₁ ≤ G₂` (ambient) and ferromagnetic `p`,
`Z_{G₁,Λ} ≤ Z_{G₂,Λ}` on any finite volume `Λ`. -/
theorem partitionFunctionΛ_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Finset V)
    [Fintype (inducedGraph G₁ Λ).edgeSet]
    [Fintype (inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunctionΛ G₁ Λ p ≤ partitionFunctionΛ G₂ Λ p :=
  IsingModel.partitionFunction_monotone_subgraph (inducedGraph_mono h Λ) p hf

/-- **Correlation ambient-subgraph monotonicity**:
for `G₁ ≤ G₂` (ambient) and ferromagnetic `p`,
`⟨σ^A⟩_{G₁,Λ} ≤ ⟨σ^A⟩_{G₂,Λ}` on any finite volume `Λ` and
`A : Finset (↑Λ)`. -/
theorem correlationΛ_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Finset V)
    [Fintype (inducedGraph G₁ Λ).edgeSet]
    [Fintype (inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ G₁ Λ p A ≤ correlationΛ G₂ Λ p A :=
  IsingModel.correlation_monotone_subgraph (inducedGraph_mono h Λ) p hf A

/-- **Magnetization ambient-subgraph monotonicity** on `Λ`:
for `G₁ ≤ G₂` and ferromagnetic `p`, `M_{Λ,G₁}(i) ≤ M_{Λ,G₂}(i)` at any
site `i : ↑Λ`. Specialization of `correlationΛ_monotone_ambient_subgraph`
at `A = {i}`. -/
theorem magnetizationΛ_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Finset V)
    [Fintype (inducedGraph G₁ Λ).edgeSet]
    [Fintype (inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ↑Λ) :
    magnetizationΛ G₁ Λ p i ≤ magnetizationΛ G₂ Λ p i :=
  correlationΛ_monotone_ambient_subgraph h Λ p hf {i}

/-- **Free energy ambient-subgraph monotonicity**:
for `G₁ ≤ G₂` (ambient) and ferromagnetic `p`,
`f_{G₁,Λ} ≤ f_{G₂,Λ}` on any finite volume `Λ`. -/
theorem freeEnergyΛ_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Finset V)
    [Fintype (inducedGraph G₁ Λ).edgeSet]
    [Fintype (inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyΛ G₁ Λ p ≤ freeEnergyΛ G₂ Λ p :=
  IsingModel.freeEnergy_monotone_subgraph (inducedGraph_mono h Λ) p hf

/-- **Subgraph monotonicity of `freeEnergyAlongExhaustion`**: for
`G₁ ≤ G₂` and ferromagnetic parameters, the free energy along the
exhaustion is pointwise monotone in the ambient subgraph. Direct
specialization of `freeEnergyΛ_monotone_ambient_subgraph` at each
`Λ.volume n`. -/
theorem freeEnergyAlongExhaustion_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    freeEnergyAlongExhaustion G₁ Λ p n
      ≤ freeEnergyAlongExhaustion G₂ Λ p n :=
  freeEnergyΛ_monotone_ambient_subgraph h (Λ.volume n) p hf


/-- **Subgraph monotonicity of `partitionFunctionAlongExhaustion`**:
for `G₁ ≤ G₂` and ferromagnetic parameters, the partition function
along the exhaustion is pointwise monotone in the ambient subgraph.
Direct specialization of `partitionFunctionΛ_monotone_ambient_subgraph`
at each `Λ.volume n`. -/
theorem partitionFunctionAlongExhaustion_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    partitionFunctionAlongExhaustion G₁ Λ p n
      ≤ partitionFunctionAlongExhaustion G₂ Λ p n :=
  partitionFunctionΛ_monotone_ambient_subgraph h (Λ.volume n) p hf

/-- **Log-bridge identity**: the `freeEnergyAlongExhaustion` sequence
is the log of the `partitionFunctionAlongExhaustion` sequence divided
by the cardinality of the volume.  Direct unfolding of the underlying
`IsingModel.freeEnergy` definition (log-partition function per site). -/
theorem freeEnergyAlongExhaustion_eq_log_div_card
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ p n =
      (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹ *
        Real.log (partitionFunctionAlongExhaustion G Λ p n) := by
  simp only [freeEnergyAlongExhaustion_apply,
    partitionFunctionAlongExhaustion_apply, freeEnergyΛ,
    partitionFunctionΛ, IsingModel.freeEnergy]

/-- **J-direction monotonicity of `freeEnergyAlongExhaustion`**: for
fixed `h ≥ 0`, `β > 0`, and any `n`, the free energy along the
exhaustion is monotone in `J ∈ Set.Ici 0`.  Direct specialization of
`IsingModel.freeEnergy_monotone_J`. -/
theorem freeEnergyAlongExhaustion_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun J : ℝ => freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n)
      (Set.Ici 0) :=
  IsingModel.freeEnergy_monotone_J (inducedGraph G (Λ.volume n)) h β hh hβ

/-- **h-direction monotonicity of `freeEnergyAlongExhaustion`**: for
fixed `J ≥ 0`, `β > 0`, and any `n`, the free energy along the
exhaustion is monotone in `h ∈ Set.Ici 0`. -/
theorem freeEnergyAlongExhaustion_monotone_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun h : ℝ => freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n)
      (Set.Ici 0) :=
  IsingModel.freeEnergy_monotone_h (inducedGraph G (Λ.volume n)) J β hJ hβ

/-- **β-direction monotonicity of `freeEnergyAlongExhaustion`**: for
fixed `J ≥ 0`, `h ≥ 0`, and any `n`, the free energy along the
exhaustion is monotone in `β ∈ Set.Ioi 0`. -/
theorem freeEnergyAlongExhaustion_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    MonotoneOn
      (fun β : ℝ => freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n)
      (Set.Ioi 0) :=
  IsingModel.freeEnergy_monotone_beta (inducedGraph G (Λ.volume n)) J hJ h hh

/-- **J-direction monotonicity of `partitionFunctionAlongExhaustion`**
(pointwise form matching finite-volume `partitionFunction_monotone_J`). -/
theorem partitionFunctionAlongExhaustion_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ ⟨J₁, h, β⟩ n
      ≤ partitionFunctionAlongExhaustion G Λ ⟨J₂, h, β⟩ n :=
  IsingModel.partitionFunction_monotone_J
    (inducedGraph G (Λ.volume n)) h β hh hβ J₁ J₂ hJ₁ hJ

/-- **h-direction monotonicity of `partitionFunctionAlongExhaustion`**. -/
theorem partitionFunctionAlongExhaustion_monotone_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ ⟨J, h₁, β⟩ n
      ≤ partitionFunctionAlongExhaustion G Λ ⟨J, h₂, β⟩ n :=
  IsingModel.partitionFunction_monotone_h
    (inducedGraph G (Λ.volume n)) J β hJ hβ h₁ h₂ hh₁ hh

/-- **β-direction monotonicity of `partitionFunctionAlongExhaustion`**. -/
theorem partitionFunctionAlongExhaustion_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ ⟨J, h, β₁⟩ n
      ≤ partitionFunctionAlongExhaustion G Λ ⟨J, h, β₂⟩ n :=
  IsingModel.partitionFunction_monotone_beta
    (inducedGraph G (Λ.volume n)) J h hJ hh β₁ β₂ hβ₁ hβ


end Ambient
end IsingModel
