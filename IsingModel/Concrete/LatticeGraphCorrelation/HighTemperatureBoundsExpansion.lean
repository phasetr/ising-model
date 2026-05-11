import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds

/-!
# Concrete high-temperature partition-function and free-energy expansion wrappers

Narrow child module for the §18.3-§18.4 high-temperature partition-function
expansion, free-energy expansion, sandwich, and bound wrappers on
`latticeGraph d` at `h = 0`. The theorem names are the same as the former
declarations in `HighTemperatureBounds`, but callers can now import this
child module directly.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ-level partition function high-temperature expansion at `h = 0`**:
`Z_Λ(⟨J, 0, β⟩) = (cosh βJ)^|E_Λ| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j)`.
ℤ^d wrapper of `partitionFunctionΛ_high_temp_expansion_h_zero`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) =
      Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
      ∑ σ : Config ↑Λ,
        ∏ e ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
          (1 + Real.tanh (β * J) * edgeSpin σ e) :=
  partitionFunctionΛ_high_temp_expansion_h_zero
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d along-exhaustion partition function high-temperature expansion at `h = 0`**:
`Z_n(⟨J, 0, β⟩) = (cosh βJ)^|E_n| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j)`
at every stage `n`. ℤ^d wrapper of
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n =
      Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card *
      ∑ σ : Config ↑(Λ.volume n),
        ∏ e ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
          (1 + Real.tanh (β * J) * edgeSpin σ e) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d FV (3.45) at `J = 0` consistency check**:
`Z_Λ(⟨0, 0, β⟩) = 2^|Λ|`. ℤ^d wrapper of
`partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed_at_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero
    (IsingModel.latticeGraph d) Λ β

/-- **ℤ^d FV (3.45) at `β = 0` consistency check**:
`Z_Λ(⟨J, 0, 0⟩) = 2^|Λ|`. ℤ^d wrapper. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed_at_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero
    (IsingModel.latticeGraph d) Λ J

/-- **ℤ^d FV (3.46) at `A = ∅` consistency check**:
under `0 ≤ β·J`,
`correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ ∅ = 1`.
ℤ^d wrapper of `correlationΛ_high_temp_h_zero_at_empty_A`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_empty_A
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) (∅ : Finset ↑Λ) = 1 :=
  correlationΛ_high_temp_h_zero_at_empty_A
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ-level partition function high-temperature expansion (general h)**:
`Z_Λ(p) = (cosh βJ)^|E_Λ| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j) · exp(βh ∑_i σ_i)`.
ℤ^d wrapper of `partitionFunctionΛ_high_temp_expansion`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ p =
      Real.cosh (p.β * p.J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
      ∑ σ : Config ↑Λ,
        (∏ e ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
          (1 + Real.tanh (p.β * p.J) * edgeSpin σ e)) *
        Real.exp (p.β * p.h * ∑ i : ↑Λ, Spin.sign ℝ (σ i)) :=
  partitionFunctionΛ_high_temp_expansion (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d along-exhaustion partition function high-temperature expansion (general h)**:
at every stage `n`,
`Z_n(p) = (cosh βJ)^|E_n| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j) · exp(βh ∑ σ_i)`.
ℤ^d wrapper of `partitionFunctionAlongExhaustion_high_temp_expansion`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (p : IsingParams ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n =
      Real.cosh (p.β * p.J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card *
      ∑ σ : Config ↑(Λ.volume n),
        (∏ e ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
          (1 + Real.tanh (p.β * p.J) * edgeSpin σ e)) *
        Real.exp (p.β * p.h *
                  ∑ i : ↑(Λ.volume n), Spin.sign ℝ (σ i)) :=
  partitionFunctionAlongExhaustion_high_temp_expansion
    (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d high-temperature partition function closed form (FV §3.7.3 eq. (3.45))**:
on the ℤ^d induced subgraph at zero external field,
`Z_Λ(⟨J, 0, β⟩) = 2^|Λ| · (cosh(β J))^|E_Λ| · ∑_{X ⊆ E_Λ, even-degree} tanh(β J)^|X|`.
ℤ^d wrapper of `partitionFunctionΛ_high_temp_expansion_h_zero_closed`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        ∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d general-h subset expansion (GJ §18.3)**:
on the ℤ^d induced subgraph,
`Z_Λ(p) = (cosh βJ)^|E_Λ| · ∑_X tanh(βJ)^|X| · ∑_σ (∏_{e ∈ X} σ_iσ_j) exp(βh ∑ σ_i)`.
ℤ^d wrapper of `partitionFunctionΛ_high_temp_expansion_subset_form`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_subset_form
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ p =
      Real.cosh (p.β * p.J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
      ∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ↑Λ,
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h * ∑ i : ↑Λ, Spin.sign ℝ (σ i)) :=
  partitionFunctionΛ_high_temp_expansion_subset_form
    (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d high-temperature correlation closed form (FV §3.7.3 eq. (3.46))**:
on the ℤ^d induced subgraph at zero external field,
`⟨σ_A⟩^Λ_{β,0} = (∑_{X : ∂X=A} tanh^|X|) / (∑_{X : ∂X=∅} tanh^|X|)`.
ℤ^d wrapper of `correlationΛ_high_temp_expansion_h_zero_closed`. -/
theorem correlationΛ_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (A : Finset ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) A
      = (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑Λ,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) /
        (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) :=
  correlationΛ_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β A

/-- **ℤ^d log Z high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J`,
`log Z_Λ(⟨J, 0, β⟩) = |Λ| · log 2 + |E_Λ| · log(cosh βJ) + log(∑_{X even} tanh^|X|)`.
ℤ^d wrapper of `log_partitionFunctionΛ_high_temp_expansion_h_zero_closed`. -/
theorem log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ↑Λ) =>
                  ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d along-exhaustion log Z high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J`, at every stage `n`,
`log Z_n(⟨J, 0, β⟩) = |Λ_n| · log 2 + |E_n| · log(cosh βJ) + log(∑ tanh^|X|)`.
ℤ^d wrapper of `log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n)).edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
                  ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d Z high-temperature upper bound (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J`,
`Z_Λ(⟨J, 0, β⟩) ≤ 2^(|Λ|+|E_Λ|) · cosh(βJ)^|E_Λ|`. ℤ^d wrapper of
`partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_upper_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ (Λ.card +
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) *
        Real.cosh (β * J) ^
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d along-exhaustion Z high-temperature upper bound**:
under `0 ≤ β·J`, at every stage `n`,
`Z_n ≤ 2^(|Λ_n|+|E_n|) · cosh(βJ)^|E_n|`. ℤ^d wrapper. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_upper_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ ((Λ.volume n).card +
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) *
        Real.cosh (β * J) ^
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d Z bounds consistency**: lower ≤ upper. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_h_zero_lower_le_upper
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ (2 : ℝ) ^ (Λ.card +
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) *
        Real.cosh (β * J) ^
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  partitionFunctionΛ_high_temp_h_zero_lower_le_upper
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d freeEnergy bounds consistency**: lower ≤ upper. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_lower_le_upper
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card * Real.log (Real.cosh (β * J))
      ≤ Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
            Λ.card * Real.log (2 * Real.cosh (β * J)) :=
  freeEnergyΛ_high_temp_h_zero_lower_le_upper
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d high-temperature partition function lower bound (GJ §18.3 / FV (3.45))**:
under `0 ≤ β * J`,
`Z_Λ(⟨J, 0, β⟩) ≥ 2^|Λ| · (cosh(βJ))^|E_Λ|`.
ℤ^d wrapper of `partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_lower_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d freeEnergy high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 < |Λ|` and `0 ≤ β·J`,
`f_Λ = log 2 + (|E_Λ|/|Λ|) · log(cosh βJ) + log(∑_{X even} tanh^|X|) / |Λ|`.
ℤ^d wrapper of `freeEnergyΛ_high_temp_expansion_h_zero_closed`. -/
theorem freeEnergyΛ_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      = Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
            Λ.card * Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ↑Λ) =>
                  ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) / Λ.card :=
  freeEnergyΛ_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d along-exhaustion freeEnergy high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J` and `0 < |Λ_n|`, at every stage `n`,
`f_n = log 2 + (|E_n|/|Λ_n|) · log(cosh βJ) + log(∑ tanh^|X|) / |Λ_n|`.
ℤ^d wrapper of `freeEnergyAlongExhaustion_high_temp_expansion_h_zero_closed`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
            (Λ.volume n).card * Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n)).edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
                  ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) / (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d freeEnergy high-temperature upper bound (FV (3.45))**:
under `0 < |Λ|` and `0 ≤ β·J`,
`f_Λ ≤ log 2 + (|E_Λ|/|Λ|) · log(2 · cosh βJ)`. ℤ^d wrapper. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_upper_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
            Λ.card * Real.log (2 * Real.cosh (β * J)) :=
  freeEnergyΛ_high_temp_h_zero_upper_bound
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d along-exhaustion freeEnergy high-temperature upper bound (FV (3.45))**:
under `0 ≤ β·J` and `0 < |Λ_n|`, at every stage `n`,
`f_n ≤ log 2 + (|E_n|/|Λ_n|) · log(2 · cosh βJ)`. ℤ^d wrapper. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_upper_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
            (Λ.volume n).card * Real.log (2 * Real.cosh (β * J)) :=
  freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d free-energy lower bound from FV (3.45)** at zero external field:
under `0 < |Λ|` and `0 ≤ β * J`,
`f_Λ(⟨J, 0, β⟩) ≥ log 2 + (|E_Λ|/|Λ|) · log(cosh(β·J))`.
ℤ^d wrapper of `freeEnergyΛ_high_temp_h_zero_lower_bound`. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_lower_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_high_temp_h_zero_lower_bound
    (IsingModel.latticeGraph d) Λ J β hβJ hne

end Ambient

end IsingModel
