import IsingModel.AmbientLattice.Defs.HighTempPartition.ClosedForms

/-!
# Λ-restricted high-temperature bounds on the partition function and the free energy

Statements about `partitionFunctionΛ`, about its logarithm and about `freeEnergyΛ`, for an
arbitrary `G : SimpleGraph V` and an arbitrary finite volume `Λ : Finset V`, always at zero
external field: the one parameter record occurring here is `⟨J, 0, β⟩`, so only the coupling
`J` and the inverse temperature `β` vary. What the bounds are written in is `Λ.card`
together with the number of edges of `inducedGraph G Λ`, the subgraph of `G` that `Λ`
induces.

Under `0 ≤ β * J` the logarithm of the partition function is given exactly. It is
`Λ.card * log 2`, plus that edge count times `log (cosh (β * J))`, plus the logarithm of a
sum taken over those subsets of the induced graph's edges in which every site of `Λ` meets
an even number of the chosen edges, each subset contributing `tanh (β * J)` raised to its
own number of edges; the free energy is the same expression divided by `Λ.card`. This is
the logarithmic form of the high-temperature representation of the partition function.

Under that same hypothesis the partition function is at least `2 ^ Λ.card` times
`cosh (β * J)` raised to the edge count; it is at most `2 ^ (Λ.card + edge count)` times
that same power, and also at most `2 ^ Λ.card` times `exp (β * J * edge count)`. Its
logarithm is at least `Λ.card * log 2` plus the edge count times `log (cosh (β * J))`, and
at most `Λ.card * log 2` plus `β * J` times the edge count. The free energy is at least
`log 2` plus the edge count over `Λ.card` times `log (cosh (β * J))`; it is at most the same
expression with `log (2 * cosh (β * J))` in place of `log (cosh (β * J))`, and also at most
`log 2` plus `β * J` times the edge count over `Λ.card`. For each of the three quantities a
lower and an upper bound are additionally conjoined into a single statement.

Some statements compare bounding expressions with one another rather than bounding a
partition function or a free energy, and their conclusions mention neither
`partitionFunctionΛ` nor `freeEnergyΛ`: the partition-function bounding expressions are
compared for arbitrary real `J` and `β` under no hypothesis at all, the free-energy ones
under `0 ≤ β * J`. Those comparisons are also the only statements here that do not take
`[DecidableEq V]`.

`0 < Λ.card` is assumed by exactly those statements whose conclusion mentions
`freeEnergyΛ`. Some statements assume `0 ≤ J` together with `0 < β` in place of
`0 ≤ β * J`. Every statement takes `[Fintype (inducedGraph G Λ).edgeSet]`, which
`partitionFunctionΛ`, `freeEnergyΛ` and the edge count each require.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

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


end Ambient

end IsingModel
