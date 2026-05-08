import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.SpecialCases.HighTemperature
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticity
import IsingModel.AmbientLattice.SpecialCases.JointRegularity
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticity
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularity
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticity
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBounds
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity
import IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticity
import IsingModel.AmbientLattice.Analyticity

/-!
# Special-case closed forms, h-symmetry, and critical exponents

Uniform upper bounds (BoundedEdgeDensity), closed forms for special
parameter slices (β=0, J=h=0, J=0), h-symmetry / |h|-monotonicity
along an exhaustion, and the critical exponent bounds η≥0, ζ≥0
at infinite volume (GJ §17.7 Thm 17.7.1).

## References

* Glimm–Jaffe, *Quantum Physics*, §4.6, §17.7.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## β = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion β=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨J, h, 0⟩ n = 2 ^ |Λ.volume n|`
for any `J, h` and any ambient graph `G, Λ`.

Specialization of `IsingModel.partitionFunction_beta_zero` (every
Boltzmann weight collapses to `exp 0 = 1`) with
`card_config_eq_two_pow` and `Fintype.card_coe`. -/
theorem partitionFunctionAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨J, h, 0⟩ : IsingParams ℝ) = (2 : ℝ) ^ (Λ.volume n).card
  rw [IsingModel.partitionFunction_beta_zero, IsingModel.card_config_eq_two_pow,
      Fintype.card_coe]
  push_cast
  rfl

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨J, h, 0⟩ n)
= |Λ.volume n| · log 2`. Follows from
`partitionFunctionAlongExhaustion_beta_zero` via `Real.log_pow`. -/
theorem log_partitionFunctionAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 := by
  rw [partitionFunctionAlongExhaustion_beta_zero, Real.log_pow]

/-! ## J = h = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion J=h=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n = 2 ^ |Λ.volume n|`
for any ambient graph `G, Λ` and any `β`.

Specialization of `IsingModel.partitionFunction_zero_params`
(`Z_G ⟨0,0,β⟩ = Fintype.card (Config ι)`) with `card_config_eq_two_pow`
(`|Config ι| = 2^|ι|`) and `Fintype.card_coe` (`|↑Λ| = |Λ|`). -/
theorem partitionFunctionAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨0, 0, β⟩ : IsingParams ℝ) = (2 : ℝ) ^ (Λ.volume n).card
  rw [IsingModel.partitionFunction_zero_params, IsingModel.card_config_eq_two_pow,
      Fintype.card_coe]
  push_cast
  rfl

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n)
= |Λ.volume n| · log 2`. Follows from
`partitionFunctionAlongExhaustion_zero_params` via `Real.log_pow`. -/
theorem log_partitionFunctionAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 := by
  rw [partitionFunctionAlongExhaustion_zero_params, Real.log_pow]

/-! ## J = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion J=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n = (2·cosh(β·h))^|Λ.volume n|`
for any `h, β` and any ambient graph `G, Λ`.

Specialization of `IsingModel.partitionFunction_J_zero`
(`Z_G ⟨0, h, β⟩ = (2·cosh(β·h))^|ι|`, graph-independent) with
`Fintype.card_coe` (`|↑Λ| = |Λ|`). -/
theorem partitionFunctionAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = (2 * Real.cosh (β * h)) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) = _
  rw [IsingModel.partitionFunction_J_zero, Fintype.card_coe]

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n)
= |Λ.volume n| · log (2·cosh(β·h))`. Follows from
`partitionFunctionAlongExhaustion_J_zero` via `Real.log_pow`
(`2·cosh(β·h) > 0`). -/
theorem log_partitionFunctionAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log (2 * Real.cosh (β * h)) := by
  rw [partitionFunctionAlongExhaustion_J_zero, Real.log_pow]

/-! ## h-symmetry / `|h|`-monotonicity along exhaustion

Specializations of `IsingModel.freeEnergy_neg_h`, `freeEnergy_eq_abs_h`,
and `freeEnergy_monotone_abs_h` (PRs #126–#127) to each stage of the
exhaustion, via the `change` + definitional-unfolding pattern already
used in this file. -/

/-- **Along-exhaustion partition-function h-evenness**:
`partitionFunctionAlongExhaustion G Λ ⟨J, -h, β⟩ n =
partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n`. Per-stage lift of
`IsingModel.partitionFunction_neg_h` via the flip involution. -/
theorem partitionFunctionAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_neg_h G (Λ.volume n) J h β

/-- **Along-exhaustion partition-function `|h|`-rewrite**:
`partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n =
partitionFunctionAlongExhaustion G Λ ⟨J, |h|, β⟩ n`. Per-stage lift of
`partitionFunctionΛ_eq_abs_h`. -/
theorem partitionFunctionAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_eq_abs_h G (Λ.volume n) J h β

/-- **Along-exhaustion ferromagnetic `|h|`-monotonicity of partition
function**: for `J ≥ 0`, `β > 0`, `|h₁| ≤ |h₂|`,
`partitionFunctionAlongExhaustion G Λ ⟨J, h₁, β⟩ n ≤
partitionFunctionAlongExhaustion G Λ ⟨J, h₂, β⟩ n`. Per-stage lift of
`partitionFunctionΛ_monotone_abs_h`. -/
theorem partitionFunctionAlongExhaustion_monotone_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_monotone_abs_h G (Λ.volume n) J β hJ hβ hh

/-! ### §18.6 mayerPartialSum regularity along-ex wraps -/

/-- **Along-ex: `mayerPartialSum` is `Continuous`**. -/
theorem mayerPartialSumAlongExhaustion_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Continuous (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) :=
  mayerPartialSum_Λ_continuous G (Λ.volume n) N

/-- **Along-ex: `mayerPartialSum` is `Differentiable ℝ`**. -/
theorem mayerPartialSumAlongExhaustion_differentiable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) :=
  mayerPartialSum_Λ_differentiable G (Λ.volume n) N

/-- **Along-ex: `mayerPartialSum` is `ContinuousOn`**. -/
theorem mayerPartialSumAlongExhaustion_continuousOn
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) s :=
  mayerPartialSum_Λ_continuousOn G (Λ.volume n) N s

/-- **Along-ex: `mayerPartialSum` is `DifferentiableOn ℝ`**. -/
theorem mayerPartialSumAlongExhaustion_differentiableOn
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    DifferentiableOn ℝ (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) s :=
  mayerPartialSum_Λ_differentiableOn G (Λ.volume n) N s

/-! ### §18.6 mayerExpansionTerm regularity along-ex wraps -/

/-- **Along-ex: `mayerExpansionTerm` is `Continuous`**. -/
theorem mayerExpansionTermAlongExhaustion_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    Continuous (fun t : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k t) :=
  mayerExpansionTerm_Λ_continuous G (Λ.volume n) k

/-- **Along-ex: `mayerExpansionTerm` is `Differentiable ℝ`**. -/
theorem mayerExpansionTermAlongExhaustion_differentiable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k t) :=
  mayerExpansionTerm_Λ_differentiable G (Λ.volume n) k

/-! ### §18.6 mayerPartialSum tanh β/J along-ex wraps -/

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerPartialSumAlongExhaustion_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β' * J))) :=
  mayerPartialSum_Λ_tanh_continuous_beta G (Λ.volume n) N J

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerPartialSumAlongExhaustion_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β * J'))) :=
  mayerPartialSum_Λ_tanh_continuous_J G (Λ.volume n) N β

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem mayerPartialSumAlongExhaustion_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β' * J))) :=
  mayerPartialSum_Λ_tanh_differentiable_beta G (Λ.volume n) N J

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerPartialSumAlongExhaustion_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β * J'))) :=
  mayerPartialSum_Λ_tanh_differentiable_J G (Λ.volume n) N β

/-! ### §18.5 mayerExpansionTerm tanh β/J along-ex wraps -/

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β' * J))) :=
  mayerExpansionTerm_Λ_tanh_continuous_beta G (Λ.volume n) k J

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β * J'))) :=
  mayerExpansionTerm_Λ_tanh_continuous_J G (Λ.volume n) k β

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β' * J))) :=
  mayerExpansionTerm_Λ_tanh_differentiable_beta G (Λ.volume n) k J

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β * J'))) :=
  mayerExpansionTerm_Λ_tanh_differentiable_J G (Λ.volume n) k β

/-! ### §18.6 vdPolymerFamilies_sum regularity in t along-ex wraps -/

/-- **Along-ex: `vdPolymerFamilies_sum` is `Continuous` in `t`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_continuous G (Λ.volume n)

/-- **Along-ex: `vdPolymerFamilies_sum` is `Differentiable ℝ`
in `t`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_differentiable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_differentiable G (Λ.volume n)

/-- **Along-ex: `vdPolymerFamilies_sum` `HasDerivAt`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_hasDerivAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card)
      (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
          ((Q.card : ℝ) * t ^ (Q.card - 1))) t :=
  vdPolymerFamilies_sum_Λ_hasDerivAt G (Λ.volume n) t

/-! ### §18.5 vdPolymerFamilies_sum tanh β/J along-ex wraps -/

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_continuous_beta G (Λ.volume n) J

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_continuous_J G (Λ.volume n) β

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_differentiable_beta G (Λ.volume n) J

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_differentiable_J G (Λ.volume n) β

/-! ### §18.5 mayer_identity_at edge-case along-ex wraps -/

/-- **Along-ex: Mayer identity at `t = 0`**. -/
theorem mayer_identity_at_zero_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
              ∏ P ∈ Γ, (0 : ℝ) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N 0 :=
  mayer_identity_at_zero_Λ G (Λ.volume n) N

/-- **Along-ex: Mayer identity at `β·J = 0`**. -/
theorem mayer_identity_at_betaJ_zero_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
              ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  mayer_identity_at_betaJ_zero_Λ G (Λ.volume n) hβJ N

/-- **Along-ex: Mayer identity at `β = 0`**. -/
theorem mayer_identity_at_beta_zero_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
              ∏ P ∈ Γ, Real.tanh ((0 : ℝ) * J) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * J)) :=
  mayer_identity_at_beta_zero_Λ G (Λ.volume n) J N

/-- **Along-ex: Mayer identity at `J = 0`**. -/
theorem mayer_identity_at_J_zero_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
              ∏ P ∈ Γ, Real.tanh (β * (0 : ℝ)) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * (0 : ℝ))) :=
  mayer_identity_at_J_zero_Λ G (Λ.volume n) β N

/-! ### §18.5 polymerFreeEnergy_eq_mayerPartialSum_at edge-case along-ex wraps -/

/-- **Along-ex: polymerFreeEnergy = mayerPartialSum at t = 0**. -/
theorem polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) 0 =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N 0 :=
  polymerFreeEnergy_Λ_eq_mayerPartialSum_at_zero G (Λ.volume n) N

/-- **Along-ex: polymerFreeEnergy = mayerPartialSum at β·J = 0**. -/
theorem polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_betaJ_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  polymerFreeEnergy_Λ_eq_mayerPartialSum_at_betaJ_zero
    G (Λ.volume n) hβJ N

/-- **Along-ex: polymerFreeEnergy = mayerPartialSum at β = 0**. -/
theorem polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * J)) :=
  polymerFreeEnergy_Λ_eq_mayerPartialSum_at_beta_zero
    G (Λ.volume n) J N

/-- **Along-ex: polymerFreeEnergy = mayerPartialSum at J = 0**. -/
theorem polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * (0 : ℝ))) :=
  polymerFreeEnergy_Λ_eq_mayerPartialSum_at_J_zero
    G (Λ.volume n) β N

/-! ### §18.5 mayer_identity polymer_free_energy variants along-ex wraps -/

/-- **Along-ex: Mayer identity at `J = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_J_zero_polymer_free_energy_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * (0 : ℝ))) :=
  mayer_identity_at_J_zero_polymer_free_energy_Λ G (Λ.volume n) β N

/-- **Along-ex: Mayer identity at `β = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_beta_zero_polymer_free_energy_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * J)) :=
  mayer_identity_at_beta_zero_polymer_free_energy_Λ G (Λ.volume n) J N

/-- **Along-ex: Mayer identity at `J = β = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_either_zero_polymer_free_energy_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n))
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) :=
  mayer_identity_at_either_zero_polymer_free_energy_Λ G (Λ.volume n) N

/-! ### §18.5 mayerPartialSum_zero ≤ polymerFreeEnergy along-ex wraps -/

/-- **Along-ex: mayerPartialSum 0 ≤ polymerFreeEnergy under `t ≥ 0`**. -/
theorem mayerPartialSum_zero_AlongExhaustion_le_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 0 t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t :=
  mayerPartialSum_zero_Λ_le_polymerFreeEnergy G (Λ.volume n) ht

/-- **Along-ex: mayerPartialSum 0 ≤ polymerFreeEnergy(tanh(β·J))**. -/
theorem mayerPartialSum_zero_AlongExhaustion_tanh_le_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) :=
  mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy G (Λ.volume n) hβJ

/-- **Along-ex: ferromagnetic mayerPartialSum 0 ≤
polymerFreeEnergy(tanh(β·J))**. -/
theorem
mayerPartialSum_zero_AlongExhaustion_tanh_le_polymerFreeEnergy_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) :=
  mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy_ferromagnetic
    G (Λ.volume n) hJ hβ

/-! ### §18.5 mayer_identity_of edge-case along-ex wraps -/

/-- **Along-ex: Mayer identity for empty-polymer induced graphs**. -/
theorem mayer_identity_of_no_polymers_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph G (Λ.volume n)) = ∅) (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N t :=
  mayer_identity_of_no_polymers_Λ G (Λ.volume n) h_no t N

/-- **Along-ex: Mayer identity for empty-polymer induced graphs
(tanh form)**. -/
theorem mayer_identity_of_no_polymers_tanh_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph G (Λ.volume n)) = ∅) (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  mayer_identity_of_no_polymers_tanh_Λ G (Λ.volume n) h_no β J N

/-- **Along-ex: Mayer identity under disjunctive trivial conditions**. -/
theorem mayer_identity_of_trivial_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) {β J : ℝ}
    (h : β * J = 0 ∨
      IsingModel.allPolymers
        (inducedGraph G (Λ.volume n)) = ∅) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  mayer_identity_of_trivial_Λ G (Λ.volume n) h N

/-- **Along-ex: Mayer identity for edgeless induced graphs**. -/
theorem mayer_identity_of_edgeFinset_empty_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N t :=
  mayer_identity_of_edgeFinset_empty_Λ G (Λ.volume n) h_empty t N

/-- **Along-ex: Mayer identity for edgeless induced graphs (tanh
form)**. -/
theorem mayer_identity_of_edgeFinset_empty_tanh_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  mayer_identity_of_edgeFinset_empty_tanh_Λ
    G (Λ.volume n) h_empty β J N

/-! ### §18.5 basic identities at_zero / at_one along-ex wraps -/

/-- **Along-ex: vdPolymerFamilies_sum at t = 0 = 1**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 :=
  vdPolymerFamilies_sum_Λ_at_zero G (Λ.volume n)

/-- **Along-ex: vdPolymerFamilies_sum at t = 1 = #vdCompatPoly**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_at_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph G (Λ.volume n))).card :=
  vdPolymerFamilies_sum_Λ_at_one G (Λ.volume n)

/-- **Along-ex: mayerPartialSum at N = 0 = 0**. -/
theorem mayerPartialSumAlongExhaustion_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 0 t = 0 :=
  mayerPartialSum_Λ_zero G (Λ.volume n) t

/-- **Along-ex: mayerPartialSum at N = 1 = ∑_P t^|P|**. -/
theorem mayerPartialSumAlongExhaustion_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)), t ^ P.card :=
  mayerPartialSum_Λ_one G (Λ.volume n) t

/-- **Along-ex: mayerPartialSum at t = 0 = 0**. -/
theorem mayerPartialSumAlongExhaustion_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N 0 = 0 :=
  mayerPartialSum_Λ_at_zero G (Λ.volume n) N

/-- **Along-ex: mayerExpansionTerm at n = 0 = 0**. -/
theorem mayerExpansionTermAlongExhaustion_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 0 t = 0 :=
  mayerExpansionTerm_Λ_zero G (Λ.volume n) t

/-- **Along-ex: mayerExpansionTerm at n = 1 = ∑_P t^|P|**. -/
theorem mayerExpansionTermAlongExhaustion_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)), t ^ P.card :=
  mayerExpansionTerm_Λ_one G (Λ.volume n) t

/-- **Along-ex: mayerExpansionTerm at t = 0 = 0**. -/
theorem mayerExpansionTermAlongExhaustion_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) k 0 = 0 :=
  mayerExpansionTerm_Λ_at_zero G (Λ.volume n) k

/-! ### §18.5 vdPolymerFamilies_sum iff characterizations along-ex wraps -/

/-- **Along-ex: vdSum = 1 ↔ ε = 0**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_eq_one_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, t ^ P.card) = 1 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 :=
  vdPolymerFamilies_sum_Λ_eq_one_iff_eps_zero G (Λ.volume n) t

/-- **Along-ex: vdSum > 1 ↔ ε > 0 under `0 ≤ t`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_gt_one_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_gt_one_iff_eps_pos G (Λ.volume n) ht

/-- **Along-ex: vdSum_tanh > 1 ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph G (Λ.volume n))).Nonempty :=
  vdPolymerFamilies_sum_Λ_tanh_gt_one_iff G (Λ.volume n) hβJ

/-- **Along-ex: vdSum_tanh = 1 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_eq_one_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph G (Λ.volume n)) = ∅ :=
  vdPolymerFamilies_sum_Λ_tanh_eq_one_iff G (Λ.volume n) hβJ

/-! ### §18.5 vdPolymerFamilies_sum bound family along-ex wraps -/

/-- **Along-ex: vdSum_tanh ≤ 2^|E|**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_le_two_pow
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_le_two_pow G (Λ.volume n) hβJ

/-- **Along-ex: vdSum_tanh ≤ (1+tanh)^|E|**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_le_one_plus_tanh_pow
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_le_one_plus_tanh_pow G (Λ.volume n) hβJ

/-- **Along-ex: 1 ≤ vdSum_tanh**. -/
theorem one_le_vdPolymerFamilies_sumAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  one_le_vdPolymerFamilies_sum_Λ G (Λ.volume n) hβJ

/-! ### §18.5 vdPolymerFamilies_sum generic-t bounds along-ex -/

/-- **Along-ex: 1 ≤ vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_ge_one_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_ge_one_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: vdSum ≤ (1+t)^|E|** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_le_one_plus_pow_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card)
      ≤ (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_le_one_plus_pow_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: 0 < vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_pos_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 < ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_pos_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: vdSum = 1 + ε(t)** decomposition. -/
theorem vdPolymerFamilies_sumAlongExhaustion_eq_one_add
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) =
      1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_eq_one_add G (Λ.volume n) t

/-! ### §18.5 Mayer expansion edge-cases + n=2 + abs_le along-ex -/

/-- **Along-ex: mayerExpansionTerm at `n = 2`**. -/
theorem mayerExpansionTermAlongExhaustion_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 2 t =
      ∑ pq ∈ (IsingModel.allPolymers
              (inducedGraph G (Λ.volume n))) ×ˢ
              (IsingModel.allPolymers (inducedGraph G (Λ.volume n))),
        (if IsingModel.PolymersIncompatible pq.1 pq.2 then (-1/2 : ℝ)
          else 0) *
          (t ^ pq.1.card * t ^ pq.2.card) :=
  mayerExpansionTerm_Λ_two G (Λ.volume n) t

/-- **Along-ex: mayerExpansionTerm at `n = 2`, filter form**. -/
theorem mayerExpansionTermAlongExhaustion_two_filter
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 2 t =
      (-1/2 : ℝ) *
        ∑ pq ∈ ((IsingModel.allPolymers
                  (inducedGraph G (Λ.volume n))) ×ˢ
                (IsingModel.allPolymers
                  (inducedGraph G (Λ.volume n)))).filter
            (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
          (t ^ pq.1.card * t ^ pq.2.card) :=
  mayerExpansionTerm_Λ_two_filter G (Λ.volume n) t

/-- **Along-ex: mayerPartialSum at `N = 2`**. -/
theorem mayerPartialSumAlongExhaustion_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) 2 t =
      (∑ P ∈ IsingModel.allPolymers (inducedGraph G (Λ.volume n)),
            t ^ P.card) +
        (-1/2 : ℝ) *
          ∑ pq ∈ ((IsingModel.allPolymers
                    (inducedGraph G (Λ.volume n))) ×ˢ
                  (IsingModel.allPolymers
                    (inducedGraph G (Λ.volume n)))).filter
              (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card) :=
  mayerPartialSum_Λ_two G (Λ.volume n) t

/-- **Along-ex: mayerPartialSum = 0 on no-polymer graphs**. -/
theorem mayerPartialSumAlongExhaustion_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_no : IsingModel.allPolymers (inducedGraph G (Λ.volume n)) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) N t = 0 :=
  mayerPartialSum_Λ_eq_zero_of_no_polymers G (Λ.volume n) h_no t N

/-- **Along-ex: mayerPartialSum = 0 on edgeless graphs**. -/
theorem mayerPartialSumAlongExhaustion_eq_zero_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) N t = 0 :=
  mayerPartialSum_Λ_eq_zero_of_edgeFinset_empty
    G (Λ.volume n) h_empty t N

/-- **Along-ex: mayerExpansionTerm absolute bound**. -/
theorem mayerExpansionTermAlongExhaustion_abs_le
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (t : ℝ) (n : ℕ) :
    |IsingModel.mayerExpansionTerm (inducedGraph G (Λ.volume n)) k t| ≤
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin k => IsingModel.allPolymers
                (inducedGraph G (Λ.volume n))),
        |IsingModel.ursellCoefficient ω| *
          |IsingModel.clusterSeqActivity t ω| :=
  mayerExpansionTerm_Λ_abs_le G (Λ.volume n) k t

/-! ### §18.5 polymerFreeEnergy at-zero/at-one + sandwich
along-ex -/

/-- **Along-ex: polymerFreeEnergy at `t = 0`** = 0. -/
theorem polymerFreeEnergyAlongExhaustion_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) 0 = 0 :=
  polymerFreeEnergy_Λ_at_zero G (Λ.volume n)

/-- **Along-ex: polymerFreeEnergy at `t = 1`** =
`log |vdCompatiblePolymerFamilies|`. -/
theorem polymerFreeEnergyAlongExhaustion_at_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) 1 =
      Real.log (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph G (Λ.volume n))).card :=
  polymerFreeEnergy_Λ_at_one G (Λ.volume n)

/-- **Along-ex: polymerFreeEnergy sandwich for `t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_sandwich_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t ∧
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log (1 + t) :=
  polymerFreeEnergy_Λ_sandwich_of_nonneg G (Λ.volume n) ht

/-! ### §18.5 polymerFreeEnergy tanh-bound + ferro + hasDerivAt +
eq_log_one_add along-ex wraps -/

/-- **Along-ex: polymerFreeEnergy tanh ≤ |E| · tanh** under
`0 ≤ β·J`. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_card_mul
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) :=
  polymerFreeEnergy_Λ_tanh_le_card_mul G (Λ.volume n) hβJ

/-- **Along-ex: ferromagnetic polymerFreeEnergy_tanh ≤ |E|·tanh**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_card_mul_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) :=
  polymerFreeEnergy_Λ_tanh_le_card_mul_ferromagnetic
    G (Λ.volume n) hJ hβ

/-- **Along-ex: ferromagnetic polymerFreeEnergy_tanh sandwich**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_sandwich_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  polymerFreeEnergy_Λ_tanh_sandwich_ferromagnetic
    G (Λ.volume n) hJ hβ

/-- **Along-ex: ferromagnetic polymerFreeEnergy_tanh ≤ |E|·log 2**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log 2 :=
  polymerFreeEnergy_Λ_tanh_le_card_log_two_ferro G (Λ.volume n) hJ hβ

/-- **Along-ex: polymerFreeEnergy = log(1 + ε(t))** decomposition. -/
theorem polymerFreeEnergyAlongExhaustion_eq_log_one_add_eps
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t =
      Real.log (1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) :=
  polymerFreeEnergy_Λ_eq_log_one_add_eps G (Λ.volume n) t

/-- **Along-ex: polymerFreeEnergy hasDerivAt at `t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_hasDerivAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    HasDerivAt (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) s)
      ((∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
            ((Q.card : ℝ) * t ^ (Q.card - 1))) /
        (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
            ∏ P ∈ Γ, t ^ P.card)) t :=
  polymerFreeEnergy_Λ_hasDerivAt G (Λ.volume n) ht

/-! ### §18.5 Mayer recurrence + hasSum + tendsto along-ex wraps -/

/-- **Along-ex: mayerPartialSum recurrence** in `N`. -/
theorem mayerPartialSumAlongExhaustion_succ
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n))
        (N + 1) t =
      IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) N t +
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) (N + 1) t :=
  mayerPartialSum_Λ_succ G (Λ.volume n) N t

/-- **Along-ex: mayerExpansionTerm = mayerPartialSum diff**. -/
theorem mayerExpansionTermAlongExhaustion_eq_mayerPartialSum_diff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) (N + 1) t =
      IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) (N + 1) t -
        IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) N t :=
  mayerExpansionTerm_Λ_eq_mayerPartialSum_diff G (Λ.volume n) N t

/-- **Along-ex: polymerFreeEnergy hasSum via log under `|ε(t)| < 1`**. -/
theorem polymerFreeEnergyAlongExhaustion_hasSum_via_log
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) {t : ℝ}
    (h_abs : |∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                        (inducedGraph G (Λ.volume n))).erase ∅,
                ∏ P ∈ Γ, t ^ P.card| < 1) :
    HasSum (fun k : ℕ =>
        (-1 : ℝ) ^ k *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                    (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) ^ (k + 1) /
          (k + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t) :=
  polymerFreeEnergy_Λ_hasSum_via_log G (Λ.volume n) h_abs

/-- **Along-ex: polymerFreeEnergy hasSum eventually as `t → 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_hasSum_via_log_eventually
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    ∀ᶠ t : ℝ in nhds 0,
      HasSum (fun k : ℕ =>
          (-1 : ℝ) ^ k *
            (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                      (inducedGraph G (Λ.volume n))).erase ∅,
                ∏ P ∈ Γ, t ^ P.card) ^ (k + 1) /
            (k + 1))
        (IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t) :=
  polymerFreeEnergy_Λ_hasSum_via_log_eventually G (Λ.volume n)

/-- **Along-ex: ε(t) → 0 as t → 0**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_tendsto_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Filter.Tendsto (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) (nhds 0) (nhds 0) :=
  vdPolymerFamilies_sum_Λ_minus_one_tendsto_zero G (Λ.volume n)

/-! ### §18.5 ε(t) infrastructure + Mayer term sign + allPolymers
empty along-ex wraps -/

/-- **Along-ex: 0 ≤ mayerExpansionTerm at n = 1** under `0 ≤ t`. -/
theorem mayerExpansionTermAlongExhaustion_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 1 t :=
  mayerExpansionTerm_Λ_one_nonneg_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: mayerExpansionTerm at n = 2 ≤ 0** under `0 ≤ t`. -/
theorem mayerExpansionTermAlongExhaustion_two_nonpos_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.mayerExpansionTerm (inducedGraph G (Λ.volume n)) 2 t
      ≤ 0 :=
  mayerExpansionTerm_Λ_two_nonpos_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: ε(0) = 0**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 :=
  vdPolymerFamilies_sum_Λ_minus_one_at_zero G (Λ.volume n)

/-- **Along-ex: ε(t) is `Continuous`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_minus_one_continuous G (Λ.volume n)

/-- **Along-ex: ε(t) < 1 eventually as t → 0**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_lt_one_eventually
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    ∀ᶠ t : ℝ in nhds 0,
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) < 1 :=
  vdPolymerFamilies_sum_Λ_minus_one_lt_one_eventually G (Λ.volume n)

/-- **Along-ex: allPolymers = ∅ on edgeless induced graphs**. -/
theorem allPolymersAlongExhaustion_eq_empty_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅) :
    IsingModel.allPolymers (inducedGraph G (Λ.volume n)) = ∅ :=
  allPolymers_Λ_eq_empty_of_edgeFinset_empty G (Λ.volume n) h_empty

/-! ### §18.5 ε(t) / polymerFreeEnergy positivity-iff along-ex
wraps -/

/-- **Along-ex: 0 < ε(t) ↔ 0 < t ∧ allPolymers ≠ ∅** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_pos_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ↔
      0 < t ∧
        (IsingModel.allPolymers
          (inducedGraph G (Λ.volume n))).Nonempty :=
  vdPolymerFamilies_sum_Λ_minus_one_pos_iff G (Λ.volume n) ht

/-- **Along-ex: ε(t) = 0 ↔ t = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_eq_zero_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 ↔
      t = 0 ∨
        IsingModel.allPolymers
          (inducedGraph G (Λ.volume n)) = ∅ :=
  vdPolymerFamilies_sum_Λ_minus_one_eq_zero_iff G (Λ.volume n) ht

/-- **Along-ex: 0 < ε(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_pos_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph G (Λ.volume n))).Nonempty :=
  vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_iff G (Λ.volume n) hβJ

/-- **Along-ex: ε(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_eq_zero_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph G (Λ.volume n)) = ∅ :=
  vdPolymerFamilies_sum_Λ_minus_one_tanh_eq_zero_iff
    G (Λ.volume n) hβJ

/-- **Along-ex: 0 < polymerFreeEnergy(tanh) ↔ 0 < tanh ∧
allPolymers ≠ ∅**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_pos_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph G (Λ.volume n))).Nonempty :=
  polymerFreeEnergy_Λ_tanh_pos_iff G (Λ.volume n) hβJ

/-- **Along-ex: polymerFreeEnergy(tanh) = 0 ↔ tanh = 0 ∨
allPolymers = ∅**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G (Λ.volume n)) = ∅ :=
  polymerFreeEnergy_Λ_tanh_eq_zero_iff G (Λ.volume n) hβJ

/-! ### §18.5 strict-mono / strict-pos under polymers ≠ ∅ along-ex
wraps -/

/-- **Along-ex: vdSum(s) < vdSum(t) under polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_lt_of_lt_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, s ^ P.card) <
      ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_lt_of_lt_of_polymers_nonempty
    G (Λ.volume n) h_poly hs hst

/-- **Along-ex: vdSum is `StrictMonoOn (Set.Ici 0)`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_strictMonoOn_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  vdPolymerFamilies_sum_Λ_strictMonoOn_of_polymers_nonempty
    G (Λ.volume n) h_poly

/-- **Along-ex: 0 < pFE under `0 < t` and polymers exist**. -/
theorem polymerFreeEnergyAlongExhaustion_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    0 < IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t :=
  polymerFreeEnergy_Λ_pos_of_t_pos_of_polymers_nonempty
    G (Λ.volume n) h_t_pos h_poly

/-- **Along-ex: 1 < vdSum under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_gt_one_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
            ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_gt_one_of_t_pos_of_polymers_nonempty
    G (Λ.volume n) h_t_pos h_poly

/-- **Along-ex: 0 < ε(t) under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_minus_one_pos_of_t_pos_of_polymers_nonempty
    G (Λ.volume n) h_t_pos h_poly

/-- **Along-ex: 0 < pFE(tanh) under `0 < tanh` and polymers exist**. -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J)) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) :=
  polymerFreeEnergy_Λ_tanh_pos_of_tanh_pos_of_polymers_nonempty
    G (Λ.volume n) h_tanh_pos h_poly

/-- **Along-ex: 1 < vdSum(tanh) under `0 < tanh` and polymers
exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J)) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    G (Λ.volume n) h_tanh_pos h_poly

/-- **Along-ex: 0 < ε(tanh) under `0 < tanh` and polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J)) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    G (Λ.volume n) h_tanh_pos h_poly

/-- **Along-ex: pFE is `StrictMonoOn (Set.Ioi 0)`**. -/
theorem
polymerFreeEnergyAlongExhaustion_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    StrictMonoOn (fun t : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t) (Set.Ioi 0) :=
  polymerFreeEnergy_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    G (Λ.volume n) h_poly

/-- **Along-ex: vdSum is `StrictMonoOn (Set.Ioi 0)`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ioi 0) :=
  vdPolymerFamilies_sum_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    G (Λ.volume n) h_poly

/-! ### §18.5 polymerFreeEnergy/vdSum tanh ferromagnetic iff family
along-ex wraps -/

/-- **Along-ex: pFE(tanh) < ε(tanh) ↔ ε(tanh) > 0** (ferro). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_eps_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos_ferro
    G (Λ.volume n) hβ hJ

/-- **Along-ex: pFE(tanh) = 0 ↔ ε(tanh) = 0** (ferro). -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff_eps_eq_zero_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero_ferro
    G (Λ.volume n) hβ hJ

/-- **Along-ex: 0 < pFE(tanh) ↔ 0 < ε(tanh)** (ferro). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_pos_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos_ferro G (Λ.volume n) hβ hJ

/-- **Along-ex: 0 < pFE(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅** (ferro). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_pos_iff_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph G (Λ.volume n))).Nonempty :=
  polymerFreeEnergy_Λ_tanh_pos_iff_ferro G (Λ.volume n) hβ hJ

/-- **Along-ex: pFE(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅** (ferro). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G (Λ.volume n)) = ∅ :=
  polymerFreeEnergy_Λ_tanh_eq_zero_iff_ferro G (Λ.volume n) hβ hJ

/-- **Along-ex: 1 < vdSum(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅**
(ferro). -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_iff_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph G (Λ.volume n))).Nonempty :=
  vdPolymerFamilies_sum_Λ_tanh_gt_one_iff_ferro G (Λ.volume n) hβ hJ

/-- **Along-ex: vdSum(tanh) = 1 ↔ tanh = 0 ∨ allPolymers = ∅**
(ferro). -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_eq_one_iff_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G (Λ.volume n)) = ∅ :=
  vdPolymerFamilies_sum_Λ_tanh_eq_one_iff_ferro G (Λ.volume n) hβ hJ

/-- **Along-ex: pFE(tanh) < (1+tanh)^|E| - 1** under ε(tanh) > 0
(ferro). -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_lt_pow_sub_one_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 :=
  polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos_ferro
    G (Λ.volume n) hβ hJ h_eps_pos

/-- **Along-ex: pFE(tanh) < ε(tanh)** under ε(tanh) > 0 (ferro). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_eps_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos_ferro
    G (Λ.volume n) hβ hJ h_eps_pos

/-! ### §18.5 polymerFreeEnergy tanh sharpening + β/J strict-mono
along-ex wraps -/

/-- **Along-ex: pFE(tanh) < ε(tanh) ↔ 0 < ε(tanh)** under
`0 ≤ β·J`. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_eps_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos G (Λ.volume n) hβJ

/-- **Along-ex: pFE(tanh) = 0 ↔ ε(tanh) = 0** under `0 ≤ β·J`. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero G (Λ.volume n) hβJ

/-- **Along-ex: 0 < pFE(tanh) ↔ 0 < ε(tanh)** under `0 ≤ β·J`. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_pos_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos G (Λ.volume n) hβJ

/-- **Along-ex: pFE(tanh) < ε(tanh)** under ε(tanh) > 0
(`0 ≤ β·J`). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_eps_of_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos G (Λ.volume n) hβJ h_eps_pos

/-- **Along-ex: pFE(tanh) < (1+tanh)^|E| - 1** under ε(tanh) > 0
(`0 ≤ β·J`). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_pow_sub_one_of_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 :=
  polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos
    G (Λ.volume n) hβJ h_eps_pos

/-- **Along-ex: pFE(tanh(β₁·J)) < pFE(tanh(β₂·J))** under `J > 0`,
`0 ≤ β₁ < β₂`, polymers nonempty. -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty)
    {β₁ β₂ J : ℝ} (hβ₁ : 0 ≤ β₁) (hJ : 0 < J) (hβ : β₁ < β₂) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β₁ * J)) <
      IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β₂ * J)) :=
  polymerFreeEnergy_Λ_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    G (Λ.volume n) h_poly hβ₁ hJ hβ

/-- **Along-ex: pFE(tanh(β·J₁)) < pFE(tanh(β·J₂))** under `β > 0`,
`0 ≤ J₁ < J₂`, polymers nonempty. -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty)
    {β J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hβ : 0 < β) (hJ : J₁ < J₂) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J₁)) <
      IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J₂)) :=
  polymerFreeEnergy_Λ_tanh_lt_of_lt_in_J_of_polymers_nonempty
    G (Λ.volume n) h_poly hJ₁ hβ hJ

/-- **Along-ex: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in β**
under `J > 0` and polymers nonempty. -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_strictMonoOn_beta_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty)
    {J : ℝ} (hJ : 0 < J) :
    StrictMonoOn (fun β : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)))
      (Set.Ici 0) :=
  polymerFreeEnergy_Λ_tanh_strictMonoOn_beta_of_polymers_nonempty
    G (Λ.volume n) h_poly hJ

/-- **Along-ex: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in J**
under `β > 0` and polymers nonempty. -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_strictMonoOn_J_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun J : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)))
      (Set.Ici 0) :=
  polymerFreeEnergy_Λ_tanh_strictMonoOn_J_of_polymers_nonempty
    G (Λ.volume n) h_poly hβ

/-! ### §18.5 ε(t) nonneg + non-tanh polymerFreeEnergy sharpening
along-ex wraps -/

/-- **Along-ex: 0 ≤ ε(t)** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_minus_one_nonneg_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: ε(0)^k = 0** for `k ≥ 1`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_pow_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ k = 0 :=
  vdPolymerFamilies_sum_Λ_minus_one_pow_at_zero G (Λ.volume n) hk

/-- **Along-ex: pFE(t) = 0 ↔ ε(t) = 0** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_eq_zero_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 :=
  polymerFreeEnergy_Λ_eq_zero_iff_eps_eq_zero G (Λ.volume n) ht

/-- **Along-ex: 0 < pFE(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_pos_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  polymerFreeEnergy_Λ_pos_iff_eps_pos G (Λ.volume n) ht

/-- **Along-ex: pFE(t) < ε(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_lt_eps_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  polymerFreeEnergy_Λ_lt_eps_iff_eps_pos G (Λ.volume n) ht

/-- **Along-ex: pFE(t) < (1+t)^|E| - 1** under `0 ≤ t` and ε(t) > 0. -/
theorem polymerFreeEnergyAlongExhaustion_lt_pow_sub_one_of_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t <
      (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 :=
  polymerFreeEnergy_Λ_lt_pow_sub_one_of_eps_pos
    G (Λ.volume n) ht h_eps_pos

/-! ### §18.5 vdSum sandwich/monotone + ε bound + pFE(tanh) bound +
log2 along-ex wraps -/

/-- **Along-ex: vdSum sandwich for `t ≥ 0`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_sandwich_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_sandwich_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: vdSum is `MonotoneOn (Set.Ici 0)`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_monotoneOn_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    MonotoneOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  vdPolymerFamilies_sum_Λ_monotoneOn_Ici_zero G (Λ.volume n)

/-- **Along-ex: ε(t) ≤ (1+t)^|E| - 1** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_le_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 :=
  vdPolymerFamilies_sum_Λ_minus_one_le_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: pFE(tanh) ≤ ε(tanh) under `0 ≤ β·J`**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_eps_of_betaJ_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_le_eps_of_betaJ_nonneg G (Λ.volume n) hβJ

/-- **Along-ex: pFE(tanh) ≤ (1+tanh)^|E| - 1 under `0 ≤ β·J`**. -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_le_pow_sub_one_of_betaJ_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 :=
  polymerFreeEnergy_Λ_tanh_le_pow_sub_one_of_betaJ_nonneg
    G (Λ.volume n) hβJ

/-- **Along-ex: pFE(tanh) < log 2** under `(1+tanh)^|E| < 2`. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_log_two_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card < 2) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) < Real.log 2 :=
  polymerFreeEnergy_Λ_tanh_lt_log_two_of_pow_lt_two
    G (Λ.volume n) hβJ h_pow

/-! ### §18.6 partitionFunctionAlongExhaustion regularity at `h = 0`
along-ex wraps -/

/-- **Along-ex: partitionFunction Continuous in `β` at `h = 0`,
per stage `n`**. -/
theorem partitionFunctionAlongExhaustion_continuous_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    Continuous (fun β : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n) :=
  partitionFunctionΛ_continuous_beta_h_zero G (Λ.volume n) J

/-- **Along-ex: partitionFunction Continuous in `J` at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_continuous_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Continuous (fun J : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n) :=
  partitionFunctionΛ_continuous_J_h_zero G (Λ.volume n) β

/-- **Along-ex: partitionFunction Differentiable in `β` at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n) :=
  partitionFunctionΛ_differentiable_beta_h_zero G (Λ.volume n) J

/-- **Along-ex: partitionFunction Differentiable in `J` at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n) :=
  partitionFunctionΛ_differentiable_J_h_zero G (Λ.volume n) β

/-- **Along-ex: partitionFunction `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β'⟩ n) β :=
  partitionFunctionΛ_analyticAt_beta_h_zero G (Λ.volume n) J β

/-- **Along-ex: partitionFunction `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', 0, β⟩ n) J :=
  partitionFunctionΛ_analyticAt_J_h_zero G (Λ.volume n) β J

/-- **Along-ex: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `β`
at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_analyticOnNhd_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β'⟩ n) Set.univ :=
  partitionFunctionΛ_analyticOnNhd_beta_h_zero G (Λ.volume n) J

/-- **Along-ex: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `J`
at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_analyticOnNhd_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', 0, β⟩ n) Set.univ :=
  partitionFunctionΛ_analyticOnNhd_J_h_zero G (Λ.volume n) β

/-! ### §18.6 freeEnergyAlongExhaustion per-direction analyticity
along-ex wraps -/

/-- **Along-ex: freeEnergy `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem freeEnergyAlongExhaustion_analyticAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, 0, β'⟩ n) β :=
  freeEnergyΛ_analyticAt_beta_h_zero G (Λ.volume n) J β

/-- **Along-ex: freeEnergy `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem freeEnergyAlongExhaustion_analyticAt_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', 0, β⟩ n) J :=
  freeEnergyΛ_analyticAt_J_h_zero G (Λ.volume n) β J

/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
`h = 0`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, 0, β'⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_beta_h_zero G (Λ.volume n) J

/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
`h = 0`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', 0, β⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_J_h_zero G (Λ.volume n) β

/-- **Along-ex: freeEnergy `AnalyticAt ℝ` in `β` at general `h`**. -/
theorem freeEnergyAlongExhaustion_analyticAt_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  freeEnergyΛ_analyticAt_beta_general_h G (Λ.volume n) J h β

/-- **Along-ex: freeEnergy `AnalyticAt ℝ` in `J` at general `h`**. -/
theorem freeEnergyAlongExhaustion_analyticAt_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  freeEnergyΛ_analyticAt_J_general_h G (Λ.volume n) β h J

/-- **Along-ex: freeEnergy `AnalyticAt ℝ` in `h`**. -/
theorem freeEnergyAlongExhaustion_analyticAt_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β h : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  freeEnergyΛ_analyticAt_h G (Λ.volume n) J β h

/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
general `h`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_beta_general_h G (Λ.volume n) J h

/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
general `h`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_J_general_h G (Λ.volume n) β h

/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `h`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_h G (Λ.volume n) J β

/-! ### §18.6 partitionFunctionAlongExhaustion joint + general-h
analyticity along-ex wraps -/

/-- **Along-ex: partitionFunction jointly `Continuous` in
`(β, J, h)`**. -/
theorem partitionFunctionAlongExhaustion_continuous_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) :=
  partitionFunctionΛ_continuous_joint G (Λ.volume n)

/-- **Along-ex: partitionFunction jointly `Differentiable ℝ` in
`(β, J, h)`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) :=
  partitionFunctionΛ_differentiable_joint G (Λ.volume n)

/-- **Along-ex: partitionFunction `AnalyticAt ℝ` in `β` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  partitionFunctionΛ_analyticAt_beta_general_h G (Λ.volume n) J h β

/-- **Along-ex: partitionFunction `AnalyticAt ℝ` in `J` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  partitionFunctionΛ_analyticAt_J_general_h G (Λ.volume n) β h J

/-- **Along-ex: partitionFunction `AnalyticAt ℝ` in `h`**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β h : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  partitionFunctionΛ_analyticAt_h G (Λ.volume n) J β h

/-! ### §18.6 partitionFunction/freeEnergy Continuous + Differentiable
along-ex wraps (Λ-layer wraps via PR #1541 / #1533) -/

/-- **Along-ex: partitionFunction Continuous in `β` at general `h`**. -/
theorem partitionFunctionAlongExhaustion_continuous_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  partitionFunctionΛ_continuous_beta_general_h G (Λ.volume n) J h

/-- **Along-ex: partitionFunction Continuous in `J` at general `h`**. -/
theorem partitionFunctionAlongExhaustion_continuous_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  partitionFunctionΛ_continuous_J_general_h G (Λ.volume n) β h

/-- **Along-ex: partitionFunction Differentiable in `β` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  partitionFunctionΛ_differentiable_beta_general_h G (Λ.volume n) J h

/-- **Along-ex: partitionFunction Differentiable in `J` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  partitionFunctionΛ_differentiable_J_general_h G (Λ.volume n) β h

/-- **Along-ex: partitionFunction Continuous in `h`**. -/
theorem partitionFunctionAlongExhaustion_continuous_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Continuous (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  partitionFunctionΛ_continuous_h G (Λ.volume n) J β

/-- **Along-ex: partitionFunction Differentiable in `h`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  partitionFunctionΛ_differentiable_h G (Λ.volume n) J β

/-- **Along-ex: freeEnergy jointly Continuous**. -/
theorem freeEnergyAlongExhaustion_continuous_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) :=
  freeEnergyΛ_continuous_joint G (Λ.volume n)

/-- **Along-ex: freeEnergy jointly Differentiable ℝ**. -/
theorem freeEnergyAlongExhaustion_differentiable_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) :=
  freeEnergyΛ_differentiable_joint G (Λ.volume n)

/-- **Along-ex: freeEnergy Continuous in β** (general h). -/
theorem freeEnergyAlongExhaustion_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  freeEnergyΛ_continuous_beta G (Λ.volume n) J h

/-- **Along-ex: freeEnergy Differentiable in β** (general h). -/
theorem freeEnergyAlongExhaustion_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  freeEnergyΛ_differentiable_beta G (Λ.volume n) J h

/-- **Along-ex: freeEnergy Continuous in h**. -/
theorem freeEnergyAlongExhaustion_continuous_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Continuous (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  freeEnergyΛ_continuous_field G (Λ.volume n) J β

/-- **Along-ex: freeEnergy Differentiable in h**. -/
theorem freeEnergyAlongExhaustion_differentiable_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  freeEnergyΛ_differentiable_field G (Λ.volume n) J β

/-- **Along-ex: freeEnergy Continuous in J**. -/
theorem freeEnergyAlongExhaustion_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  freeEnergyΛ_continuous_J G (Λ.volume n) h β

/-- **Along-ex: freeEnergy Differentiable in J**. -/
theorem freeEnergyAlongExhaustion_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  freeEnergyΛ_differentiable_J G (Λ.volume n) h β

/-! ### §18.4-§18.6 capstones along-ex wraps -/

/-- **Along-ex: §18.4 partitionFunction polymer-family form**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_polymer_family
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n =
      (2 : ℝ) ^ Fintype.card ↑(Λ.volume n : Finset V) *
        Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card *
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_polymer_family
    G (Λ.volume n) J β

/-- **Along-ex: §18.4 partitionFunction even-subgraph form**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_evenSubgraphs
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n =
      (2 : ℝ) ^ Fintype.card ↑(Λ.volume n : Finset V) *
        Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card *
        ∑ X ∈ IsingModel.evenSubgraphs (inducedGraph G (Λ.volume n)),
          Real.tanh (β * J) ^ X.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_closed_evenSubgraphs
    G (Λ.volume n) J β

/-- **Along-ex: §18.6 freeEnergy decomposition** under `0 ≤ β·J` and
`(Λ.volume n).Nonempty`. -/
theorem freeEnergyAlongExhaustion_eq_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ ⟨J, 0, β⟩ n =
      Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ.volume n : Finset V) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ.volume n : Finset V) :=
  freeEnergyΛ_eq_polymerFreeEnergy G (Λ.volume n) J β hβJ hne

/-- **Along-ex: §18.6 ferromagnetic freeEnergy decomposition**. -/
theorem freeEnergyAlongExhaustion_eq_polymerFreeEnergy_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ ⟨J, 0, β⟩ n =
      Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ.volume n : Finset V) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ.volume n : Finset V) :=
  freeEnergyΛ_eq_polymerFreeEnergy_ferromagnetic
    G (Λ.volume n) J β hJ hβ hne

/-- **Along-ex: freeEnergy = log 2 at `β·J = 0`** under
`(Λ.volume n).Nonempty`. -/
theorem freeEnergyAlongExhaustion_eq_log_two_at_betaJ_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ ⟨J, 0, β⟩ n = Real.log 2 :=
  freeEnergyΛ_eq_log_two_at_betaJ_zero G (Λ.volume n) hβJ hne

/-- **Along-ex: mayerPartialSum at N=1, t=1**. -/
theorem mayerPartialSumAlongExhaustion_one_at_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) 1 1 =
      (IsingModel.allPolymers (inducedGraph G (Λ.volume n))).card :=
  mayerPartialSum_Λ_one_at_one G (Λ.volume n)

/-! ### §18.5 Mayer filter-connected + ε^n along-ex wraps -/

/-- **Along-ex: ε(t)^n as multi-Γ piFinset sum**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_pow
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (k : ℕ) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ^ k =
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin k =>
                (IsingModel.vdCompatiblePolymerFamilies
                  (inducedGraph G (Λ.volume n))).erase ∅),
        ∏ i : Fin k, ∏ P ∈ ω i, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_minus_one_pow G (Λ.volume n) t k

/-- **Along-ex: mayerExpansionTerm filter-connected at k=0 = ∅**. -/
theorem mayerExpansionTermAlongExhaustion_filter_connected_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    (Fintype.piFinset
        (fun _ : Fin 0 =>
          IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) = ∅ :=
  mayerExpansionTerm_Λ_filter_connected_zero G (Λ.volume n) t

/-- **Along-ex: mayerExpansionTerm filter-connected at k=1 = full
piFinset**. -/
theorem mayerExpansionTermAlongExhaustion_filter_connected_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers
            (inducedGraph G (Λ.volume n))) :=
  mayerExpansionTerm_Λ_filter_connected_one G (Λ.volume n)

/-- **Along-ex: filter-connected = filter-incompatible at k=2**. -/
theorem mayerExpansionTermAlongExhaustion_two_filter_connected_eq_incompat
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (Fintype.piFinset
        (fun _ : Fin 2 =>
          IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      (Fintype.piFinset
          (fun _ : Fin 2 =>
            IsingModel.allPolymers
              (inducedGraph G (Λ.volume n)))).filter
          (fun ω => IsingModel.PolymersIncompatible (ω 0) (ω 1)) :=
  mayerExpansionTerm_Λ_two_filter_connected_eq_incompat G (Λ.volume n)

/-! ### magnetization regularity along-ex wraps -/

/-- **Along-ex: magnetization Continuous in `h` for `i ∈
Λ.volume n`**. The site coercion is the obvious lift. -/
theorem magnetizationAlongExhaustion_continuous_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    Continuous (fun h' =>
      magnetizationAlongExhaustion G Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact magnetizationΛ_continuous_field G (Λ.volume n) J β _
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

/-- **Along-ex: magnetization Differentiable in `h`**. -/
theorem magnetizationAlongExhaustion_differentiable_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun h' =>
      magnetizationAlongExhaustion G Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact magnetizationΛ_differentiable_field G (Λ.volume n) J β _
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

/-- **Along-ex: magnetization Continuous in `J`**. -/
theorem magnetizationAlongExhaustion_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (i : V) (n : ℕ) :
    Continuous (fun J' =>
      magnetizationAlongExhaustion G Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact magnetizationΛ_continuous_J G (Λ.volume n) h β _
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

/-- **Along-ex: magnetization Differentiable in `J`**. -/
theorem magnetizationAlongExhaustion_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun J' =>
      magnetizationAlongExhaustion G Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact magnetizationΛ_differentiable_J G (Λ.volume n) h β _
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

/-- **Along-ex: magnetization Continuous in `β`** (general h). -/
theorem magnetizationAlongExhaustion_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    Continuous (fun β' =>
      magnetizationAlongExhaustion G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact magnetizationΛ_continuous_beta G (Λ.volume n) J h _
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

/-- **Along-ex: magnetization Differentiable in `β`** (general h). -/
theorem magnetizationAlongExhaustion_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun β' =>
      magnetizationAlongExhaustion G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact magnetizationΛ_differentiable_beta G (Λ.volume n) J h _
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

/-! ### ContinuousAt / DifferentiableAt along-ex wrappers -/

/-- **Along-ex: magnetization ContinuousAt β** (general h). -/
theorem magnetizationAlongExhaustion_continuousAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun β' => magnetizationAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (magnetizationAlongExhaustion_continuous_beta G Λ J h i n).continuousAt

/-- **Along-ex: magnetization DifferentiableAt β** (general h). -/
theorem magnetizationAlongExhaustion_differentiableAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun β' => magnetizationAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (magnetizationAlongExhaustion_differentiable_beta G Λ J h i n).differentiableAt

/-- **Along-ex: magnetization ContinuousAt h**. -/
theorem magnetizationAlongExhaustion_continuousAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun h' => magnetizationAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (magnetizationAlongExhaustion_continuous_field G Λ J β i n).continuousAt

/-- **Along-ex: magnetization DifferentiableAt h**. -/
theorem magnetizationAlongExhaustion_differentiableAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun h' => magnetizationAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (magnetizationAlongExhaustion_differentiable_field G Λ J β i n).differentiableAt

/-- **Along-ex: magnetization ContinuousAt J**. -/
theorem magnetizationAlongExhaustion_continuousAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun J' => magnetizationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (magnetizationAlongExhaustion_continuous_J G Λ h β i n).continuousAt

/-- **Along-ex: magnetization DifferentiableAt J**. -/
theorem magnetizationAlongExhaustion_differentiableAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun J' => magnetizationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (magnetizationAlongExhaustion_differentiable_J G Λ h β i n).differentiableAt

/-! ### magnetization parameter-direction convergent (β/h/J → ∞)
along-ex wraps -/

/-- **Along-ex: magnetization β → ∞ convergence**. Per-stage `n`. -/
theorem magnetizationAlongExhaustion_convergent_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => magnetizationΛ G (Λ.volume n)
          (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold magnetizationAlongExhaustion correlationAlongExhaustion
      simp only [Finset.singleton_subset_iff, hi, dif_pos]
      rfl
    rw [h_eq]
    exact magnetizationΛ_convergent_beta G (Λ.volume n) J hJ h hh _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold magnetizationAlongExhaustion correlationAlongExhaustion
      simp only [Finset.singleton_subset_iff, hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

/-- **Along-ex: magnetization h → ∞ convergence**. -/
theorem magnetizationAlongExhaustion_convergent_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => magnetizationΛ G (Λ.volume n)
          (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold magnetizationAlongExhaustion correlationAlongExhaustion
      simp only [Finset.singleton_subset_iff, hi, dif_pos]
      rfl
    rw [h_eq]
    exact magnetizationΛ_convergent_h G (Λ.volume n) J hJ β hβ _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold magnetizationAlongExhaustion correlationAlongExhaustion
      simp only [Finset.singleton_subset_iff, hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

/-- **Along-ex: magnetization J → ∞ convergence**. -/
theorem magnetizationAlongExhaustion_convergent_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => magnetizationΛ G (Λ.volume n)
          (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold magnetizationAlongExhaustion correlationAlongExhaustion
      simp only [Finset.singleton_subset_iff, hi, dif_pos]
      rfl
    rw [h_eq]
    exact magnetizationΛ_convergent_J G (Λ.volume n) h hh β hβ _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold magnetizationAlongExhaustion correlationAlongExhaustion
      simp only [Finset.singleton_subset_iff, hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

/-! ### susceptibility parameter-direction convergent (β/h/J → ∞)
along-ex wraps -/

/-- **Along-ex: susceptibility β → ∞ convergence**. Per-stage `n`. -/
theorem susceptibilityAlongExhaustion_convergent_beta_param
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => susceptibilityΛ G (Λ.volume n)
          (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_pos]
    rw [h_eq]
    exact susceptibilityΛ_convergent_beta G (Λ.volume n) J hJ h hh _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

/-- **Along-ex: susceptibility h → ∞ convergence**. -/
theorem susceptibilityAlongExhaustion_convergent_h_param
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => susceptibilityΛ G (Λ.volume n)
          (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_pos]
    rw [h_eq]
    exact susceptibilityΛ_convergent_h G (Λ.volume n) J hJ β hβ _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

/-- **Along-ex: susceptibility J → ∞ convergence**. -/
theorem susceptibilityAlongExhaustion_convergent_J_param
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => susceptibilityΛ G (Λ.volume n)
          (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_pos]
    rw [h_eq]
    exact susceptibilityΛ_convergent_J G (Λ.volume n) h hh β hβ _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

end Ambient
end IsingModel
