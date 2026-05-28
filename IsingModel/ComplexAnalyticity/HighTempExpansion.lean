import IsingModel.ComplexAnalyticity.Basic
import IsingModel.ClusterExpansion.Families
import IsingModel.ClusterExpansion.Families.SandwichBounds

/-!
# Complex partition function high-temperature polymer-family expansion

This module hosts the complex extension of the high-temperature polymer-family
expansion of the partition function. The base case at real parameters
(`partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_at_real`)
is the analytic-continuation seed for the general `(J, β) : ℂ × ℂ` identity
toward the volume-uniform `Z_ℂ` lower bound for the Lemma 17.5.2 `hZ` provider
(Issue #3044) via the cluster-expansion route (Issue #3054).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-- **Complex `Z` high-temperature polymer-family expansion at real parameters**
(Issue #3054): the complex partition function at real `J, β` (coerced to `ℂ`)
admits the same factorization as the real `Z` —
`partitionFunctionComplex G ↑J 0 ↑β = 2^|ι| · Complex.cosh(β·J)^|E| ·
∑_Γ ∏_P Complex.tanh(β·J)^|P|`.

Cast of `partitionFunction_high_temp_expansion_h_zero_polymer_family` via
`partitionFunction_ofReal_eq_partitionFunctionComplex` and the standard
`Complex.ofReal_*` casts. This is the analytic-continuation seed for the
general-`(J, β) : ℂ × ℂ` complex high-temperature expansion (still to be
established by identity theorem). -/
theorem partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_at_real
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    partitionFunctionComplex G (J : ℂ) 0 (β : ℂ) =
      (2 : ℂ) ^ Fintype.card ι *
        Complex.cosh ((β : ℂ) * (J : ℂ)) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh ((β : ℂ) * (J : ℂ)) ^ P.card := by
  have hreal :
      partitionFunction G ⟨J, 0, β⟩ =
        (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
          ∑ Γ ∈ vdCompatiblePolymerFamilies G,
            ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    partitionFunction_high_temp_expansion_h_zero_polymer_family G J β
  have hcast :
      ((partitionFunction G ⟨J, 0, β⟩ : ℝ) : ℂ) =
        partitionFunctionComplex G (J : ℂ) ((0 : ℝ) : ℂ) (β : ℂ) :=
    partitionFunction_ofReal_eq_partitionFunctionComplex G ⟨J, 0, β⟩
  -- Rewrite (0 : ℝ) : ℂ as (0 : ℂ).
  rw [show ((0 : ℝ) : ℂ) = (0 : ℂ) from Complex.ofReal_zero] at hcast
  rw [← hcast]
  -- Cast the real identity to ℂ.
  have hcast_id := congrArg (fun x : ℝ => (x : ℂ)) hreal
  simp only at hcast_id
  rw [hcast_id]
  push_cast
  rfl

end IsingModel
