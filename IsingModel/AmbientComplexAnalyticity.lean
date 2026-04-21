import IsingModel.AmbientLattice
import IsingModel.ComplexAnalyticity

/-!
# Complex partition function / free energy along an exhaustion

The complex analogues of `Ambient.partitionFunctionAlongExhaustion` and
`Ambient.freeEnergyAlongExhaustion`:

* `Ambient.partitionFunctionComplexAlongExhaustion G Λ J h β n`
  := `partitionFunctionComplex (inducedGraph G (Λ.volume n)) J h β`
* `Ambient.freeEnergyComplexAlongExhaustion G Λ J h β n`
  := `freeEnergyComplex (inducedGraph G (Λ.volume n)) J h β`

These are the foundational objects for the infinite-volume Vitali
completion argument for GJ §4.6 Thm 4.6.2: the per-site
`freeEnergyComplexAlongExhaustion` at stage `n` equals the finite-volume
`freeEnergyComplex` on the induced subgraph of the `Λ.volume n` block,
and the sequence is expected to converge (in the Montel/Vitali sense)
as `n → ∞` on the Lee-Yang (sub)domain.

This file supplies the definitions, their `_apply` unfoldings, and the
real-complex compatibility identities that identify the complex
along-exhaustion sequence with the cast of the real `…AlongExhaustion`
on real-parameter slices.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.6 Thm 4.6.2, pp. 67–70.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Complex partition function along an exhaustion**: per-stage
`Z_ℂ_{Λ_n}(J, h, β)`. Complex analogue of
`partitionFunctionAlongExhaustion`. -/
noncomputable def partitionFunctionComplexAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℂ) : ℕ → ℂ :=
  fun n => partitionFunctionComplex (inducedGraph G (Λ.volume n)) J h β

/-- **Unfolding of `partitionFunctionComplexAlongExhaustion`**:
equal to `partitionFunctionComplex` on the `n`-th volume by
construction. -/
@[simp]
theorem partitionFunctionComplexAlongExhaustion_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℂ) (n : ℕ) :
    partitionFunctionComplexAlongExhaustion G Λ J h β n
      = partitionFunctionComplex (inducedGraph G (Λ.volume n)) J h β :=
  rfl

/-- **Complex free energy along an exhaustion**: per-stage
`f_ℂ_{Λ_n}(J, h, β) = |Λ_n|⁻¹ · log Z_ℂ_{Λ_n}(J, h, β)`. Complex
analogue of `freeEnergyAlongExhaustion`. -/
noncomputable def freeEnergyComplexAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℂ) : ℕ → ℂ :=
  fun n => freeEnergyComplex (inducedGraph G (Λ.volume n)) J h β

/-- **Unfolding of `freeEnergyComplexAlongExhaustion`**:
equal to `freeEnergyComplex` on the `n`-th volume by construction. -/
@[simp]
theorem freeEnergyComplexAlongExhaustion_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℂ) (n : ℕ) :
    freeEnergyComplexAlongExhaustion G Λ J h β n
      = freeEnergyComplex (inducedGraph G (Λ.volume n)) J h β :=
  rfl

/-- **Real-complex compatibility** for the along-exhaustion Z at real
parameters: the cast of the real `partitionFunctionAlongExhaustion`
agrees with `partitionFunctionComplexAlongExhaustion` at the cast
parameters. Direct pointwise consequence of
`partitionFunction_ofReal_eq_partitionFunctionComplex`. -/
theorem partitionFunctionComplexAlongExhaustion_at_real_eq_ofReal
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    partitionFunctionComplexAlongExhaustion G Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n
      = ((partitionFunctionAlongExhaustion G Λ p n : ℝ) : ℂ) := by
  unfold partitionFunctionComplexAlongExhaustion
  unfold partitionFunctionAlongExhaustion partitionFunctionΛ
  exact (IsingModel.partitionFunction_ofReal_eq_partitionFunctionComplex
    (inducedGraph G (Λ.volume n)) p).symm

/-- **Real-complex compatibility** for the along-exhaustion free energy
at real parameters. Direct pointwise consequence of
`freeEnergy_ofReal_eq_freeEnergyComplex`. -/
theorem freeEnergyComplexAlongExhaustion_at_real_eq_ofReal
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyComplexAlongExhaustion G Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n
      = ((freeEnergyAlongExhaustion G Λ p n : ℝ) : ℂ) := by
  unfold freeEnergyComplexAlongExhaustion
  unfold freeEnergyAlongExhaustion freeEnergyΛ
  exact (IsingModel.freeEnergy_ofReal_eq_freeEnergyComplex
    (inducedGraph G (Λ.volume n)) p).symm

end Ambient

end IsingModel
