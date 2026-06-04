import IsingModel.Concrete.LatticeGraphCorrelation.LocalObservableUnion
import IsingModel.TranslationInvariance.FiniteVolume

/-!
# Boundary-condition translation covariance (Issue #3581 PR 1)

Towards translation invariance of the cubic-exhaustion `±`-state functional, this
file establishes the **translation covariance of the boundary-condition Gibbs
expectation** on a translation-invariant graph with uniform coupling and constant
field.  This is the boundary-condition analogue of `correlationΛ_vaddFinset_eq`.

* `plusConfig_configVaddEquiv` — the all-`+` configuration is translation-invariant.
* `agreesOff_map_configVaddEquiv_iff` — boundary agreement transports under
  translation.
* `boltzmannWeightBC_vaddFinset_eq` / `partitionFunctionBC_vaddFinset_eq` /
  `gibbsExpectationBC_vaddFinset_eq` — the per-configuration weight, partition
  function, and expectation covariance under translation.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
§3.4 (translation invariance of the infinite-volume Gibbs states).
-/

universe u v

namespace IsingModel

namespace Ambient

open Finset

variable {T : Type u} [AddGroup T] {V : Type v} [DecidableEq V] [AddAction T V]

/-- **The all-`+` configuration is translation-invariant**: `configVaddEquiv` maps
the all-`+` configuration on `↑Ω` to the all-`+` configuration on
`↑(vaddFinset t Ω)`. -/
theorem plusConfig_configVaddEquiv (t : T) (Ω : Finset V) :
    configVaddEquiv t Ω (plusConfig (↑Ω : Type _)) = plusConfig (↑(vaddFinset t Ω) : Type _) := by
  funext j
  rw [configVaddEquiv_apply]
  rfl

/-- **Boundary agreement transports under translation**: `σ'` agrees with the
translated boundary condition off the translated volume iff its pullback agrees
with the original boundary condition off the original volume. -/
theorem agreesOff_map_configVaddEquiv_iff (t : T) (Ω : Finset V) (Λ : Finset (↑Ω : Type _))
    (η : Config (↑Ω : Type _)) (σ' : Config (↑(vaddFinset t Ω) : Type _)) :
    agreesOff (Λ.map (vaddSubtypeEquiv t Ω).toEmbedding) (configVaddEquiv t Ω η) σ'
      ↔ agreesOff Λ η ((configVaddEquiv t Ω).symm σ') := by
  constructor
  · intro hag i hi
    have hj : vaddSubtypeEquiv t Ω i ∉ Λ.map (vaddSubtypeEquiv t Ω).toEmbedding := by
      rw [Finset.mem_map]
      rintro ⟨a, ha, hae⟩
      simp only [Equiv.coe_toEmbedding] at hae
      exact hi ((vaddSubtypeEquiv t Ω).injective hae ▸ ha)
    have hval := hag (vaddSubtypeEquiv t Ω i) hj
    rw [configVaddEquiv_symm_apply, hval, configVaddEquiv_apply, Equiv.symm_apply_apply]
  · intro hag j hj
    obtain ⟨i, rfl⟩ : ∃ i, vaddSubtypeEquiv t Ω i = j := ⟨(vaddSubtypeEquiv t Ω).symm j, by simp⟩
    have hi : i ∉ Λ := by
      intro hiΛ
      exact hj (Finset.mem_map.mpr ⟨i, hiΛ, by simp⟩)
    have hval := hag i hi
    rw [configVaddEquiv_apply, Equiv.symm_apply_apply, ← hval, configVaddEquiv_symm_apply]

variable (G : SimpleGraph V) [IsTranslationInvariant T G]

/-- **Per-configuration boundary weight covariance under translation**: for a
translation-invariant graph, uniform coupling, and constant field, the boundary
Boltzmann weight on the translated volume equals that on the original volume at the
pulled-back configuration. -/
theorem boltzmannWeightBC_vaddFinset_eq (t : T) (Ω : Finset V)
    [Fintype (inducedGraph G Ω).edgeSet]
    [Fintype (inducedGraph G (vaddFinset t Ω)).edgeSet]
    (β J h : ℝ) (Λ : Finset (↑Ω : Type _)) (η : Config (↑Ω : Type _))
    (σ' : Config (↑(vaddFinset t Ω) : Type _)) :
    boltzmannWeightBC (inducedGraph G (vaddFinset t Ω)) β (fun _ => J) h
        (Λ.map (vaddSubtypeEquiv t Ω).toEmbedding) (configVaddEquiv t Ω η) σ'
      = boltzmannWeightBC (inducedGraph G Ω) β (fun _ => J) h Λ η
          ((configVaddEquiv t Ω).symm σ') := by
  unfold boltzmannWeightBC
  by_cases hag : agreesOff Λ η ((configVaddEquiv t Ω).symm σ')
  · rw [Set.indicator_of_mem ((agreesOff_map_configVaddEquiv_iff t Ω Λ η σ').mpr hag),
      Set.indicator_of_mem hag, boltzmannWeightJ_uniform_eq, boltzmannWeightJ_uniform_eq]
    unfold boltzmannWeight
    rw [hamiltonian_configVaddEquiv_symm G t Ω (⟨J, h, β⟩ : IsingParams ℝ) σ']
  · rw [Set.indicator_of_notMem
      (fun hc => hag ((agreesOff_map_configVaddEquiv_iff t Ω Λ η σ').mp hc)),
      Set.indicator_of_notMem hag]

/-- **Partition-function covariance under translation**. -/
theorem partitionFunctionBC_vaddFinset_eq (t : T) (Ω : Finset V)
    [Fintype (inducedGraph G Ω).edgeSet]
    [Fintype (inducedGraph G (vaddFinset t Ω)).edgeSet]
    (β J h : ℝ) (Λ : Finset (↑Ω : Type _)) (η : Config (↑Ω : Type _)) :
    partitionFunctionBC (inducedGraph G (vaddFinset t Ω)) β (fun _ => J) h
        (Λ.map (vaddSubtypeEquiv t Ω).toEmbedding) (configVaddEquiv t Ω η)
      = partitionFunctionBC (inducedGraph G Ω) β (fun _ => J) h Λ η := by
  unfold partitionFunctionBC
  refine (Fintype.sum_equiv (configVaddEquiv t Ω) _ _ (fun σ => ?_)).symm
  simp only [boltzmannWeightBC_vaddFinset_eq G t Ω β J h Λ η, Equiv.symm_apply_apply]

/-- **Boundary-condition Gibbs expectation covariance under translation** (the BC
analogue of `correlationΛ_vaddFinset_eq`): for a translation-invariant graph,
uniform coupling, and constant field,

`⟨F ∘ τ⁻¹⟩^{τη}_{τΛ} = ⟨F⟩^η_Λ`,

where `τ = configVaddEquiv t Ω` transports the boundary condition and observable. -/
theorem gibbsExpectationBC_vaddFinset_eq (t : T) (Ω : Finset V)
    [Fintype (inducedGraph G Ω).edgeSet]
    [Fintype (inducedGraph G (vaddFinset t Ω)).edgeSet]
    (β J h : ℝ) (Λ : Finset (↑Ω : Type _)) (η : Config (↑Ω : Type _))
    (F : Config (↑Ω : Type _) → ℝ) :
    gibbsExpectationBC (inducedGraph G (vaddFinset t Ω)) β (fun _ => J) h
        (Λ.map (vaddSubtypeEquiv t Ω).toEmbedding) (configVaddEquiv t Ω η)
        (fun σ' => F ((configVaddEquiv t Ω).symm σ'))
      = gibbsExpectationBC (inducedGraph G Ω) β (fun _ => J) h Λ η F := by
  unfold gibbsExpectationBC
  rw [partitionFunctionBC_vaddFinset_eq G t Ω β J h Λ η]
  congr 1
  refine (Fintype.sum_equiv (configVaddEquiv t Ω) _ _ (fun σ => ?_)).symm
  simp only [boltzmannWeightBC_vaddFinset_eq G t Ω β J h Λ η, Equiv.symm_apply_apply]

end Ambient

end IsingModel
