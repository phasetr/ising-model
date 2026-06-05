import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateExhaustion

/-!
# General two-ambient independence of the `+` boundary expectation (Issue #3581)

Towards exhaustion independence: for an inner free region `I` whose lattice
neighbours all lie in `Λ₁`, the `+` boundary expectation of `O` is the same on any
two ambients `Ω₁, Ω₂ ⊇ Λ₁` — both reduce to the value on `Λ₁` by the general
ambient independence (`gibbsExpectationBC_screening_of_neighbors`).  This is the key
compatibility for the directed-infimum formulation of the `+` state: different
finite free regions can be compared by routing each through its own ambient.

* `gibbsExpectationBC_ambient_indep` — ambient independence across two ambients.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17 (statement p. 95, proof pp. 102–103).
-/

namespace IsingModel

namespace Ambient

open Finset

variable {d : ℕ}

/-- **General two-ambient independence**: for a free region `I` whose lattice
neighbours lie in `Λ₁`, and an observable `O` supported in `Λ₁`, the `+` boundary
expectation of `O` on `Ω₁` equals that on `Ω₂`, for any `Ω₁, Ω₂ ⊇ Λ₁` — both equal
the value on `Λ₁` (the shells are frozen `+` and cancel). -/
theorem gibbsExpectationBC_ambient_indep {Λ₁ Ω₁ Ω₂ : Finset (Fin d → ℤ)}
    (h1 : Λ₁ ⊆ Ω₁) (h2 : Λ₁ ⊆ Ω₂)
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Ω₁).edgeSet]
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Ω₂).edgeSet]
    (I : Finset (↑Λ₁ : Type _)) {J h β : ℝ}
    (hNN : ∀ k ∈ I, ∀ y : Fin d → ℤ, (IsingModel.latticeGraph d).Adj k.val y → y ∈ Λ₁)
    (O : LocalMonotoneObservable d) (hSΛ₁ : O.S ⊆ Λ₁) :
    gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) Ω₁) β (fun _ => J) h
        (I.map (subtypeInclEmb h1)) (plusConfig _) (O.lift (hSΛ₁.trans h1))
      = gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) Ω₂) β (fun _ => J) h
          (I.map (subtypeInclEmb h2)) (plusConfig _) (O.lift (hSΛ₁.trans h2)) := by
  haveI : Fintype (inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet := Fintype.ofFinite _
  rw [gibbsExpectationBC_screening_of_neighbors h1 I hNN (O.lift (hSΛ₁.trans h1))
      (O.lift hSΛ₁) (fun σ₁ σ₂ => ?_),
    gibbsExpectationBC_screening_of_neighbors h2 I hNN (O.lift (hSΛ₁.trans h2))
      (O.lift hSΛ₁) (fun σ₁ σ₂ => ?_)]
  · change O.φ (restrictConfig (hSΛ₁.trans h2) ((configEquivSubtypeProd h2).symm (σ₁, σ₂)))
      = O.φ (restrictConfig hSΛ₁ σ₁)
    rw [restrictConfig_trans hSΛ₁ h2, restrictConfig_configEquivSubtypeProd_symm]
  · change O.φ (restrictConfig (hSΛ₁.trans h1) ((configEquivSubtypeProd h1).symm (σ₁, σ₂)))
      = O.φ (restrictConfig hSΛ₁ σ₁)
    rw [restrictConfig_trans hSΛ₁ h1, restrictConfig_configEquivSubtypeProd_symm]

end Ambient

end IsingModel
