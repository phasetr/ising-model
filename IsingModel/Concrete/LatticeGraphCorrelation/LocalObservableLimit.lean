import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumePlusState

/-!
# Infinite-volume `+` expectation of a monotone local observable on ℤ^d (Issue #3565)

Generalises the single-spin infinite-volume `+` expectation
(`tendsto_plusBoxSpin_infiniteVolume`) to an arbitrary **monotone local
observable** — a monotone function of the spins on a fixed finite support `S`.
This is the standard `+`-state API: any such observable's `+` boundary expectation
converges along the cubic exhaustion.

* `restrictConfig_monotone` / `restrictConfig_trans` — the restriction map on
  configurations is monotone and transitive (reusable).
* `LocalMonotoneObservable` — a monotone observable on a finite support `S`.
* `plusBoxLocalExpectation` — its `+` box expectation.
* `tendsto_plusBoxLocalObservable_infiniteVolume` — the monotone-convergence
  existence of its infinite-volume `+` expectation.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
§3.4 Theorem 3.17 (the `+` infinite-volume state) and §3.6 Lemma 3.22
(volume monotonicity via FKG).
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **The restriction map on configurations is monotone**: `σ ↦ restrictConfig h σ`
preserves the configuration order (it is a coordinate projection). -/
theorem restrictConfig_monotone {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂) :
    Monotone (restrictConfig h12) := fun _ _ hστ v => hστ (subtypeIncl h12 v)

omit [DecidableEq V] in
/-- **Restriction is transitive**: for `S ⊆ Λ₁ ⊆ Λ₂`, restricting a `↑Λ₂`-config to
`↑S` equals first restricting to `↑Λ₁` then to `↑S`. -/
theorem restrictConfig_trans {S Λ₁ Λ₂ : Finset V} (hS : S ⊆ Λ₁) (h12 : Λ₁ ⊆ Λ₂)
    (σ : (↑Λ₂ : Type _) → Spin) :
    restrictConfig (hS.trans h12) σ = restrictConfig hS (restrictConfig h12 σ) := rfl

/-- **A monotone local observable**: a monotone real function of the spins on a
fixed finite support `S`. -/
structure LocalMonotoneObservable (d : ℕ) where
  /-- The finite support of the observable. -/
  S : Finset (Fin d → ℤ)
  /-- The underlying function of the support spins. -/
  φ : Config (↑S : Type _) → ℝ
  /-- The observable is monotone in the configuration order. -/
  mono : Monotone φ

/-- **The lifted observable** on a box containing the support: `O.φ` precomposed
with the restriction to `O.S`. -/
noncomputable def LocalMonotoneObservable.lift {d : ℕ} (O : LocalMonotoneObservable d)
    {Λ : Finset (Fin d → ℤ)} (hS : O.S ⊆ Λ) : Config (↑Λ : Type _) → ℝ :=
  fun σ => O.φ (restrictConfig hS σ)

omit [DecidableEq V] in
/-- The lifted observable is monotone. -/
theorem LocalMonotoneObservable.lift_monotone {d : ℕ} (O : LocalMonotoneObservable d)
    {Λ : Finset (Fin d → ℤ)} (hS : O.S ⊆ Λ) : Monotone (O.lift hS) :=
  O.mono.comp (restrictConfig_monotone hS)

/-- **The `+` box expectation of a monotone local observable**: the `+` boundary
expectation on `cubicBox d m` (inner box `cubicBox d n`) of the lifted observable. -/
noncomputable def plusBoxLocalExpectation {d : ℕ} (n m : ℕ) (J h β : ℝ)
    (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d m) : ℝ :=
  plusBoxExpectation d n m J h β (O.lift hS)

/-- **Single-step ambient screening of the `+` local expectation**: for `n + 1 ≤ m`
and `O.S ⊆ cubicBox d m`, growing the ambient box by one leaves the `+` local
expectation unchanged.  The lifted observable depends only on the inner
configuration (restriction transitivity). -/
theorem plusBoxLocalExpectation_screening_succ {d : ℕ} {n m : ℕ} (hnm : n + 1 ≤ m)
    {J h β : ℝ} (h12 : cubicBox d m ⊆ cubicBox d (m + 1))
    (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d m) :
    plusBoxLocalExpectation n (m + 1) J h β O (hS.trans h12)
      = plusBoxLocalExpectation n m J h β O hS := by
  unfold plusBoxLocalExpectation plusBoxExpectation
  refine gibbsExpectationBC_cubicBox_succ hnm h12 (O.lift (hS.trans h12)) (O.lift hS)
    (fun σ₁ σ₂ => ?_)
  change O.φ (restrictConfig (hS.trans h12) ((configEquivSubtypeProd h12).symm (σ₁, σ₂)))
    = O.φ (restrictConfig hS σ₁)
  rw [restrictConfig_trans hS h12, restrictConfig_configEquivSubtypeProd_symm]

/-- **The `+` local expectation is bounded below** by the minimum of the
observable over the (finite) support configurations. -/
theorem plusBoxLocalExpectation_ge {d : ℕ} (n m : ℕ) (J h β : ℝ)
    (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d m)
    (huniv : (Finset.univ : Finset (Config (↑O.S : Type _))).Nonempty) :
    Finset.univ.inf' huniv O.φ ≤ plusBoxLocalExpectation n m J h β O hS := by
  refine gibbsExpectationBC_ge_of_forall_ge _ β (fun _ => J) h _ _ (fun σ => ?_)
  exact Finset.inf'_le O.φ (Finset.mem_univ (restrictConfig hS σ))

/-- **The screened `+` local expectation sequence is antitone**: for `O.S ⊆
cubicBox d N`, `k ↦ plusBoxLocalExpectation (N+k) (N+k+1) … O` decreases (growing the
free region pushes the `+` boundary away; FV Lemma 3.22 + the ambient screening). -/
theorem plusBoxLocalExpectation_infiniteVolume_antitone {d N : ℕ} {J h β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d N) :
    Antitone (fun k => plusBoxLocalExpectation (N + k) (N + k + 1) J h β O
      (hS.trans (cubicBox_mono d (by omega)))) := by
  apply antitone_nat_of_succ_le
  intro k
  refine le_trans
    (plusBoxExpectation_antitone_interior d (show N + k ≤ N + k + 1 by omega) hβ hJ
      (O.lift (hS.trans (cubicBox_mono d (show N ≤ N + k + 2 by omega))))
      (O.lift_monotone _)) ?_
  exact le_of_eq (plusBoxLocalExpectation_screening_succ
    (show N + k + 1 ≤ N + k + 1 by omega) (cubicBox_mono d (by omega)) O
    (hS.trans (cubicBox_mono d (show N ≤ N + k + 1 by omega))))

/-- **The infinite-volume `+` expectation of a monotone local observable exists**
(the standard `+`-state API, Issue #3565): for `O.S ⊆ cubicBox d N`, the screened
`+` local expectations converge (decreasingly) to their infimum,

`plusBoxLocalExpectation (N+k) (N+k+1) … O  →  ⨅ k, plusBoxLocalExpectation …`   as `k → ∞`.

The sequence is antitone (`plusBoxLocalExpectation_infiniteVolume_antitone`) and
bounded below (`plusBoxLocalExpectation_ge`), so `tendsto_atTop_ciInf` applies. -/
theorem tendsto_plusBoxLocalObservable_infiniteVolume {d N : ℕ} {J h β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d N) :
    Tendsto (fun k => plusBoxLocalExpectation (N + k) (N + k + 1) J h β O
        (hS.trans (cubicBox_mono d (by omega)))) atTop
      (nhds (⨅ k, plusBoxLocalExpectation (N + k) (N + k + 1) J h β O
        (hS.trans (cubicBox_mono d (by omega))))) := by
  haveI : Nonempty (Config (↑O.S : Type _)) := inferInstance
  refine tendsto_atTop_ciInf
    (plusBoxLocalExpectation_infiniteVolume_antitone hβ hJ O hS)
    ⟨Finset.univ.inf' Finset.univ_nonempty O.φ, ?_⟩
  rintro y ⟨k, rfl⟩
  exact plusBoxLocalExpectation_ge (N + k) (N + k + 1) J h β O _ Finset.univ_nonempty

end Ambient

end IsingModel
