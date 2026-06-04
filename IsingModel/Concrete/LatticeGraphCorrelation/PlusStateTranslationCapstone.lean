import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateTranslationInvariance
import IsingModel.Concrete.IntLattice

/-!
# Recentering covariance for the translation-invariance squeeze (Issue #3581 PR 4b)

The recentering step of the translation-invariance squeeze: the `+` expectation of
the translated observable `O.vadd a` with the translated inner region on the
centered cubic ambient equals the `+` expectation of `O` with the centered inner
region on the **translated** ambient, by the boundary-condition covariance applied
with `t = -a` (which keeps the cubic box as `Ω`, sending the *translated* box to the
`vaddFinset t Ω` side, so no ambient-equality transport is needed).

* `innerOf` — the inner region of an ambient given by a site set.
* `translatedInner_map_vaddSubtypeEquiv` — the translated inner region pulls back to
  the centered inner region on the translated ambient.
* `vadd_lift_comp_configVaddEquiv_symm` — the translated observable's lift composed
  with the inverse translation equals `O`'s lift on the translated ambient.
* `gibbsExpectationBC_translatedInner_recenter` — the recentering identity.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17, pp. 100–104.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **The inner region of an ambient `Ω` given by a site set `I`**: the sites of `Ω`
whose value lies in `I`. -/
noncomputable def innerOf {d : ℕ} (Ω : Finset (Fin d → ℤ)) (I : Finset (Fin d → ℤ)) :
    Finset (↑Ω : Type _) :=
  Finset.univ.filter (fun x => (x : Fin d → ℤ) ∈ I)

/-- The translated inner region is the `innerOf` form for the translated cubic box. -/
theorem translatedInner_eq_innerOf {d : ℕ} (a : Fin d → ℤ) (n M : ℕ) :
    translatedInner a n M = innerOf (cubicBox d M) (vaddFinset a (cubicBox d n)) := rfl

/-- **The translated inner region pulls back to the centered inner region**: mapping
`translatedInner a n M` (in `↑(cubicBox d M)`) by `vaddSubtypeEquiv (-a)` lands on
`innerOf (vaddFinset (-a) (cubicBox d M)) (cubicBox d n)`. -/
theorem translatedInner_map_vaddSubtypeEquiv {d : ℕ} (a : Fin d → ℤ) (n M : ℕ) :
    (translatedInner a n M).map (vaddSubtypeEquiv (-a) (cubicBox d M)).toEmbedding
      = innerOf (vaddFinset (-a) (cubicBox d M)) (cubicBox d n) := by
  ext z
  simp only [translatedInner, innerOf, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
    true_and, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [vaddSubtypeEquiv_apply_coe]
    obtain ⟨y, hy, hxy⟩ := (mem_vaddFinset _ _ _).mp hx
    rw [← hxy, neg_vadd_vadd]
    exact hy
  · intro hz
    have hzM : (a +ᵥ (z : Fin d → ℤ)) ∈ cubicBox d M := by
      obtain ⟨w, hw, hwz⟩ := (mem_vaddFinset _ _ _).mp z.2
      rw [← hwz, ← add_vadd, add_neg_cancel, zero_vadd]
      exact hw
    refine ⟨⟨a +ᵥ (z : Fin d → ℤ), hzM⟩, ?_, ?_⟩
    · rw [mem_vaddFinset]
      exact ⟨z.val, hz, rfl⟩
    · apply Subtype.ext
      rw [vaddSubtypeEquiv_apply_coe, neg_vadd_vadd]

/-- **The translated observable's lift, recentered**: composing `(O.vadd a).lift`
on the cubic ambient with the inverse translation `configVaddEquiv (-a)` yields
`O`'s lift on the translated ambient. -/
theorem vadd_lift_comp_configVaddEquiv_symm {d : ℕ} {a : Fin d → ℤ} {M : ℕ}
    (O : LocalMonotoneObservable d) (hSM : (O.vadd a).S ⊆ cubicBox d M)
    (hSΩ : O.S ⊆ vaddFinset (-a) (cubicBox d M)) :
    (fun σ' => (O.vadd a).lift hSM ((configVaddEquiv (-a) (cubicBox d M)).symm σ'))
      = O.lift hSΩ := by
  funext σ'
  simp only [LocalMonotoneObservable.lift, LocalMonotoneObservable.vadd]
  congr 1
  funext i
  rw [configVaddEquiv_symm_apply]
  change (restrictConfig hSM ((configVaddEquiv (-a) (cubicBox d M)).symm σ'))
      (vaddSubtypeEquiv a O.S i) = restrictConfig hSΩ σ' i
  rw [restrictConfig, Function.comp_apply, configVaddEquiv_symm_apply,
    restrictConfig, Function.comp_apply]
  congr 1
  apply Subtype.ext
  change -a +ᵥ (a +ᵥ (i : Fin d → ℤ)) = (i : Fin d → ℤ)
  rw [neg_vadd_vadd]

/-- **The recentering identity**: the `+` expectation of the translated observable
`O.vadd a` with the translated inner region on the centered cubic ambient equals the
`+` expectation of `O` with the centered inner region on the translated ambient (via
the boundary-condition covariance with `t = -a`). -/
theorem gibbsExpectationBC_translatedInner_recenter {d : ℕ} (a : Fin d → ℤ) {n M : ℕ}
    {J h β : ℝ} (O : LocalMonotoneObservable d) (hSM : (O.vadd a).S ⊆ cubicBox d M)
    (hSΩ : O.S ⊆ vaddFinset (-a) (cubicBox d M)) :
    gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d M)) β
        (fun _ => J) h (translatedInner a n M) (plusConfig _) ((O.vadd a).lift hSM)
      = gibbsExpectationBC
          (inducedGraph (IsingModel.latticeGraph d) (vaddFinset (-a) (cubicBox d M)))
          β (fun _ => J) h (innerOf (vaddFinset (-a) (cubicBox d M)) (cubicBox d n))
          (plusConfig _) (O.lift hSΩ) := by
  rw [← gibbsExpectationBC_vaddFinset_eq (IsingModel.latticeGraph d) (-a) (cubicBox d M)
      β J h (translatedInner a n M) (plusConfig _) ((O.vadd a).lift hSM),
    plusConfig_configVaddEquiv, translatedInner_map_vaddSubtypeEquiv,
    vadd_lift_comp_configVaddEquiv_symm O hSM hSΩ]

end Ambient

end IsingModel
