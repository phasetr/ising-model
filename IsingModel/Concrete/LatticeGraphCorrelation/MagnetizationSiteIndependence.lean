import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateCongrN
import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateTranslationGeneralHeadline
import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeMagnetization
import IsingModel.TranslationInvariance.Truncated

/-!
# Site-independence of the `+` magnetization (FV §3.6, Issue #3599)

The `+` magnetization `m⁺(β,h)` does not depend on the site (translation invariance of
the order parameter): `m⁺(a +ᵥ x) = m⁺(x)`.  The proof identifies the translated
single-spin observable with the single-spin observable at the translated site
(`singleSpinObs_vadd_eq`), applies the translation invariance of the `+`-state
functional (`plusStateExpectation_vadd`), and bridges the observable/witnessing-box
mismatch with `plusStateExpectation_congr_obs` (built on `plusStateExpectation_congr_N`).

* `LocalObservable.ext_of_support_eq` — extensionality with a provable support equality.
* `singleSpinObs_vadd_eq` — the translated single spin is the single spin at the
  translated site.
* `plusMagnetization_vadd` — site-independence of `m⁺`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.6.
-/

namespace IsingModel
namespace Ambient
open Finset
variable {d : ℕ}

/-- **Extensionality of `LocalObservable` with a provable support equality**: if the
supports are equal and the spin functions agree after transporting along the support
equality, the observables are equal. -/
theorem LocalObservable.ext_of_support_eq {O₁ O₂ : LocalObservable d} (hS : O₁.S = O₂.S)
    (hφ : ∀ σ : Config (↑O₂.S : Type _), O₁.φ (hS.symm ▸ σ) = O₂.φ σ) : O₁ = O₂ := by
  obtain ⟨S₁, φ₁⟩ := O₁; obtain ⟨S₂, φ₂⟩ := O₂
  dsimp at hS hφ ⊢; subst hS; congr; funext σ; exact hφ σ

/-- **The translated single-spin observable is the single-spin observable at the
translated site**: `vadd a (singleSpinObs x) = singleSpinObs (a +ᵥ x)` (the support
`vaddFinset a {x} = {a +ᵥ x}` and the pulled-back spin value matches the spin at the
translated site). -/
theorem singleSpinObs_vadd_eq (a x : Fin d → ℤ) :
    LocalObservable.vadd a
        (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d)
      = (⟨(singleSpinMonoObs (a +ᵥ x)).S, (singleSpinMonoObs (a +ᵥ x)).φ⟩ :
          LocalObservable d) := by
  have hSeq : (LocalObservable.vadd a
        (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d)).S
      = (⟨(singleSpinMonoObs (a +ᵥ x)).S, (singleSpinMonoObs (a +ᵥ x)).φ⟩ :
          LocalObservable d).S := vaddFinset_singleton a x
  refine LocalObservable.ext_of_support_eq hSeq (fun σ => ?_)
  simp only [LocalObservable.vadd, singleSpinMonoObs]
  rw [configVaddEquiv_symm_apply]
  congr 1

/-- **Observable-congruence of the `+`-state functional**: equal observables (with
possibly different witnessing boxes) give the same value. -/
theorem plusStateExpectation_congr_obs {N₁ N₂ : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    {O₁ O₂ : LocalObservable d} (hO : O₁ = O₂) (hS₁ : O₁.S ⊆ cubicBox d N₁)
    (hS₂ : O₂.S ⊆ cubicBox d N₂) :
    plusStateExpectation J h β O₁ hS₁ = plusStateExpectation J h β O₂ hS₂ := by
  subst hO
  exact plusStateExpectation_congr_N hβ hJ O₁ hS₁ hS₂

/-- The translated site lies in the cubic box of the combined lattice radii. -/
theorem mem_cubicBox_vadd (a x : Fin d → ℤ) :
    (a +ᵥ x) ∈ cubicBox d (latticeRadius x + latticeRadius a) := by
  rw [mem_cubicBox]
  intro i
  have hx := abs_le.mp (abs_coord_le_latticeRadius x i)
  have ha := abs_le.mp (abs_coord_le_latticeRadius a i)
  simp only [vadd_eq_add, Pi.add_apply]
  push_cast
  omega

/-- **Site-independence of the `+` magnetization**: `m⁺(a +ᵥ x) = m⁺(x)`. -/
theorem plusMagnetization_vadd {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (a x : Fin d → ℤ) :
    plusMagnetization (a +ᵥ x) J h β = plusMagnetization x J h β := by
  have hSv : (LocalObservable.vadd a
        (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d)).S ⊆
      cubicBox d (latticeRadius x + latticeRadius a) := by
    rw [singleSpinObs_vadd_eq]
    exact Finset.singleton_subset_iff.mpr (mem_cubicBox_vadd a x)
  have hvadd := plusStateExpectation_vadd (h := h) hβ hJ a
    (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d)
    (singleSpinMonoObs_support_subset x) hSv
  exact (plusStateExpectation_congr_obs hβ hJ (singleSpinObs_vadd_eq a x).symm
    (singleSpinMonoObs_support_subset (a +ᵥ x)) hSv).trans hvadd

end Ambient
end IsingModel
