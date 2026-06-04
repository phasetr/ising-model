import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxInterlacing
import IsingModel.AmbientLattice.Monotonicity.PlusScreening
import IsingModel.Concrete.LatticeGraphCorrelation.MinusStateExtremal
import IsingModel.TranslationInvariance.FiniteVolume

/-!
# Translation invariance of the cubic-exhaustion `+`-state functional (Issue #3581 PR 4)

The culmination of the translation-invariance arc: the cubic-exhaustion `+`-state
functional is invariant under lattice translations,
`μ⁺(τ_a φ) = μ⁺(φ)`, via the shifted-cubic cofinal squeeze assembled from the
boundary-condition covariance (#3582), the cubic interlacing geometry (#3583), and
the general-ambient screening (#3584), together with the existing volume
monotonicity.

This file currently provides the **translated observable** infrastructure:

* `LocalMonotoneObservable.vadd` — the lattice translation of a monotone local
  observable, with `vadd_support_subset` and monotonicity preserved.

The squeeze proper (`plusBoxLocalExpectation_vadd_squeeze`,
`plusStateExpectation_vadd_monotone`) is built on top of this.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17, pp. 100–104.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **The lattice translation of a monotone local observable**: support translated
by `a`, observable pulled back through `configVaddEquiv`.  Monotonicity is
preserved (the pullback is a coordinate relabeling). -/
noncomputable def LocalMonotoneObservable.vadd {d : ℕ} (a : Fin d → ℤ)
    (O : LocalMonotoneObservable d) : LocalMonotoneObservable d where
  S := vaddFinset a O.S
  φ := fun σ => O.φ ((configVaddEquiv a O.S).symm σ)
  mono := by
    intro σ σ' hσσ'
    apply O.mono
    intro i
    rw [configVaddEquiv_symm_apply, configVaddEquiv_symm_apply]
    exact hσσ' _

/-- The translated observable's support sits inside the centered cubic box grown by
the lattice radius. -/
theorem LocalMonotoneObservable.vadd_support_subset {d N : ℕ} (a : Fin d → ℤ)
    (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d N) :
    (O.vadd a).S ⊆ cubicBox d (N + latticeRadius a) :=
  (vaddFinset_subset_iff a O.S (cubicBox d N)).mpr hS |>.trans
    (vaddFinset_cubicBox_subset a N)

/-! ## Inner-region interlacing on a common ambient -/

/-- **The translated inner region**: the sites of the common ambient `cubicBox d M`
whose value lies in the translated cubic box `a +ᵥ cubicBox d n`. -/
noncomputable def translatedInner {d : ℕ} (a : Fin d → ℤ) (n M : ℕ) :
    Finset (↑(cubicBox d M) : Type _) :=
  Finset.univ.filter (fun x => (x : Fin d → ℤ) ∈ vaddFinset a (cubicBox d n))

/-- **Upper interlacing of inner regions**: the translated inner region sits inside
the cubic inner region grown by the lattice radius (`vaddFinset_cubicBox_subset`). -/
theorem translatedInner_subset_plusBoxInterior {d : ℕ} (a : Fin d → ℤ) (n M : ℕ) :
    translatedInner a n M ⊆ plusBoxInterior d (n + latticeRadius a) M := by
  intro x hx
  simp only [translatedInner, plusBoxInterior, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx ⊢
  exact vaddFinset_cubicBox_subset a n hx

/-- **Lower interlacing of inner regions**: the cubic inner region sits inside the
translated inner region grown by the lattice radius (`cubicBox_subset_vaddFinset`). -/
theorem plusBoxInterior_subset_translatedInner {d : ℕ} (a : Fin d → ℤ) (k M : ℕ) :
    plusBoxInterior d k M ⊆ translatedInner a (k + latticeRadius a) M := by
  intro x hx
  simp only [plusBoxInterior, translatedInner, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx ⊢
  exact cubicBox_subset_vaddFinset a k hx

/-- **Antitone upper bound** (common ambient): for a monotone observable, the `+`
expectation with the larger cubic inner region is below that with the translated
inner region. -/
theorem gibbsExpectationBC_plusBoxInterior_le_translatedInner {d : ℕ} (a : Fin d → ℤ)
    {n M : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (φ : Config (↑(cubicBox d M) : Type _) → ℝ) (hφ : Monotone φ) :
    gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d M)) β
        (fun _ => J) h (plusBoxInterior d (n + latticeRadius a) M) (plusConfig _) φ
      ≤ gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d M)) β
          (fun _ => J) h (translatedInner a n M) (plusConfig _) φ :=
  gibbsExpectationBC_plus_volume_antitone _ hβ (fun _ => hJ)
    (translatedInner_subset_plusBoxInterior a n M) φ hφ

/-- **Antitone lower bound** (common ambient): for a monotone observable, the `+`
expectation with the translated inner region is below that with the smaller cubic
inner region. -/
theorem gibbsExpectationBC_translatedInner_le_plusBoxInterior {d : ℕ} (a : Fin d → ℤ)
    {k M : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (φ : Config (↑(cubicBox d M) : Type _) → ℝ) (hφ : Monotone φ) :
    gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d M)) β
        (fun _ => J) h (translatedInner a (k + latticeRadius a) M) (plusConfig _) φ
      ≤ gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d M)) β
          (fun _ => J) h (plusBoxInterior d k M) (plusConfig _) φ :=
  gibbsExpectationBC_plus_volume_antitone _ hβ (fun _ => hJ)
    (plusBoxInterior_subset_translatedInner a k M) φ hφ

/-- **The interlacing antitone sandwich** (common ambient): for a monotone
observable and `latticeRadius a ≤ n`, the `+` expectation with the translated inner
region is bracketed between the cubic inner regions `n ± latticeRadius a`,

`E⁺_{n+R} ≤ E⁺_{a +ᵥ n} ≤ E⁺_{n-R}`   (all on the common ambient `cubicBox d M`).

Recentering the middle term to the original observable and passing to the limit
along the cubic exhaustion yields the translation invariance of the `+` state. -/
theorem gibbsExpectationBC_translatedInner_sandwich {d : ℕ} (a : Fin d → ℤ)
    {n M : ℕ} (hRn : latticeRadius a ≤ n) {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (φ : Config (↑(cubicBox d M) : Type _) → ℝ) (hφ : Monotone φ) :
    gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d M)) β
          (fun _ => J) h (plusBoxInterior d (n + latticeRadius a) M) (plusConfig _) φ
        ≤ gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d M)) β
          (fun _ => J) h (translatedInner a n M) (plusConfig _) φ
      ∧ gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d M)) β
          (fun _ => J) h (translatedInner a n M) (plusConfig _) φ
        ≤ gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d M)) β
          (fun _ => J) h (plusBoxInterior d (n - latticeRadius a) M) (plusConfig _) φ := by
  refine ⟨gibbsExpectationBC_plusBoxInterior_le_translatedInner a hβ hJ φ hφ, ?_⟩
  have hk : n - latticeRadius a + latticeRadius a = n := Nat.sub_add_cancel hRn
  have := gibbsExpectationBC_translatedInner_le_plusBoxInterior (a := a)
    (k := n - latticeRadius a) (M := M) (J := J) (h := h) (β := β) hβ hJ φ hφ
  rwa [hk] at this

end Ambient

end IsingModel
