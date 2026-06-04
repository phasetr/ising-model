import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxScreening
import IsingModel.AmbientLattice.Monotonicity.InducedWeightFactor

/-!
# Configuration-split decomposition for the cubic-box screening (Issue #3565)

The configuration-side ingredients for the nearest-neighbour screening of the
cubic-box `+` state.  Under the configuration splitting
`configEquivSubtypeProd (cubicBox d m ⊆ cubicBox d (m+1))`, a configuration on the
larger box is identified with a pair `(σ₁, σ₂)` of a configuration on `cubicBox d m`
and one on the shell `cubicBox d (m+1) ∖ cubicBox d m`.

* `restrictConfig_plusConfig` — restricting the all-`+` configuration is again
  all-`+`.
* `agreesOff_plus_configEquiv_iff` — the boundary-agreement of the recombined
  configuration off `cubicBox d n` splits into the boundary-agreement of `σ₁` off
  `cubicBox d n` together with `σ₂` being all-`+` (the frozen shell).

These let the `+` box partition function and numerator factor over the box-`m`
ones times a shell constant, which cancels in the normalised expectation — the
screening (final assembly, Issue #3565).

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
Lemma 3.22, §6.
-/

namespace IsingModel

namespace Ambient

open Finset

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **Restricting the all-`+` configuration is all-`+`**: for `Λ₁ ⊆ Λ₂`,
`restrictConfig h12 (plusConfig ↑Λ₂) = plusConfig ↑Λ₁`. -/
theorem restrictConfig_plusConfig {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂) :
    restrictConfig h12 (plusConfig (↑Λ₂ : Type _)) = plusConfig (↑Λ₁ : Type _) := by
  rfl

/-- **Membership in `plusBoxInterior`**: `j ∈ plusBoxInterior d n m` iff the
underlying lattice point lies in `cubicBox d n`. -/
theorem mem_plusBoxInterior {d n m : ℕ} {j : (↑(cubicBox d m) : Type _)} :
    j ∈ plusBoxInterior d n m ↔ (j : Fin d → ℤ) ∈ cubicBox d n := by
  simp only [plusBoxInterior, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Boundary-agreement decomposition under the configuration split** (cubic box):
for `n ≤ m`, a recombined configuration `(configEquivSubtypeProd h12).symm (σ₁, σ₂)`
on `cubicBox d (m+1)` agrees with `+` off `cubicBox d n` iff `σ₁` agrees with `+`
off `cubicBox d n` (on `cubicBox d m`) and `σ₂` is all-`+` on the shell.

The split site `i` of `cubicBox d (m+1)` is treated by cases on `i.val ∈ cubicBox d m`:
inside the box it is the `σ₁` component (via `restrictConfig`/the equiv),
on the shell it is the `σ₂` component and automatically lies outside `cubicBox d n`
(as `cubicBox d n ⊆ cubicBox d m`). -/
theorem agreesOff_plus_configEquiv_iff {d n m : ℕ} (hnm : n ≤ m)
    (h12 : cubicBox d m ⊆ cubicBox d (m + 1))
    (σ₁ : (↑(cubicBox d m) : Type _) → Spin)
    (σ₂ : {x : (↑(cubicBox d (m + 1)) : Type _) // x.val ∉ cubicBox d m} → Spin) :
    agreesOff (plusBoxInterior d n (m + 1)) (plusConfig _)
        ((configEquivSubtypeProd h12).symm (σ₁, σ₂))
      ↔ agreesOff (plusBoxInterior d n m) (plusConfig _) σ₁
        ∧ (∀ v, σ₂ v = Spin.up) := by
  classical
  have hres : ∀ k : (↑(cubicBox d m) : Type _),
      ((configEquivSubtypeProd h12).symm (σ₁, σ₂)) ⟨(k : Fin d → ℤ), h12 k.2⟩ = σ₁ k := by
    intro k
    have hr := congrFun (restrictConfig_configEquivSubtypeProd_symm h12 σ₁ σ₂) k
    simpa only [restrictConfig, subtypeIncl] using hr
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun v => ?_⟩
    · have hjn : (j : Fin d → ℤ) ∉ cubicBox d n := fun hh => hj (mem_plusBoxInterior.mpr hh)
      have hjM : (j : Fin d → ℤ) ∈ cubicBox d (m + 1) := h12 j.2
      have hnotI : (⟨(j : Fin d → ℤ), hjM⟩ : (↑(cubicBox d (m + 1)) : Type _))
          ∉ plusBoxInterior d n (m + 1) := fun hh =>
        hjn ((mem_plusBoxInterior (j := (⟨(j : Fin d → ℤ), hjM⟩ :
          (↑(cubicBox d (m + 1)) : Type _)))).mp hh)
      have := h ⟨(j : Fin d → ℤ), hjM⟩ hnotI
      rwa [hres j] at this
    · have hvn : (v.val : Fin d → ℤ) ∉ cubicBox d n := fun hvn =>
        v.2 (cubicBox_mono d hnm hvn)
      have hnotI : v.val ∉ plusBoxInterior d n (m + 1) :=
        fun hh => hvn ((mem_plusBoxInterior (j := v.val)).mp hh)
      have := h v.val hnotI
      rwa [configEquivSubtypeProd_symm_apply_compl h12 σ₁ σ₂ v] at this
  · rintro ⟨h1, h2⟩ i hi
    have hin : (i : Fin d → ℤ) ∉ cubicBox d n := fun hh => hi (mem_plusBoxInterior.mpr hh)
    by_cases him : (i : Fin d → ℤ) ∈ cubicBox d m
    · set i₁ : (↑(cubicBox d m) : Type _) := ⟨(i : Fin d → ℤ), him⟩ with hi₁
      have hnotI : i₁ ∉ plusBoxInterior d n m :=
        fun hh => hin ((mem_plusBoxInterior (j := i₁)).mp hh)
      have hval := h1 ⟨(i : Fin d → ℤ), him⟩ hnotI
      have hkey := hres ⟨(i : Fin d → ℤ), him⟩
      simp only [Subtype.coe_eta] at hkey
      rw [show i = (⟨(i : Fin d → ℤ), h12 him⟩ : (↑(cubicBox d (m + 1)) : Type _)) from
        Subtype.ext rfl, hkey]
      exact hval
    · rw [configEquivSubtypeProd_symm_apply_compl h12 σ₁ σ₂ ⟨i, him⟩]
      exact h2 _

end Ambient

end IsingModel
