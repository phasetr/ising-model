import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateTranslation

/-!
# Cubic-box interlacing geometry and `+` boundary covariance (Issue #3581 PR 2)

The translation toolkit for the cubic-exhaustion `±`-state squeeze.  The centered
cubic boxes `cubicBox d n` are not preserved by a lattice translation
`a : Fin d → ℤ` (translation moves the box off-center), but they **interlace** with
their translates up to an index shift by `latticeRadius a = max_i |a i|`:

* `vaddFinset_cubicBox_subset` — `a +ᵥ cubicBox d n ⊆ cubicBox d (n + R)`.
* `cubicBox_subset_vaddFinset` — `cubicBox d n ⊆ a +ᵥ cubicBox d (n + R)`.

Together with the `+` boundary translation covariance
(`gibbsExpectationBC_plus_vaddFinset_eq`, the `plusConfig` specialisation of
`gibbsExpectationBC_vaddFinset_eq`), this interlacing is what lets the cubic-box
limit of the `±`-state functional be shown translation-invariant (a squeeze, not a
pointwise identity).

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
§3.4 (translation invariance of the infinite-volume states).
-/

universe u v

namespace IsingModel

namespace Ambient

open Finset

/-- **The lattice radius of a translation**: `max_i |a i|`, the index shift needed
to interlace `cubicBox` with its translate by `a`. -/
def latticeRadius {d : ℕ} (a : Fin d → ℤ) : ℕ :=
  Finset.univ.sup (fun i => (a i).natAbs)

/-- The lattice radius of the zero translation is `0`. -/
@[simp] theorem latticeRadius_zero {d : ℕ} : latticeRadius (0 : Fin d → ℤ) = 0 := by
  simp [latticeRadius]

/-- The lattice radius is invariant under negation. -/
@[simp] theorem latticeRadius_neg {d : ℕ} (a : Fin d → ℤ) :
    latticeRadius (-a) = latticeRadius a := by
  simp [latticeRadius]

/-- Each coordinate of `a` is bounded by the lattice radius. -/
theorem abs_coord_le_latticeRadius {d : ℕ} (a : Fin d → ℤ) (i : Fin d) :
    |a i| ≤ (latticeRadius a : ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)

/-- **Upper interlacing**: translating a centered box by `a` lands inside the
centered box grown by `latticeRadius a`. -/
theorem vaddFinset_cubicBox_subset {d : ℕ} (a : Fin d → ℤ) (n : ℕ) :
    vaddFinset a (cubicBox d n) ⊆ cubicBox d (n + latticeRadius a) := by
  intro x hx
  rw [mem_vaddFinset] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [mem_cubicBox] at hy ⊢
  intro i
  have hR := abs_coord_le_latticeRadius a i
  have hyi := hy i
  have hadd : (a +ᵥ y) i = a i + y i := by
    rw [vadd_eq_add]; rfl
  rw [hadd]
  rw [abs_le] at hR
  push_cast
  omega

/-- **Lower interlacing**: every centered box sits inside the translate (by `a`) of
the centered box grown by `latticeRadius a`. -/
theorem cubicBox_subset_vaddFinset {d : ℕ} (a : Fin d → ℤ) (n : ℕ) :
    cubicBox d n ⊆ vaddFinset a (cubicBox d (n + latticeRadius a)) := by
  intro x hx
  rw [mem_cubicBox] at hx
  rw [mem_vaddFinset]
  refine ⟨x - a, ?_, ?_⟩
  · rw [mem_cubicBox]
    intro i
    have hR := abs_coord_le_latticeRadius a i
    have hxi := hx i
    have hsub : (x - a) i = x i - a i := rfl
    rw [hsub]
    rw [abs_le] at hR
    push_cast
    omega
  · rw [vadd_eq_add]
    ext i
    simp [Pi.add_apply, Pi.sub_apply]

/-- **`+` boundary translation covariance**: the `plusConfig` specialisation of
`gibbsExpectationBC_vaddFinset_eq`.  Since the all-`+` boundary condition is
translation-invariant (`plusConfig_configVaddEquiv`), the `+` boundary Gibbs
expectation on the translated volume equals that on the original volume at the
pulled-back observable. -/
theorem gibbsExpectationBC_plus_vaddFinset_eq {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G] (t : T) (Ω : Finset V)
    [Fintype (inducedGraph G Ω).edgeSet]
    [Fintype (inducedGraph G (vaddFinset t Ω)).edgeSet]
    (β J h : ℝ) (Λ : Finset (↑Ω : Type _)) (F : Config (↑Ω : Type _) → ℝ) :
    gibbsExpectationBC (inducedGraph G (vaddFinset t Ω)) β (fun _ => J) h
        (Λ.map (vaddSubtypeEquiv t Ω).toEmbedding) (plusConfig (↑(vaddFinset t Ω) : Type _))
        (fun σ' => F ((configVaddEquiv t Ω).symm σ'))
      = gibbsExpectationBC (inducedGraph G Ω) β (fun _ => J) h Λ
          (plusConfig (↑Ω : Type _)) F := by
  rw [← plusConfig_configVaddEquiv t Ω, gibbsExpectationBC_vaddFinset_eq G t Ω β J h Λ]

end Ambient

end IsingModel
