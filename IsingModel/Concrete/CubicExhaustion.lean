import IsingModel.AmbientLattice
import IsingModel.Lattice

/-!
# Cubic exhaustion of the integer lattice `Fin d → ℤ`

We equip the vertex type `Fin d → ℤ` (the `d`-dimensional integer
lattice used by `IsingModel.latticeGraph`) with a concrete
`Ambient.Exhaustion` built from two-sided cubic boxes
`[-n, n]^d`. This is the first concrete `Ambient.Exhaustion`
instance on `ℤ^d`, and makes `correlationInfinite (latticeGraph d)
(cubicExhaustion d) p A` an explicit object on the physical
`d`-dimensional Ising lattice.

## Main definitions

* `cubicBox d n : Finset (Fin d → ℤ)` — the finite set
  `{x : Fin d → ℤ | ∀ i, -n ≤ x i ≤ n}`, realised as
  `Fintype.piFinset` of coordinatewise `Finset.Icc (-↑n) ↑n`.
* `cubicExhaustion d : Ambient.Exhaustion (Fin d → ℤ)` — the
  exhaustion whose stage-`n` volume is `cubicBox d n`.

## Main theorems

* `mem_cubicBox` — membership characterisation
  `x ∈ cubicBox d n ↔ ∀ i, -n ≤ x i ∧ x i ≤ n`.
* `cubicBox_mono` — `m ≤ n → cubicBox d m ⊆ cubicBox d n`.
* `cubicBox_exhaust` — any finite `A ⊆ Fin d → ℤ` is contained in
  some `cubicBox d N`.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6, p. 64.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **Cubic box in `Fin d → ℤ`**: the finite set
`{x : Fin d → ℤ | ∀ i, -n ≤ x i ≤ n}` as a `Finset`. Built as the
dependent product of coordinate intervals
`Finset.Icc (-↑n : ℤ) n` via `Fintype.piFinset`. -/
noncomputable def cubicBox (d : ℕ) (n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n)

/-- **Membership in `cubicBox`**: `x ∈ cubicBox d n` iff every
coordinate lies in `Icc (-n) n`. -/
theorem mem_cubicBox {d n : ℕ} {x : Fin d → ℤ} :
    x ∈ cubicBox d n ↔ ∀ i, -(n : ℤ) ≤ x i ∧ x i ≤ n := by
  unfold cubicBox
  rw [Fintype.mem_piFinset]
  simp [Finset.mem_Icc]

/-- **Monotonicity of `cubicBox`**: if `m ≤ n`, the cube at level
`m` is contained in the cube at level `n`. -/
theorem cubicBox_mono (d : ℕ) : Monotone (cubicBox d) := by
  intro m n hmn x hx
  rw [mem_cubicBox] at hx ⊢
  intro i
  obtain ⟨hle, hge⟩ := hx i
  have hmn' : (m : ℤ) ≤ n := by exact_mod_cast hmn
  refine ⟨?_, ?_⟩
  · linarith [hle, hmn']
  · linarith [hge, hmn']

/-- **Exhaustion property for `cubicBox`**: any finite set
`A ⊆ Fin d → ℤ` is contained in some sufficiently large cube. The
witness `N` is the maximum absolute coordinate value across all
points of `A`. -/
theorem cubicBox_exhaust (d : ℕ) (A : Finset (Fin d → ℤ)) :
    ∃ N, ∀ n ≥ N, A ⊆ cubicBox d n := by
  classical
  -- The set of absolute coordinates `|a i|` for `a ∈ A`, `i : Fin d`.
  set absSet : Finset ℕ :=
    A.biUnion (fun a => (Finset.univ : Finset (Fin d)).image
      (fun i => (a i).natAbs))
    with habsSet_def
  by_cases hne : absSet.Nonempty
  · refine ⟨absSet.max' hne, ?_⟩
    intro n hn a ha
    rw [mem_cubicBox]
    intro i
    have hmem : (a i).natAbs ∈ absSet := by
      rw [habsSet_def]
      exact Finset.mem_biUnion.mpr ⟨a, ha,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    have hle : (a i).natAbs ≤ absSet.max' hne := Finset.le_max' _ _ hmem
    have hleN : (a i).natAbs ≤ n := hle.trans hn
    have habs : |a i| ≤ (n : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hleN
    have := abs_le.mp habs
    refine ⟨this.1, this.2⟩
  · -- `absSet` empty; refine ⟨0, _⟩ and conclude by exfalso via `a, i`.
    refine ⟨0, ?_⟩
    intro n _ a ha
    rw [mem_cubicBox]
    intro i
    exfalso
    apply hne
    refine ⟨(a i).natAbs, ?_⟩
    rw [habsSet_def]
    exact Finset.mem_biUnion.mpr ⟨a, ha,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

/-- **Concrete cubic exhaustion of `Fin d → ℤ`**: stage-`n` volume is
the cube `[-n, n]^d`. Satisfies monotonicity and covers every finite
subset of `Fin d → ℤ`, so furnishes an `Ambient.Exhaustion` instance.
This is the first concrete exhaustion on the physical integer lattice,
enabling `correlationInfinite (latticeGraph d) (cubicExhaustion d)`
etc. as explicit objects. -/
noncomputable def cubicExhaustion (d : ℕ) : Ambient.Exhaustion (Fin d → ℤ) where
  volume := cubicBox d
  mono := cubicBox_mono d
  exhaust := cubicBox_exhaust d

end Ambient

end IsingModel
