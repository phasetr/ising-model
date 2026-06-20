import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic

/-!
# Separating the first coordinate of a constant `piFinset` sum (GJ §18.5)

The rooted-tree Kotecky--Preiss leaf-peel induction sums over polymer sequences
`ω : Fin (n+1) → X` ranging in a constant `Fintype.piFinset (fun _ => s)`, peeling
one coordinate at a time.  This file provides the basic coordinate-separation step
for the first coordinate: the sum over the constant `piFinset` on `Fin (n+1)`
factors as a double sum over the first value and the remaining `Fin n`-tuple, glued
by `Fin.cons`.

`sum_piFinset_const_succ`:
`∑_{ω ∈ piFinset (fun _ : Fin (n+1) => s)} f ω
   = ∑_{x ∈ s} ∑_{ω' ∈ piFinset (fun _ : Fin n => s)} f (Fin.cons x ω')`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

/-- **First-coordinate separation of a constant `piFinset` sum.**  The sum of `f`
over the constant `piFinset` on `Fin (n+1)` equals the double sum over the first
value `x ∈ s` and the remaining `Fin n`-tuple, glued by `Fin.cons`.  The
`piFinset` is the image of `s ×ˢ piFinset` under `Fin.cons`, an injection. -/
theorem sum_piFinset_const_succ {X : Type*} {n : ℕ} (s : Finset X)
    (f : (Fin (n + 1) → X) → ℝ) :
    (∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => s), f ω)
      = ∑ x ∈ s, ∑ ω' ∈ Fintype.piFinset (fun _ : Fin n => s), f (Fin.cons x ω') := by
  have hbij :
      Fintype.piFinset (fun _ : Fin (n + 1) => s)
        = (s ×ˢ Fintype.piFinset (fun _ : Fin n => s)).map
            (Fin.consEquiv (fun _ : Fin (n + 1) => X)).toEmbedding := by
    ext ω
    simp only [Finset.mem_map, Finset.mem_product, Fintype.mem_piFinset,
      Equiv.coe_toEmbedding]
    constructor
    · intro hω
      refine ⟨(ω 0, Fin.tail ω), ⟨hω 0, fun i => hω (Fin.succ i)⟩, ?_⟩
      simp [Fin.consEquiv, Fin.cons_self_tail]
    · rintro ⟨⟨x, ω'⟩, ⟨hx, hω'⟩, rfl⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [Fin.consEquiv] using hx
      · simpa [Fin.consEquiv] using hω' j
  rw [hbij, Finset.sum_map, Finset.sum_product]
  rfl

end IsingModel
