import IsingModel.ClusterExpansion.PiFinsetSeparation

/-!
# Separating an arbitrary coordinate of a constant `piFinset` sum (GJ §18.5)

The rooted-tree Kotecky--Preiss leaf-peel induction peels an arbitrary leaf vertex
`p : Fin (n+1)` (not necessarily the root index `0`).  This generalises
`sum_piFinset_const_succ` to an arbitrary pivot `p`, gluing the separated value and
the remaining tuple by `Fin.insertNth`.

`sum_piFinset_const_insertNth`:
`∑_{ω ∈ piFinset (fun _ : Fin (n+1) => s)} f ω
   = ∑_{x ∈ s} ∑_{ω' ∈ piFinset (fun _ : Fin n => s)} f (p.insertNth x ω')`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

/-- **Arbitrary-coordinate separation of a constant `piFinset` sum.**  For a pivot
`p : Fin (n+1)`, the sum of `f` over the constant `piFinset` equals the double sum
over the value `x ∈ s` at coordinate `p` and the remaining `Fin n`-tuple, glued by
`Fin.insertNth`.  The `piFinset` is the image of `s ×ˢ piFinset` under the injection
`p.insertNth`. -/
theorem sum_piFinset_const_insertNth {X : Type*} {n : ℕ} (p : Fin (n + 1))
    (s : Finset X) (f : (Fin (n + 1) → X) → ℝ) :
    (∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => s), f ω)
      = ∑ x ∈ s, ∑ ω' ∈ Fintype.piFinset (fun _ : Fin n => s), f (p.insertNth x ω') := by
  have hbij :
      Fintype.piFinset (fun _ : Fin (n + 1) => s)
        = (s ×ˢ Fintype.piFinset (fun _ : Fin n => s)).map
            (Fin.insertNthEquiv (fun _ : Fin (n + 1) => X) p).toEmbedding := by
    ext ω
    simp only [Finset.mem_map, Finset.mem_product, Fintype.mem_piFinset,
      Equiv.coe_toEmbedding]
    constructor
    · intro hω
      refine ⟨(ω p, Fin.removeNth p ω), ⟨hω p, fun i => hω (p.succAbove i)⟩, ?_⟩
      simp [Fin.insertNthEquiv]
    · rintro ⟨⟨x, ω'⟩, ⟨hx, hω'⟩, rfl⟩
      rw [Fin.forall_iff_succAbove p]
      refine ⟨?_, fun j => ?_⟩
      · simpa [Fin.insertNthEquiv, Fin.insertNth_apply_same] using hx
      · simpa [Fin.insertNthEquiv, Fin.insertNth_apply_succAbove] using hω' j
  rw [hbij, Finset.sum_map, Finset.sum_product]
  rfl

end IsingModel
