import IsingModel.Concrete.CubicExhaustion

/-!
# Surface (ℓ¹-sphere) cardinality bound on `ℤ^d`

The number of lattice points at exact ℓ¹ distance `r` from the origin in `ℤ^d`
grows only like `r^{d-1}` (a *surface*, not volume, count): projecting away the
last coordinate is two-to-one onto the `(d-1)`-cube of radius `r`, since the last
coordinate is determined up to sign by the remaining ones.

This is the input that makes the contraction factor of GJ §17.8 tend to zero
under merely *polynomial* decay (`O(r^{d-1})` boundary terms each of size
`o(r^{-(d-1)})`), where the cruder volume bound `O(r^d)` would not suffice.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.8, pp. 316–318.
-/

namespace IsingModel.Ambient

open Finset

/-- **ℓ¹-sphere surface cardinality bound**: the number of lattice points in
`ℤ^{m+1}` at exact ℓ¹ distance `r` from the origin is at most `2·(2r+1)^m`.

Realized via the injection `x ↦ (sign (x (last)), Fin.init x)` into
`Bool × cubicBox m r`: the first `m` coordinates lie in the `m`-cube of radius
`r` (each `|xᵢ| ≤ ∑ⱼ|xⱼ| = r`), and the last coordinate is recovered from them
(its absolute value is `r − ∑_{init}|xⱼ|`) together with its sign. -/
theorem latticeSphere_card_le (m r : ℕ) :
    ((cubicBox (m + 1) r).filter
        (fun x => IsingModel.latticeDistance (m + 1) 0 x = r)).card
      ≤ 2 * (2 * r + 1) ^ m := by
  classical
  -- The last-coordinate absolute value as a sum identity, for any sphere point.
  have hsplit : ∀ x : Fin (m + 1) → ℤ,
      IsingModel.latticeDistance (m + 1) 0 x = r →
        (x (Fin.last m)).natAbs
          = r - ∑ i : Fin m, (x (Fin.castSucc i)).natAbs := by
    intro x hx
    have hsum : (∑ i : Fin m, (x (Fin.castSucc i)).natAbs) + (x (Fin.last m)).natAbs = r := by
      have h := hx
      unfold IsingModel.latticeDistance at h
      rw [Fin.sum_univ_castSucc] at h
      simpa only [Pi.zero_apply, zero_sub, Int.natAbs_neg] using h
    omega
  -- The whole-sum bound, used for membership in the `(m)`-cube.
  have hcoord : ∀ x : Fin (m + 1) → ℤ,
      IsingModel.latticeDistance (m + 1) 0 x = r →
        ∀ i : Fin m, (x (Fin.castSucc i)).natAbs ≤ r := by
    intro x hx i
    have hle : (x (Fin.castSucc i)).natAbs
        ≤ ∑ j : Fin (m + 1), (x j).natAbs :=
      Finset.single_le_sum (f := fun j => (x j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ _)
    have heq : (∑ j : Fin (m + 1), (x j).natAbs) = r := by
      have h := hx
      unfold IsingModel.latticeDistance at h
      simpa only [Pi.zero_apply, zero_sub, Int.natAbs_neg] using h
    omega
  have hcard_t :
      ((Finset.univ : Finset Bool) ×ˢ cubicBox m r).card = 2 * (2 * r + 1) ^ m := by
    rw [Finset.card_product, card_cubicBox, Finset.card_univ, Fintype.card_bool]
  rw [← hcard_t]
  refine Finset.card_le_card_of_injOn
    (fun x => (decide (0 ≤ x (Fin.last m)), Fin.init x)) ?_ ?_
  · -- maps the sphere into `Bool ×ˢ cubicBox m r`
    intro x hx
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hx
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, true_and]
    rw [mem_cubicBox]
    intro i
    have hi : (x (Fin.castSucc i)).natAbs ≤ r := hcoord x hx.2 i
    have habs : |x (Fin.castSucc i)| ≤ (r : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hi
    rw [abs_le] at habs
    exact ⟨by simpa [Fin.init] using habs.1, by simpa [Fin.init] using habs.2⟩
  · -- injective on the sphere
    intro x hx y hy hxy
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    obtain ⟨_, hxd⟩ := hx
    obtain ⟨_, hyd⟩ := hy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨hsign, hinit⟩ := hxy
    -- last coordinates have equal absolute value (the init sums agree)
    have habs_eq : (x (Fin.last m)).natAbs = (y (Fin.last m)).natAbs := by
      rw [hsplit x hxd, hsplit y hyd]
      have : ∀ i : Fin m, (x (Fin.castSucc i)).natAbs = (y (Fin.castSucc i)).natAbs := by
        intro i
        have := congrFun hinit i
        simp only [Fin.init] at this
        rw [this]
      rw [Finset.sum_congr rfl (fun i _ => this i)]
    -- equal sign
    have hsign' : (0 ≤ x (Fin.last m)) ↔ (0 ≤ y (Fin.last m)) := by
      constructor <;> intro h
      · by_contra hc; rw [decide_eq_decide] at hsign; exact hc (hsign.mp h)
      · by_contra hc; rw [decide_eq_decide] at hsign; exact hc (hsign.mpr h)
    have hlast : x (Fin.last m) = y (Fin.last m) := by omega
    -- reconstruct via `Fin.snoc (Fin.init ·) (· (last))`
    rw [← Fin.snoc_init_self x, ← Fin.snoc_init_self y, hinit, hlast]

end IsingModel.Ambient
