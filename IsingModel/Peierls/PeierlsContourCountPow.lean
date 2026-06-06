import IsingModel.Peierls.PeierlsContourCount

/-!
# The Peierls contour count as a clean power bound (FV §3.7.2)

Absorbing the polynomial factor `r ≤ 2^r`, the Peierls contour count `r · (2·2)^{2r} = r · 16^r` is
at most `32^r`. As a real-valued bound on the number of size-`r` droplets, this is exactly the
`hcount : ∀ ℓ, #{C : g C = ℓ} ≤ M^ℓ` hypothesis (with `M = 32`) of the geometric tail estimate
`sum_pow_le_geometric_tail_of_count`.

* `peierls_contour_count_pow` — `#{S ∈ D : |cut S| = ℓ} ≤ (32 : ℝ)^ℓ` given `hone`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, (3.49), pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **The contour count as a `32^ℓ` power bound**: the number of size-`ℓ` droplets is at most
`32^ℓ` (absorbing the polynomial factor `ℓ ≤ 2^ℓ` into `ℓ · 16^ℓ ≤ 32^ℓ`). -/
theorem peierls_contour_count_pow {Λ Λd : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ} {g : ↑Λ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hone : ∀ S ∈ D, ∀ d e : BoundaryDart (S.image Subtype.val), d.SameOrbit e)
    (ℓ : ℕ) :
    ((D.filter (fun S => (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = ℓ)).card
      : ℝ) ≤ (32 : ℝ) ^ ℓ := by
  classical
  set Dℓ := D.filter (fun S => (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = ℓ)
    with hDℓ
  have hmem : ∀ S ∈ Dℓ, S ∈ D := fun S hS => Finset.mem_of_mem_filter S hS
  have hcount : Dℓ.card ≤ ℓ * (2 * 2) ^ (2 * ℓ) :=
    peierls_contour_count hpre Dℓ
      (fun S hS => hdual S (hmem S hS)) (fun S hS => hi S (hmem S hS))
      (fun S hS => hne S (hmem S hS)) (fun S hS => hg S (hmem S hS))
      (fun S hS => hone S (hmem S hS))
      (fun S hS => (Finset.mem_filter.mp hS).2)
  have habsorb : ℓ * (2 * 2) ^ (2 * ℓ) ≤ 32 ^ ℓ := by
    have key : (2 * 2) ^ (2 * ℓ) = 16 ^ ℓ := by rw [pow_mul]; norm_num
    have h32 : (32 : ℕ) ^ ℓ = 2 ^ ℓ * 16 ^ ℓ := by
      rw [show (32 : ℕ) = 2 * 16 by norm_num, mul_pow]
    rw [key, h32]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.lt_two_pow_self))
  calc ((Dℓ.card : ℝ))
      ≤ ((ℓ * (2 * 2) ^ (2 * ℓ) : ℕ) : ℝ) := by exact_mod_cast hcount
    _ ≤ ((32 ^ ℓ : ℕ) : ℝ) := by exact_mod_cast habsorb
    _ = (32 : ℝ) ^ ℓ := by push_cast; ring

end IsingModel
