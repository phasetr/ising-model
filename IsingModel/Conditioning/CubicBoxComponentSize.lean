import IsingModel.Conditioning.InduceDistanceTransfer
import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxScreeningDecomp

/-!
# Lower bound on the origin component size in the cubic box (FV §3.7.3, eq. 3.49)

The FV §3.7.3 geometric estimate `|C| ≥ n`: in the cubic box `B(m)` with `+` boundary on
the inner box `B(n)`, the connected component of the origin arising from an `E⁺;0`
subgraph must reach the boundary, hence has at least `n` edges. Towards the
high-temperature `m*(β)=0` (Issue #3613).

* `latticeDistance_origin_ge_of_not_mem_cubicBox` — a site outside `B(n)` is at lattice
  distance `≥ n+1` from the origin.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, eq. (3.49), p. 118.
-/

namespace IsingModel

open Finset Ambient

/-- **A site outside the inner box is far from the origin**: if `x ∉ cubicBox d n` then
`n + 1 ≤ latticeDistance d 0 x` (some coordinate has absolute value `≥ n+1`, which already
contributes that much to the `ℓ¹` distance). -/
theorem latticeDistance_origin_ge_of_not_mem_cubicBox {d n : ℕ} {x : Fin d → ℤ}
    (hx : x ∉ cubicBox d n) :
    n + 1 ≤ latticeDistance d (0 : Fin d → ℤ) x := by
  classical
  rw [mem_cubicBox] at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  have hnat : n + 1 ≤ (x i).natAbs := by
    have : (n : ℤ) + 1 ≤ |x i| := by
      rcases lt_or_ge (x i) 0 with hneg | hpos
      · rw [abs_of_neg hneg]; omega
      · rw [abs_of_nonneg hpos]; omega
    have habs : (((x i).natAbs : ℤ)) = |x i| := (Int.abs_eq_natAbs (x i)).symm
    omega
  calc n + 1 ≤ (x i).natAbs := hnat
    _ = ((0 : Fin d → ℤ) i - x i).natAbs := by simp [Int.natAbs_neg]
    _ ≤ ∑ j : Fin d, ((0 : Fin d → ℤ) j - x j).natAbs :=
        Finset.single_le_sum (f := fun j => ((0 : Fin d → ℤ) j - x j).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = latticeDistance d (0 : Fin d → ℤ) x := rfl

variable {ι : Type*} [DecidableEq ι]

/-- **Parity inheritance for the origin component**: if a vertex `v` has even `X`-degree,
then it has even `componentOfZero X z`-degree (the component-degree is either the full
`X`-degree, when `v` is in the component support, or `0`). -/
theorem even_filter_card_componentOfZero {X : Finset (Sym2 ι)} {z v : ι}
    (hv : Even ((X.filter (v ∈ ·)).card)) :
    Even (((componentOfZero X z).filter (v ∈ ·)).card) := by
  classical
  by_cases hvsupp : ∃ f ∈ componentOfZero X z, v ∈ f
  · obtain ⟨f, hf, hvf⟩ := hvsupp
    have hadd := filter_card_componentOfZero_add X z v
    rw [filter_card_sdiff_eq_zero_of_mem_support hf hvf, add_zero] at hadd
    rwa [← hadd]
  · have hempty : ((componentOfZero X z).filter (v ∈ ·)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      exact fun e he hve => hvsupp ⟨e, he, hve⟩
    rw [hempty, Finset.card_empty]
    exact ⟨0, by simp⟩

/-- **The origin component reaches the boundary** (FV (3.49)): in the cubic box `B(m)` with
`+` boundary on the inner box `B(n)`, an `E⁺;0` subgraph `X` (odd degree at the origin `z`,
even degree elsewhere on the interior) has `n ≤ |componentOfZero X z|`. The component's
second odd-degree vertex must lie outside the inner box (even degree there forbids it), at
lattice distance `≥ n+1` from the origin, and the component reaches it within `|C|` edges. -/
theorem card_componentOfZero_ge_of_E0 {d n m : ℕ}
    (X : Finset (Sym2 ↑(cubicBox d m)))
    (hXG : X ⊆ (inducedGraph (latticeGraph d) (cubicBox d m)).edgeFinset)
    {z : ↑(cubicBox d m)} (hz0 : (z : Fin d → ℤ) = 0) {e₀ : Sym2 ↑(cubicBox d m)}
    (he₀ : e₀ ∈ X) (hze₀ : z ∈ e₀)
    (hE0 : ∀ v ∈ plusBoxInterior d n m,
        Even ((if v = z then 1 else 0) + (X.filter (v ∈ ·)).card)) :
    n ≤ (componentOfZero X z).card := by
  classical
  have hzΛ : z ∈ plusBoxInterior d n m := by
    rw [mem_plusBoxInterior, hz0, mem_cubicBox]
    intro i; simp only [Pi.zero_apply]; omega
  have hXzodd : Odd ((X.filter (z ∈ ·)).card) := by
    have hev := hE0 z hzΛ
    rw [if_pos rfl] at hev
    rcases Nat.even_or_odd ((X.filter (z ∈ ·)).card) with h | h
    · exact absurd hev (by rw [add_comm]; simpa [Nat.even_add_one] using h)
    · exact h
  have hCzodd : Odd (((componentOfZero X z).filter (z ∈ ·)).card) := by
    have hadd := filter_card_componentOfZero_add X z z
    rw [filter_card_sdiff_eq_zero_of_mem_support
      (mem_componentOfZero_of_incident he₀ hze₀) hze₀, add_zero] at hadd
    rwa [← hadd]
  obtain ⟨j, hjz, hjodd, hdist⟩ :=
    latticeDistance_le_card_componentOfZero hXG he₀ hze₀ hCzodd
  have hjΛ : j ∉ plusBoxInterior d n m := by
    intro hjmem
    have hev : Even (((componentOfZero X z).filter (j ∈ ·)).card) := by
      apply even_filter_card_componentOfZero
      have := hE0 j hjmem
      rwa [if_neg hjz, zero_add] at this
    exact (Nat.not_even_iff_odd.mpr hjodd) hev
  have hjbox : (j : Fin d → ℤ) ∉ cubicBox d n :=
    fun h => hjΛ (mem_plusBoxInterior.mpr h)
  have hgeom := latticeDistance_origin_ge_of_not_mem_cubicBox hjbox
  rw [hz0] at hdist
  omega

end IsingModel
