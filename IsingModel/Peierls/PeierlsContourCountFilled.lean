import IsingModel.Peierls.PeierlsSum
import IsingModel.Peierls.BondFilledEdgeConnected

/-!
# The unconditional filled-droplet Peierls contour count (FV §3.7.2)

With `planarBondHypothesis` discharged (`#4180`) and the filled-droplet dual-cut edge-connectivity
established unconditionally (`dualCutInBox_isEdgeConnected_filled`), the Peierls contour count no
longer needs the single-orbit hypothesis `hone` nor the ambient connectivity inputs `hF`/`hC`. For a
family of filled connected neighbour-closed droplets it holds outright, with the connectivity supply
discharged internally from the droplet structure.

This is the convergent route replacing the `hone` hypothesis (`peierls_contour_count`) and the
ambient-`hF`/`hC` bond hypothesis (`peierls_contour_count_of_bond`): the only geometric inputs are
that each droplet is connected (`IsConnectedDroplet`) and filled (`IsFilled`).

* `peierls_contour_count_filled` — the contour bound `|D| ≤ r · 16^r` for filled droplets.
* `peierls_contour_count_pow_filled` — the clean `32^ℓ` power bound for filled droplets.
* `peierls_sum_le_filled` — the geometric tail bound on the filled droplet sum at low temperature.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, (3.49), pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

/-- **The Peierls contour count for filled droplets** (unconditional): the contour bound holds when
each box droplet is connected (`IsConnectedDroplet`) and filled (`IsFilled`). The connectivity
supply for the contour-counting injection is discharged via `dualCutInBox_isEdgeConnected_filled`,
the filled-droplet specialisation of the now-proved planar bond lemma, so neither the single-orbit
hypothesis nor the ambient `hF`/`hC` connectivity inputs are required. -/
theorem peierls_contour_count_filled {Λ Λd : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ}
    {g : ↑Λ} {r : ℕ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hconn : ∀ S ∈ D, IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hfill : ∀ S ∈ D, IsFilled (Ambient.inducedGraph (latticeGraph 2) Λ) g S)
    (hr : ∀ S ∈ D, (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = r) :
    D.card ≤ r * (2 * 2) ^ (2 * r) := by
  classical
  set cut : Finset ↑Λ → Finset (Sym2 ↑Λd) :=
    fun S => if h : dualSupport (S.image Subtype.val) ⊆ Λd then dualCutInBox h else ∅ with hcut
  have hcutD : ∀ S (hS : S ∈ D), cut S = dualCutInBox (hdual S hS) := by
    intro S hS; exact dif_pos (hdual S hS)
  have hcardD : ∀ S ∈ D, (cut S).card = r := by
    intro S hS
    rw [hcutD S hS, dualCutInBox_card_eq_cutEdges (hne S hS), hr S hS]
  calc D.card
      ≤ (rayAnchorSet Λd i r).card * (2 * 2) ^ (2 * r) := by
        refine contour_count_le r D cut (rayAnchorSet Λd i r) ?_ ?_ ?_ hcardD ?_
        · -- injectivity
          intro S₁ hS₁ S₂ hS₂ heq
          rw [Finset.mem_coe] at hS₁ hS₂
          rw [hcutD S₁ hS₁, hcutD S₂ hS₂] at heq
          exact box_droplet_eq_of_dualCutInBox_eq hpre (hne S₁ hS₁) (hne S₂ hS₂)
            (hg S₁ hS₁) (hg S₂ hS₂) heq
        · -- subset of the edge finset
          intro S hS
          rw [hcutD S hS]; exact dualCutInBox_subset_edgeFinset _
        · -- connectivity (filled-droplet planar bond lemma)
          intro S hS
          rw [hcutD S hS]
          exact dualCutInBox_isEdgeConnected_filled (hdual S hS) (hne S hS) (hconn S hS)
            (hfill S hS)
        · -- anchored in the ray anchor set
          intro S hS
          rw [hcutD S hS]
          exact rayAnchorSet_cover (hi S hS) (hdual S hS) (by
            rw [← hcutD S hS]; exact hcardD S hS)
    _ ≤ r * (2 * 2) ^ (2 * r) :=
        Nat.mul_le_mul_right _ rayAnchorSet_card_le

/-- **The filled-droplet contour count as a `32^ℓ` power bound**: the number of size-`ℓ` filled
connected droplets is at most `32^ℓ` (absorbing the polynomial factor `ℓ ≤ 2^ℓ` into
`ℓ · 16^ℓ ≤ 32^ℓ`), with no single-orbit or ambient connectivity hypothesis. -/
theorem peierls_contour_count_pow_filled {Λ Λd : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ} {g : ↑Λ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hconn : ∀ S ∈ D, IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hfill : ∀ S ∈ D, IsFilled (Ambient.inducedGraph (latticeGraph 2) Λ) g S)
    (ℓ : ℕ) :
    ((D.filter (fun S => (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = ℓ)).card
      : ℝ) ≤ (32 : ℝ) ^ ℓ := by
  classical
  set Dℓ := D.filter (fun S => (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card = ℓ)
    with hDℓ
  have hmem : ∀ S ∈ Dℓ, S ∈ D := fun S hS => Finset.mem_of_mem_filter S hS
  have hcount : Dℓ.card ≤ ℓ * (2 * 2) ^ (2 * ℓ) :=
    peierls_contour_count_filled hpre Dℓ
      (fun S hS => hdual S (hmem S hS)) (fun S hS => hi S (hmem S hS))
      (fun S hS => hne S (hmem S hS)) (fun S hS => hg S (hmem S hS))
      (fun S hS => hconn S (hmem S hS)) (fun S hS => hfill S (hmem S hS))
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

/-- **The filled-droplet Peierls sum is geometrically small at low temperature** (unconditional):
for `q = exp(-2βJ)` with `32 q < 1`, the sum `∑_S exp(-2βJ · |cut S|)` over filled connected
neighbour-closed droplets is at most `(32 q)^n / (1 - 32 q)`, where `n` lower-bounds the cut sizes.
No single-orbit or ambient connectivity hypothesis is required. -/
theorem peierls_sum_le_filled {Λ Λd : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ} {g : ↑Λ}
    (hpre : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (D : Finset (Finset ↑Λ))
    (hdual : ∀ S ∈ D, dualSupport (S.image Subtype.val) ⊆ Λd)
    (hi : ∀ S ∈ D, i ∈ S.image Subtype.val)
    (hne : ∀ S ∈ D, NeighbourClosed Λ S)
    (hg : ∀ S ∈ D, g ∉ S)
    (hconn : ∀ S ∈ D, IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hfill : ∀ S ∈ D, IsFilled (Ambient.inducedGraph (latticeGraph 2) Λ) g S)
    {β J : ℝ} (n : ℕ)
    (hge : ∀ S ∈ D, n ≤ (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card)
    (hr0 : 0 < 32 * Real.exp (-2 * β * J)) (hr1 : 32 * Real.exp (-2 * β * J) < 1) :
    ∑ S ∈ D, Real.exp (-2 * β * J * ↑(cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card)
      ≤ (32 * Real.exp (-2 * β * J)) ^ n / (1 - 32 * Real.exp (-2 * β * J)) := by
  classical
  set G := Ambient.inducedGraph (latticeGraph 2) Λ with hGdef
  have hexp : ∀ S : Finset ↑Λ,
      Real.exp (-2 * β * J * ↑(cutEdges G S).card)
      = Real.exp (-2 * β * J) ^ (cutEdges G S).card := by
    intro S
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [Finset.sum_congr rfl (fun S _ => hexp S)]
  have hbound := sum_pow_le_geometric_tail_of_count D
    (fun S => (cutEdges G S).card) (q := Real.exp (-2 * β * J))
    (Real.exp_nonneg _) (M := 32) n hge
    (fun ℓ => peierls_contour_count_pow_filled hpre D hdual hi hne hg hconn hfill ℓ)
    (by exact_mod_cast hr0) (by exact_mod_cast hr1)
  refine hbound.trans (le_of_eq ?_)
  norm_num

end IsingModel
