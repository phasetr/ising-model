import IsingModel.Concrete.CubicExhaustion
import IsingModel.TranslationInvariance.Finset

/-!
# Tiling a cube by translates of a smaller cube (GJ §4.6)

The geometric core of the unconditional infinite-volume free-energy convergence on the cubic
exhaustion (GJ Proposition 4.6.1): for a fixed radius `r` and spacing `s = 2r+1`, the translates
of `cubicBox d r` centred at the points `s • k`, `k ∈ cubicBox d M`, are pairwise disjoint and
tile the cube `cubicBox d (s*M + r)` exactly. Tiling an arbitrarily large cube almost fully by
copies of a fixed cube turns the disjoint-union super-additivity of `log Z` into the lower bound
`f_N ≥ (|B_{R_N}|/|B_N|) · f_r`, the Fekete-type input of the convergence proof.

* `cubicTileCenter`, `cubicTile` — the tile of index `k`.
* `mem_cubicTile` — coordinatewise membership characterisation.
* `cubicTile_pairwiseDisjoint` — distinct indices give disjoint tiles.
* `biUnion_cubicTile` — the tiles indexed by `cubicBox d M` tile `cubicBox d (s*M + r)`.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Proposition 4.6.1, p. 68.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- The **centre of the tile of index `k`**: the lattice point `(2r+1) • k`. -/
def cubicTileCenter {d : ℕ} (r : ℕ) (k : Fin d → ℤ) : Fin d → ℤ :=
  fun i => (2 * (r : ℤ) + 1) * k i

/-- The **tile of index `k`**: the cube of radius `r` centred at `cubicTileCenter r k`. -/
noncomputable def cubicTile (d r : ℕ) (k : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  vaddFinset (cubicTileCenter r k) (cubicBox d r)

/-- **Membership in a tile**: every coordinate lies within `r` of the tile centre. -/
theorem mem_cubicTile {d r : ℕ} {k x : Fin d → ℤ} :
    x ∈ cubicTile d r k ↔ ∀ i, |x i - (2 * (r : ℤ) + 1) * k i| ≤ r := by
  unfold cubicTile vaddFinset
  rw [Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    intro i
    have hbi := (mem_cubicBox.mp hb) i
    have : (cubicTileCenter r k +ᵥ b) i - (2 * (r : ℤ) + 1) * k i = b i := by
      simp only [cubicTileCenter, vadd_eq_add, Pi.add_apply]
      ring
    rw [this]
    rw [abs_le]
    exact ⟨hbi.1, hbi.2⟩
  · intro h
    refine ⟨fun i => x i - (2 * (r : ℤ) + 1) * k i, ?_, ?_⟩
    · rw [mem_cubicBox]
      intro i
      have := abs_le.mp (h i)
      exact ⟨this.1, this.2⟩
    · funext i
      simp only [cubicTileCenter, vadd_eq_add, Pi.add_apply]
      ring

/-- **The tile index is determined by any of its points**: two indices whose tiles share a
coordinate value within radius `r` of both centres agree (the spacing `2r+1` exceeds `2r`). -/
private theorem tile_index_eq_of_close {r a b c : ℤ} (hr : 0 ≤ r)
    (h1 : |c - (2 * r + 1) * a| ≤ r) (h2 : |c - (2 * r + 1) * b| ≤ r) : a = b := by
  rcases abs_le.mp h1 with ⟨h1l, h1r⟩
  rcases abs_le.mp h2 with ⟨h2l, h2r⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hs : (1 : ℤ) ≤ b - a := by omega
    have : (2 * r + 1) * 1 ≤ (2 * r + 1) * (b - a) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    nlinarith
  · have hs : (1 : ℤ) ≤ a - b := by omega
    have : (2 * r + 1) * 1 ≤ (2 * r + 1) * (a - b) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    nlinarith

/-- **Distinct indices give disjoint tiles.** -/
theorem cubicTile_disjoint {d r : ℕ} {k k' : Fin d → ℤ} (hkk : k ≠ k') :
    Disjoint (cubicTile d r k) (cubicTile d r k') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  refine hkk (funext fun i => ?_)
  exact tile_index_eq_of_close (by positivity)
    ((mem_cubicTile.mp hx) i) ((mem_cubicTile.mp hx') i)

/-- **The tiles indexed by `cubicBox d M` tile the cube of radius `(2r+1)M + r` exactly**: every
point decomposes uniquely as `(2r+1)·k + b` with `|kᵢ| ≤ M` and `|bᵢ| ≤ r` (Euclidean division
of `xᵢ + r` by `2r+1`). -/
theorem biUnion_cubicTile (d r M : ℕ) :
    (cubicBox d M).biUnion (cubicTile d r) = cubicBox d ((2 * r + 1) * M + r) := by
  have hspos : (0 : ℤ) < 2 * (r : ℤ) + 1 := by positivity
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨k, hk, hx⟩
    rw [mem_cubicBox]
    intro i
    have hki := (mem_cubicBox.mp hk) i
    have hxi := abs_le.mp ((mem_cubicTile.mp hx) i)
    have hkup : (2 * (r : ℤ) + 1) * k i ≤ (2 * (r : ℤ) + 1) * M :=
      mul_le_mul_of_nonneg_left hki.2 (by positivity)
    have hklo : -((2 * (r : ℤ) + 1) * M) ≤ (2 * (r : ℤ) + 1) * k i := by
      have := mul_le_mul_of_nonneg_left hki.1 (le_of_lt hspos)
      nlinarith
    constructor
    · push_cast
      nlinarith [hxi.1]
    · push_cast
      nlinarith [hxi.2]
  · intro hx
    refine ⟨fun i => (x i + r) / (2 * (r : ℤ) + 1), ?_, ?_⟩
    · rw [mem_cubicBox]
      intro i
      have hxi := (mem_cubicBox.mp hx) i
      have hde := Int.mul_ediv_add_emod (x i + r) (2 * (r : ℤ) + 1)
      have hm0 : 0 ≤ (x i + r) % (2 * (r : ℤ) + 1) :=
        Int.emod_nonneg _ (by positivity)
      have hms : (x i + r) % (2 * (r : ℤ) + 1) < 2 * (r : ℤ) + 1 :=
        Int.emod_lt_of_pos _ hspos
      push_cast at hxi
      constructor
      · -- `-(M) ≤ k i` from `(2r+1)·k i ≥ -(2r+1)M - (2r)` hence `> -(2r+1)(M+1)`
        by_contra hlt
        push Not at hlt
        have hk1 : (x i + r) / (2 * (r : ℤ) + 1) ≤ -(M : ℤ) - 1 := by omega
        have := mul_le_mul_of_nonneg_left hk1 (le_of_lt hspos)
        nlinarith
      · by_contra hlt
        push Not at hlt
        have hk1 : (M : ℤ) + 1 ≤ (x i + r) / (2 * (r : ℤ) + 1) := by omega
        have := mul_le_mul_of_nonneg_left hk1 (le_of_lt hspos)
        nlinarith
    · rw [mem_cubicTile]
      intro i
      have hde := Int.mul_ediv_add_emod (x i + r) (2 * (r : ℤ) + 1)
      have hm0 : 0 ≤ (x i + r) % (2 * (r : ℤ) + 1) :=
        Int.emod_nonneg _ (by positivity)
      have hms : (x i + r) % (2 * (r : ℤ) + 1) < 2 * (r : ℤ) + 1 :=
        Int.emod_lt_of_pos _ hspos
      rw [abs_le]
      constructor <;> nlinarith

end Ambient

end IsingModel
