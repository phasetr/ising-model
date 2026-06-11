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

end Ambient

end IsingModel
