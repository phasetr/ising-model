import IsingModel.GibbsMeasure

/-!
# Lattice graphs on ℤ^d

The d-dimensional integer lattice ℤ^d with nearest-neighbor adjacency.
This provides the concrete graph structure for the Ising model on a lattice,
used in the Peierls argument for the existence of phase transitions (§5.4).

## Main definitions

* `latticeGraph` — the ℤ^d nearest-neighbor simple graph
* `BoxSite` — the finite box `{-n, ..., n}^d ⊂ ℤ^d`
* `boxGraph` — lattice graph restricted to a box
* `latticeZ`, `latticeCorrelation` — Ising model on a lattice box

## References

* Glimm–Jaffe, *Quantum Physics*, §5.4, pp. 80–84.
-/

namespace IsingModel

open Finset

/-! ## ℤ^d nearest-neighbor graph -/

/-- Two points in ℤ^d are nearest neighbors if the ℓ¹ distance is 1:
they differ by ±1 in exactly one coordinate and agree in all others. -/
def latticeGraph (d : ℕ) : SimpleGraph (Fin d → ℤ) where
  Adj x y := (∑ i : Fin d, |x i - y i|) = 1
  symm := fun {x y} h => by simp only [abs_sub_comm] at h ⊢; exact h
  loopless := ⟨fun _ h => by simp only [sub_self, abs_zero, Finset.sum_const_zero] at h; omega⟩

/-- Adjacency in the lattice graph is decidable. -/
instance (d : ℕ) : DecidableRel (latticeGraph d).Adj :=
  fun x y => inferInstanceAs (Decidable ((∑ i : Fin d, |x i - y i|) = 1))

/-! ## ℓ¹ lattice distance on ℤ^d

An `ℕ`-valued $\ell^1$ distance on `Fin d → ℤ`, used as an
infrastructure step in the GJ §5.1 cluster-decay formalization
(Epic #780). The value is taken in `ℕ` via `Int.natAbs` so that
"far apart" can be expressed at the natural-number level; downstream
summability arguments (Simon–Lieb iteration) then operate on a purely
natural quantity with only a single cast crossing to `ℤ` (the
adjacency-compatibility lemma `latticeGraph_adj_iff_latticeDistance_eq_one`).
-/

/-- **ℓ¹ lattice distance on `ℤ^d`** with range `ℕ`:
`latticeDistance d x y = ∑ i, |x i - y i|_ℕ` where `|·|_ℕ` is
`Int.natAbs`. Used as the natural "far apart" quantity in the
cluster-decay statements of GJ §5.1. -/
def latticeDistance (d : ℕ) (x y : Fin d → ℤ) : ℕ :=
  ∑ i : Fin d, (x i - y i).natAbs

/-- A point is at `latticeDistance` zero from itself. -/
@[simp] lemma latticeDistance_self (d : ℕ) (x : Fin d → ℤ) :
    latticeDistance d x x = 0 := by
  simp [latticeDistance]

/-- `latticeDistance` is symmetric in its two arguments. -/
lemma latticeDistance_comm (d : ℕ) (x y : Fin d → ℤ) :
    latticeDistance d x y = latticeDistance d y x := by
  unfold latticeDistance
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [show x i - y i = -(y i - x i) by ring, Int.natAbs_neg]

/-- `latticeDistance` vanishes exactly on the diagonal. -/
lemma latticeDistance_eq_zero_iff (d : ℕ) (x y : Fin d → ℤ) :
    latticeDistance d x y = 0 ↔ x = y := by
  unfold latticeDistance
  constructor
  · intro hsum
    funext i
    have hi : (x i - y i).natAbs = 0 := by
      have hmem : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
      have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin d)),
          0 ≤ (x j - y j).natAbs := by
        intro j _; exact Nat.zero_le _
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum i hmem
    have hzero : x i - y i = 0 := Int.natAbs_eq_zero.mp hi
    linarith
  · rintro rfl
    simp

/-- Triangle inequality for `latticeDistance`. -/
lemma latticeDistance_triangle (d : ℕ) (x y z : Fin d → ℤ) :
    latticeDistance d x z ≤
      latticeDistance d x y + latticeDistance d y z := by
  unfold latticeDistance
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i _
  have hsplit : x i - z i = (x i - y i) + (y i - z i) := by ring
  calc (x i - z i).natAbs
      = ((x i - y i) + (y i - z i)).natAbs := by rw [hsplit]
    _ ≤ (x i - y i).natAbs + (y i - z i).natAbs :=
        Int.natAbs_add_le _ _

/-- Adjacency in `latticeGraph d` is exactly `latticeDistance = 1`. -/
lemma latticeGraph_adj_iff_latticeDistance_eq_one
    (d : ℕ) (x y : Fin d → ℤ) :
    (latticeGraph d).Adj x y ↔ latticeDistance d x y = 1 := by
  change (∑ i : Fin d, |x i - y i|) = 1 ↔ latticeDistance d x y = 1
  have hcast :
      (∑ i : Fin d, |x i - y i|) =
        ((latticeDistance d x y : ℕ) : ℤ) := by
    unfold latticeDistance
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact Int.abs_eq_natAbs (x i - y i)
  rw [hcast]
  exact_mod_cast Iff.rfl

/-- **Finite ℓ¹ balls**: the set of points at `latticeDistance` at
most `N` from a fixed basepoint is finite. Follows from the
coordinatewise bound `(i k - j k).natAbs ≤ latticeDistance d i j`
(one summand is bounded by a `ℕ`-sum), placing `j k` in the finite
integer interval `[i k - N, i k + N]`. -/
lemma latticeDistance_le_finite (d : ℕ) (i : Fin d → ℤ) (N : ℕ) :
    Set.Finite {j : Fin d → ℤ | latticeDistance d i j ≤ N} := by
  -- Every point in the ball lies in the product of finite integer
  -- intervals `[i k - N, i k + N]`.
  apply Set.Finite.subset
    (Set.Finite.pi (fun k : Fin d =>
      Set.finite_Icc ((i k) - (N : ℤ)) ((i k) + (N : ℤ))))
  intro j hj
  have hball : latticeDistance d i j ≤ N := hj
  intro k _
  -- The `k`-th summand is bounded by the whole sum.
  have hcoord : (i k - j k).natAbs ≤ latticeDistance d i j := by
    unfold latticeDistance
    exact Finset.single_le_sum
      (f := fun m : Fin d => (i m - j m).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hkN : (i k - j k).natAbs ≤ N := hcoord.trans hball
  -- Convert to the integer interval bound.
  have habs_le : |i k - j k| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hkN
  obtain ⟨h_neg, h_pos⟩ := abs_le.mp habs_le
  exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩

/-- **Proper map property**: `latticeDistance d i` tends to infinity
along the cofinite filter, for every dimension `d` and basepoint
`i`. Equivalently, preimages of bounded sets are finite. For `d =
0` the domain `Fin 0 → ℤ` is a singleton, so `Filter.cofinite` on
the source collapses to `⊥` and the Tendsto statement holds
vacuously; for `d ≥ 1` this is the substantive statement that
lets PR #779's cofinite cluster decay be reread as "`j` tends to
infinity in the ℓ¹ sense". -/
theorem tendsto_latticeDistance_atTop_cofinite
    (d : ℕ) (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ => latticeDistance d i j)
      Filter.cofinite Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro N
  rw [Filter.eventually_cofinite]
  apply (latticeDistance_le_finite d i N).subset
  intro j hj
  exact (Nat.lt_of_not_le hj).le

/-- **Filter equality** between the comap of `Filter.atTop` along
`latticeDistance d i` and the cofinite filter on `Fin d → ℤ`. The
`≥` direction is `Filter.Tendsto.le_comap` of PR #782's
`tendsto_latticeDistance_atTop_cofinite`. The `≤` direction uses
PR #782's `latticeDistance_le_finite` together with
`Set.Finite.bddAbove` on `ℕ`: any cofinite `S` has a finite
complement, on which `latticeDistance d i` is therefore bounded
above by some `M`, so `S` contains the preimage of
`Set.Ici (M + 1) ∈ Filter.atTop`.

Geometrically: "going to infinity along the lattice distance" and
"eventually leaving every finite set" are the same filter on
`Fin d → ℤ`. This lets the cofinite cluster decay of PR #779 be
restated in distance-based form (see
`truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_summable`). -/
lemma comap_latticeDistance_atTop_eq_cofinite
    (d : ℕ) (i : Fin d → ℤ) :
    Filter.comap (fun j : Fin d → ℤ => latticeDistance d i j)
        Filter.atTop
      = Filter.cofinite := by
  classical
  refine le_antisymm ?_ (tendsto_latticeDistance_atTop_cofinite d i).le_comap
  intro S hS
  rw [Filter.mem_cofinite] at hS
  obtain ⟨M, hM⟩ :=
    (hS.image (fun j : Fin d → ℤ => latticeDistance d i j)).bddAbove
  refine Filter.mem_comap.mpr ⟨Set.Ici (M + 1), Filter.Ici_mem_atTop _, ?_⟩
  intro j hj
  by_contra hjS
  have hjSc : j ∈ Sᶜ := hjS
  have hbound : latticeDistance d i j ≤ M :=
    hM (Set.mem_image_of_mem _ hjSc)
  have hge : M + 1 ≤ latticeDistance d i j := hj
  omega

/-! ## Finite boxes in ℤ^d

We model the box `{-n, ..., n}^d` as `Fin d → Fin (2*n+1)` with a
canonical embedding into `Fin d → ℤ`. This avoids the need for
`Fintype (Fin d → ℤ)` (which doesn't exist since ℤ is infinite). -/

/-- The box site type: `Fin d → Fin (2*n+1)`, representing the box `{0,...,2n}^d`.
The canonical embedding into ℤ^d maps `x` to `x - n` (centering at origin). -/
abbrev BoxSite (d : ℕ) (n : ℕ) := Fin d → Fin (2 * n + 1)

/-- Embed a box site into ℤ^d, centering the box at the origin:
`embed(x)_i = x_i - n`. -/
def boxEmbed (d : ℕ) (n : ℕ) (x : BoxSite d n) : Fin d → ℤ :=
  fun i => (x i : ℤ) - ↑n

/-- The lattice graph restricted to a finite box. Two box sites are adjacent
if their ℤ^d embeddings are nearest neighbors. -/
def boxGraph (d : ℕ) (n : ℕ) : SimpleGraph (BoxSite d n) where
  Adj x y := (latticeGraph d).Adj (boxEmbed d n x) (boxEmbed d n y)
  symm := fun {_ _} h => (latticeGraph d).symm h
  loopless := ⟨fun v h => (latticeGraph d).loopless.irrefl (boxEmbed d n v) h⟩

/-- Adjacency in the box graph is decidable. -/
instance (d : ℕ) (n : ℕ) : DecidableRel (boxGraph d n).Adj :=
  fun x y => inferInstanceAs (Decidable ((latticeGraph d).Adj (boxEmbed d n x) (boxEmbed d n y)))

/-- The edge set of the box graph is finite (finite vertex type). -/
noncomputable instance (d : ℕ) (n : ℕ) : Fintype (boxGraph d n).edgeSet :=
  Set.Finite.fintype (Set.toFinite (boxGraph d n).edgeSet)

/-! ## The Ising model on a lattice box -/

/-- The Ising partition function on the d-dimensional box of radius n. -/
noncomputable def latticeZ (d : ℕ) (n : ℕ) (p : IsingParams ℝ) : ℝ :=
  partitionFunction (boxGraph d n) p

/-- The Ising correlation function on the d-dimensional box of radius n. -/
noncomputable def latticeCorrelation (d : ℕ) (n : ℕ) (p : IsingParams ℝ)
    (A : Finset (BoxSite d n)) : ℝ :=
  correlation (boxGraph d n) p A

/-- The partition function on any lattice box is positive. -/
theorem latticeZ_pos (d : ℕ) (n : ℕ) (p : IsingParams ℝ) :
    0 < latticeZ d n p :=
  partitionFunction_pos (boxGraph d n) p

end IsingModel
