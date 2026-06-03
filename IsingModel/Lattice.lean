import IsingModel.GibbsMeasure
import Mathlib.Combinatorics.SimpleGraph.Metric

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

/-- **Lattice Chebyshev (ℓ∞) distance** on `ℤ^d`: the maximum coordinate
difference `max_i |x_i − y_i|`. This is the lattice "hyperplane separation"
distance of Glimm–Jaffe §17.5 (p. 312), in which the transfer matrix gives
exponential decay `e^{−m·dist}` of correlations. -/
def latticeDistanceInf (d : ℕ) (x y : Fin d → ℤ) : ℕ :=
  Finset.univ.sup (fun i => (x i - y i).natAbs)

/-- A point is at Chebyshev distance zero from itself. -/
@[simp] lemma latticeDistanceInf_self (d : ℕ) (x : Fin d → ℤ) :
    latticeDistanceInf d x x = 0 := by
  unfold latticeDistanceInf
  simp only [sub_self, Int.natAbs_zero]
  exact Nat.le_zero.mp (Finset.sup_le fun _ _ => le_rfl)

/-- The Chebyshev distance is symmetric. -/
lemma latticeDistanceInf_comm (d : ℕ) (x y : Fin d → ℤ) :
    latticeDistanceInf d x y = latticeDistanceInf d y x := by
  unfold latticeDistanceInf
  refine Finset.sup_congr rfl (fun i _ => ?_)
  rw [show x i - y i = -(y i - x i) by ring, Int.natAbs_neg]

/-- The Chebyshev distance vanishes exactly between equal points. -/
lemma latticeDistanceInf_eq_zero_iff (d : ℕ) (x y : Fin d → ℤ) :
    latticeDistanceInf d x y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    have hle : (x i - y i).natAbs ≤ latticeDistanceInf d x y :=
      Finset.le_sup (f := fun j => (x j - y j).natAbs) (Finset.mem_univ i)
    rw [h, Nat.le_zero, Int.natAbs_eq_zero, sub_eq_zero] at hle
    exact hle
  · intro h
    rw [h]
    exact latticeDistanceInf_self d y

/-- Triangle inequality for the Chebyshev (ℓ∞) distance. -/
lemma latticeDistanceInf_triangle (d : ℕ) (x y z : Fin d → ℤ) :
    latticeDistanceInf d x z ≤
      latticeDistanceInf d x y + latticeDistanceInf d y z := by
  unfold latticeDistanceInf
  apply Finset.sup_le
  intro i _
  calc (x i - z i).natAbs
      = ((x i - y i) + (y i - z i)).natAbs := by rw [sub_add_sub_cancel]
    _ ≤ (x i - y i).natAbs + (y i - z i).natAbs := Int.natAbs_add_le _ _
    _ ≤ Finset.univ.sup (fun j => (x j - y j).natAbs)
          + Finset.univ.sup (fun j => (y j - z j).natAbs) :=
        Nat.add_le_add
          (Finset.le_sup (f := fun j => (x j - y j).natAbs) (Finset.mem_univ i))
          (Finset.le_sup (f := fun j => (y j - z j).natAbs) (Finset.mem_univ i))

/-- The Chebyshev distance between distinct points is strictly positive. -/
lemma latticeDistanceInf_pos_of_ne (d : ℕ) {x y : Fin d → ℤ} (hxy : x ≠ y) :
    0 < latticeDistanceInf d x y :=
  Nat.pos_of_ne_zero (fun h => hxy ((latticeDistanceInf_eq_zero_iff d x y).mp h))

/-- **The Chebyshev (ℓ∞) distance is bounded by the ℓ¹ distance** (`max ≤ sum`):
each coordinate difference is at most the total. -/
lemma latticeDistanceInf_le_latticeDistance (d : ℕ) (x y : Fin d → ℤ) :
    latticeDistanceInf d x y ≤ latticeDistance d x y := by
  unfold latticeDistanceInf latticeDistance
  apply Finset.sup_le
  intro i _
  exact Finset.single_le_sum (f := fun j => (x j - y j).natAbs)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

/-- **The ℓ¹ distance is bounded by `d` times the Chebyshev distance**
(`sum ≤ card · max`): the geometric input `dist ≥ |x−y|/a₀` of Glimm–Jaffe §17.5
with `a₀ = d`. On ℤ^d the hyperplane separation is the ℓ∞ distance, and
`|x−y|₁ ≤ d·|x−y|_∞`, so the transfer-matrix decay `e^{−m·dist}` in the hyperplane
separation implies decay at rate `m/d` in the ℓ¹ distance. -/
lemma latticeDistance_le_card_mul_latticeDistanceInf (d : ℕ) (x y : Fin d → ℤ) :
    latticeDistance d x y ≤ d * latticeDistanceInf d x y := by
  unfold latticeDistance latticeDistanceInf
  calc ∑ i : Fin d, (x i - y i).natAbs
      ≤ ∑ _i : Fin d, Finset.univ.sup (fun j => (x j - y j).natAbs) :=
        Finset.sum_le_sum
          (fun i _ => Finset.le_sup (f := fun j => (x j - y j).natAbs) (Finset.mem_univ i))
    _ = d * Finset.univ.sup (fun j => (x j - y j).natAbs) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

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

/-- **One-step reduction toward `y`**: if the ℓ¹ distance from `x` to `y` is
`n+1`, there is a lattice-adjacent point `x'` (one coordinate moved one unit
toward `y`) with ℓ¹ distance `n` to `y`. The inductive step for constructing a
geodesic walk in `latticeGraph d`. -/
lemma latticeDistance_exists_adj_step (d : ℕ) {x y : Fin d → ℤ} {n : ℕ}
    (h : latticeDistance d x y = n + 1) :
    ∃ x', (latticeGraph d).Adj x x' ∧ latticeDistance d x' y = n := by
  have hne : x ≠ y := fun he => by rw [he, latticeDistance_self] at h; omega
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  set v : ℤ := x i + (if x i < y i then 1 else -1) with hvdef
  have hstep : (v - y i).natAbs + 1 = (x i - y i).natAbs := by
    rcases lt_trichotomy (x i) (y i) with hlt | heq | hgt
    · rw [hvdef, if_pos hlt]; omega
    · exact absurd heq hi
    · rw [hvdef, if_neg (not_lt.mpr hgt.le)]; omega
  refine ⟨Function.update x i v, ?_, ?_⟩
  · rw [latticeGraph_adj_iff_latticeDistance_eq_one]
    unfold latticeDistance
    rw [Finset.sum_eq_single i]
    · rw [Function.update_self]
      omega
    · intro j _ hj
      rw [Function.update_of_ne hj]
      simp
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  · have hL : latticeDistance d (Function.update x i v) y
        = (v - y i).natAbs + ∑ j ∈ Finset.univ.erase i, (x j - y j).natAbs := by
      unfold latticeDistance
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have hR : latticeDistance d x y
        = (x i - y i).natAbs + ∑ j ∈ Finset.univ.erase i, (x j - y j).natAbs := by
      unfold latticeDistance
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [hL]
    rw [hR] at h
    omega

/-- **A geodesic walk exists**: between any two points there is a walk in
`latticeGraph d` whose length equals the ℓ¹ distance. By induction on the
distance, prepending one coordinate step (`latticeDistance_exists_adj_step`). -/
lemma latticeGraph_exists_walk_length (d : ℕ) (x y : Fin d → ℤ) :
    ∃ w : (latticeGraph d).Walk x y, w.length = latticeDistance d x y := by
  suffices h : ∀ n x, latticeDistance d x y = n →
      ∃ w : (latticeGraph d).Walk x y, w.length = n by
    obtain ⟨w, hw⟩ := h (latticeDistance d x y) x rfl
    exact ⟨w, hw⟩
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [latticeDistance_eq_zero_iff] at hx
    subst hx
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ m ih =>
    intro x hx
    obtain ⟨x', hadj, hd'⟩ := latticeDistance_exists_adj_step d hx
    obtain ⟨w', hw'⟩ := ih x' hd'
    exact ⟨SimpleGraph.Walk.cons hadj w', by rw [SimpleGraph.Walk.length_cons, hw']⟩

/-- **The lattice graph is connected.** -/
lemma latticeGraph_connected (d : ℕ) : (latticeGraph d).Connected where
  preconnected x y := (latticeGraph_exists_walk_length d x y).elim (fun w _ => w.reachable)
  nonempty := ⟨fun _ => 0⟩

/-- **The ℓ¹ distance is a lower bound on any walk length**: every walk in
`latticeGraph d` from `x` to `y` has length at least `latticeDistance d x y`
(each edge changes the ℓ¹ distance by one, via the triangle inequality). -/
lemma latticeDistance_le_walk_length (d : ℕ) {x y : Fin d → ℤ}
    (w : (latticeGraph d).Walk x y) : latticeDistance d x y ≤ w.length := by
  induction w with
  | nil => simp
  | @cons x z y hadj w' ih =>
    rw [latticeGraph_adj_iff_latticeDistance_eq_one] at hadj
    rw [SimpleGraph.Walk.length_cons]
    calc latticeDistance d x y
        ≤ latticeDistance d x z + latticeDistance d z y := latticeDistance_triangle d x z y
      _ = 1 + latticeDistance d z y := by rw [hadj]
      _ ≤ 1 + w'.length := by omega
      _ = w'.length + 1 := by omega

/-- **Graph distance in `latticeGraph d` equals the ℓ¹ distance**: the
shortest-path metric of the lattice graph coincides with `latticeDistance`. The
geodesic walk (`latticeGraph_exists_walk_length`) gives `≤`, and the
walk-length lower bound (`latticeDistance_le_walk_length`) gives `≥`. -/
lemma latticeGraph_dist_eq_latticeDistance (d : ℕ) (x y : Fin d → ℤ) :
    (latticeGraph d).dist x y = latticeDistance d x y := by
  apply le_antisymm
  · obtain ⟨w, hw⟩ := latticeGraph_exists_walk_length d x y
    calc (latticeGraph d).dist x y ≤ w.length := SimpleGraph.dist_le w
      _ = latticeDistance d x y := hw
  · obtain ⟨p, hp⟩ := ((latticeGraph_connected d).preconnected x y).exists_walk_length_eq_dist
    calc latticeDistance d x y ≤ p.length := latticeDistance_le_walk_length d p
      _ = (latticeGraph d).dist x y := hp

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
`Set.Finite.bddAbove` on `ℕ` to bound `latticeDistance d i` on
the finite complement of any cofinite set: the image of that
finite complement under `latticeDistance d i` is a finite subset
of `ℕ`, hence has an upper bound `M`, so the cofinite set contains
the preimage of `Set.Ici (M + 1) ∈ Filter.atTop`.

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
