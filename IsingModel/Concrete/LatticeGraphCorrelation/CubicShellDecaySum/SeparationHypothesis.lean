import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellDecaySum.ShellDecaySumBound
import IsingModel.Concrete.CubicExhaustion
import IsingModel.Lattice
import IsingModel.AmbientLatticeSum.PerStageIncrement
import IsingModel.AmbientLattice.Defs.Core

/-!
# Cubic-shell decay sum (3/4): separation hypothesis

Structural split (3/4) of `Concrete.LatticeGraphCorrelation.CubicShellDecaySum`.  This child
holds the combinatorics that auto-discharges the separation hypothesis `hsep` of the cubic
per-stage increment bounds: a `latticeGraph` neighbour of a site of `box_R` still lies in
`box_{R+1}`, hence for `R + 1 ≤ k` a lifted site of `box_R` is an endpoint of no straddle
edge of stage `k+1` (using the fresh-vertex property from the sibling
`...ShellDecaySumBound`), and the pair version giving exactly the `hsep` shape.  See the
`Concrete.LatticeGraphCorrelation.CubicShellDecaySum` facade module for the full contents
overview.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- **Adjacent vertex of `cubicBox R` lies in `cubicBox (R + 1)`** (Issue #3054,
Step B sub-lemma). A `latticeGraph` neighbour differs in exactly one coordinate
by ±1, so any neighbour of `r ∈ cubicBox d R` has all coordinates in `Icc (-R-1) (R+1)`,
i.e., lies in `cubicBox d (R + 1)`. Key combinatorial building block for the
separation hypothesis `hsep` of the cubic per-stage increment bound. -/
theorem cubicBox_succ_of_latticeGraph_adj (d R : ℕ) {r y : Fin d → ℤ}
    (hr : r ∈ cubicBox d R) (hadj : (latticeGraph d).Adj r y) :
    y ∈ cubicBox d (R + 1) := by
  rw [mem_cubicBox] at hr ⊢
  -- hadj : ∑ i, |r i - y i| = 1
  have hadj_sum : (∑ i : Fin d, |r i - y i|) = 1 := hadj
  intro i
  -- Bound |y i| by |r i| + |y i - r i| ≤ R + (sum of |y j - r j|) = R + 1
  have hri := hr i
  have hyi_le_sum : |y i - r i| ≤ ∑ j : Fin d, |y j - r j| := by
    refine Finset.single_le_sum (f := fun j => |y j - r j|) ?_ (Finset.mem_univ i)
    intro j _; exact abs_nonneg _
  have hsum_eq : (∑ j : Fin d, |y j - r j|) = (∑ j : Fin d, |r j - y j|) := by
    refine Finset.sum_congr rfl ?_
    intro j _; rw [abs_sub_comm]
  rw [hsum_eq, hadj_sum] at hyi_le_sum
  -- |y i - r i| ≤ 1
  have hbound : -1 ≤ y i - r i ∧ y i - r i ≤ 1 := by
    constructor
    · linarith [neg_abs_le (y i - r i)]
    · linarith [le_abs_self (y i - r i)]
  refine ⟨?_, ?_⟩
  · push_cast; linarith [hri.1, hbound.1]
  · push_cast; linarith [hri.2, hbound.2]

/-- **Single-vertex separation from `R + 1 ≤ k`** (Issue #3054, Step B). For
`r ∈ cubicBox d R` with `R + 1 ≤ k`, the lifted vertex `⟨r, _⟩` is not an
endpoint of any straddle edge of stage `k+1`. Proof: any neighbour `b` of
`r` in `latticeGraph d` lies in `cubicBox d (R+1) ⊆ cubicBox d k` (via
`cubicBox_succ_of_latticeGraph_adj`), and `r ∈ cubicBox d R ⊆ cubicBox d k`,
so both endpoints of any incident edge lie in `cubicBox d k` — contradicting
`straddle_fresh_vertex` which requires at least one fresh endpoint. -/
theorem not_sym2_mem_straddle_of_cubicBox_R_succ_le_k
    (d k R : ℕ) (hRk : R + 1 ≤ k)
    {r : Fin d → ℤ} (hr : r ∈ cubicBox d R) :
    ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem
        (⟨r, cubicBox_mono d (by omega : R ≤ k + 1) hr⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e := by
  intro e he
  simp only [Finset.mem_filter] at he
  obtain ⟨he_mem, hstr⟩ := he
  -- Reduce to e = s(a, b)
  induction e with
  | h a b =>
    -- he_mem : Sym2.mk (a, b) ∈ edgeFinset
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he_mem
    -- he_mem : (inducedGraph (latticeGraph d) (cubicBox d (k+1))).Adj a b
    -- means latticeGraph d).Adj a.val b.val
    have hadj : (latticeGraph d).Adj a.val b.val := he_mem
    -- hstr : straddlePred for s(a, b)
    have hfresh := straddle_fresh_vertex hstr
    -- hfresh : a.val ∉ cubicBox d k ∨ b.val ∉ cubicBox d k
    intro hr_in
    rw [Sym2.mem_iff'] at hr_in
    -- hr_in : ⟨r, _⟩ = a ∨ ⟨r, _⟩ = b
    -- r ∈ cubicBox d R ⊆ cubicBox d k via cubicBox_mono
    have hr_in_k : r ∈ cubicBox d k := cubicBox_mono d (by omega : R ≤ k) hr
    -- Either way, the OTHER endpoint is a neighbor of r.
    rcases hr_in with hra | hrb
    · -- a.val = r
      have hav : a.val = r := by rw [← hra]
      -- b.val adj r in latticeGraph; r ∈ box_R so b ∈ box_{R+1} ⊆ box_k
      have hadj' : (latticeGraph d).Adj r b.val := by rw [← hav]; exact hadj
      have hb_in : b.val ∈ cubicBox d (R + 1) :=
        cubicBox_succ_of_latticeGraph_adj d R hr hadj'
      have hb_in_k : b.val ∈ cubicBox d k :=
        cubicBox_mono d hRk hb_in
      -- Both a.val = r ∈ box_k and b.val ∈ box_k; contradicts hfresh.
      rcases hfresh with ha_notk | hb_notk
      · exact ha_notk (hav ▸ hr_in_k)
      · exact hb_notk hb_in_k
    · -- b.val = r (symmetric)
      have hbv : b.val = r := by rw [← hrb]
      have hadj' : (latticeGraph d).Adj a.val r := by rw [← hbv]; exact hadj
      have hadj_sym : (latticeGraph d).Adj r a.val := (latticeGraph d).symm hadj'
      have ha_in : a.val ∈ cubicBox d (R + 1) :=
        cubicBox_succ_of_latticeGraph_adj d R hr hadj_sym
      have ha_in_k : a.val ∈ cubicBox d k := cubicBox_mono d hRk ha_in
      rcases hfresh with ha_notk | hb_notk
      · exact ha_notk ha_in_k
      · exact hb_notk (hbv ▸ hr_in_k)

/-- **Pair separation from `R + 1 ≤ k`** (Issue #3054, Step B capstone). The
exact `hsep` hypothesis shape required by the cubic per-stage increment bounds
(`abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow_high_temp`). Combines
two applications of `not_sym2_mem_straddle_of_cubicBox_R_succ_le_k`. -/
theorem hsep_of_cubicBox_R_succ_le_k
    (d k R : ℕ) (hRk : R + 1 ≤ k)
    {r s : Fin d → ℤ} (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R) :
    ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem
        (⟨r, cubicBox_mono d (by omega : R ≤ k + 1) hr⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e ∧
      ¬ Sym2.Mem
        (⟨s, cubicBox_mono d (by omega : R ≤ k + 1) hs⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e := fun e he =>
  ⟨not_sym2_mem_straddle_of_cubicBox_R_succ_le_k d k R hRk hr e he,
   not_sym2_mem_straddle_of_cubicBox_R_succ_le_k d k R hRk hs e he⟩

end Ambient
end IsingModel
