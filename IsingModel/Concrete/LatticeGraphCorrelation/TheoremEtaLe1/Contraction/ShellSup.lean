import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.BallDefs
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.BallBoundaryInfinite
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationVadd
import IsingModel.Concrete.LatticeSphereCard
import IsingModel.TranslationInvariance.Truncated
import IsingModel.LatticeExpSum
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.Contraction.Factor

/-!
# Theorem eta-le-1 split — Phase 6: shell-supremum contraction

Part of the split eta<=1 polynomial-to-exponential decay layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Phase 6: Shell-supremum contraction -/

/-- **Nonemptiness of a distance shell**: for `1 ≤ d` and `1 ≤ m` the shell
`{y : Fin d → ℤ // m ≤ latticeDistance d 0 y ∧ y ≠ 0}` is nonempty (the point with
first coordinate `m`). -/
private theorem shell_nonempty {d : ℕ} (hd : 1 ≤ d) {m : ℕ} (hm : 1 ≤ m) :
    Nonempty {y : Fin d → ℤ // m ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0} := by
  let y₀ : Fin d → ℤ := fun i => if i = (⟨0, by omega⟩ : Fin d) then (m : ℤ) else 0
  refine ⟨⟨y₀, ?_, ?_⟩⟩
  · unfold IsingModel.latticeDistance y₀
    simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg]
    let f : Fin d → ℕ := fun i => (if i = (⟨0, by omega⟩ : Fin d) then (m : ℤ) else 0).natAbs
    have hle : f (⟨0, by omega⟩ : Fin d) ≤ ∑ i : Fin d, f i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
    have hf0 : f (⟨0, by omega⟩ : Fin d) = m := by
      simp [f]
    calc m = f (⟨0, by omega⟩ : Fin d) := hf0.symm
      _ ≤ ∑ i : Fin d, f i := hle
  · intro h
    have := congrFun h (⟨0, by omega⟩ : Fin d)
    simp only [y₀, if_pos rfl, Pi.zero_apply] at this
    omega

/-- **Boundary-edge endpoints are within distance `r + 1`**: every endpoint of a
ball-boundary edge has `latticeDistance d 0 · ≤ r + 1` (the inside endpoint is at
distance `≤ r`, the outside one at exactly `r + 1`). -/
theorem latticeBallBoundaryEdges_dist_le {d r : ℕ} {k l : Fin d → ℤ}
    (h : s(k, l) ∈ latticeBallBoundaryEdges d r) :
    IsingModel.latticeDistance d 0 k ≤ r + 1 ∧ IsingModel.latticeDistance d 0 l ≤ r + 1 := by
  obtain ⟨hadj, hstr⟩ := mem_latticeBallBoundaryEdges.mp h
  have hlk : IsingModel.latticeDistance d l k = 1 :=
    (latticeGraph_adj_iff_latticeDistance_eq_one d l k).mp hadj.symm
  have hkl : IsingModel.latticeDistance d k l = 1 :=
    (latticeGraph_adj_iff_latticeDistance_eq_one d k l).mp hadj
  have h1 := IsingModel.latticeDistance_triangle d 0 l k
  have h2 := IsingModel.latticeDistance_triangle d 0 k l
  by_cases hA : IsingModel.latticeDistance d 0 k ≤ r
  · exact ⟨by omega, by omega⟩
  · have hB : IsingModel.latticeDistance d 0 l ≤ r := by
      by_contra hB
      exact hstr (propext ⟨fun h => absurd h hA, fun h => absurd h hB⟩)
    exact ⟨by omega, by omega⟩

set_option maxHeartbeats 1600000 in
-- The proof per shell point applies the ball-boundary inequality, translation
-- invariance, and a triangle-inequality shell bound, then aggregates over the
-- boundary-edge sum; the combined elaboration exceeds the default heartbeat limit.
/-- **Shell supremum contraction** (key inductive step of GJ §17.8, p. 317;
formerly an axiom): for `1 ≤ r` and `n > r + 1`,

`⨆ {|y| ≥ n} corr∞{0, y} ≤ contractionFactor d Λ p r * ⨆ {|y| ≥ n - r - 1} corr∞{0, y}`.

For each `y` with `|y| ≥ n`, `ball_boundary_tight_infinite` gives
`corr∞{0,y} ≤ βJ·∑_{(k,l)∈∂B_r}[corr∞{0,k}·corr∞{l,y} + corr∞{0,l}·corr∞{k,y}]`;
translation invariance turns `corr∞{l,y}` into `corr∞{0,y−l}` with
`|y−l| ≥ |y| − (r+1) ≥ n − r − 1` (boundary endpoints have distance `≤ r+1`), so
each `corr∞{l,y}, corr∞{k,y}` is `≤` the `(n−r−1)`-shell supremum `S`, whence
`corr∞{0,y} ≤ (βJ·∑(corr∞{0,k}+corr∞{0,l}))·S = contractionFactor · S`.

The hypothesis `1 ≤ r` (new relative to the former axiom) is required because
`ball_boundary_tight_infinite` is false at `r = 0`. -/
theorem shellSup_contraction (d : ℕ) (hd : 1 ≤ d)
    (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (n : ℕ) (hn : r + 1 < n) :
    ⨆ (y : {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
        correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val}
      ≤ contractionFactor d Λ p r *
        ⨆ (y : {y : Fin d → ℤ // (n - r - 1) ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val} := by
  classical
  have hβJ : 0 ≤ p.β * p.J := mul_nonneg hf.hβ.le hf.hJ
  -- The (n-r-1)-shell supremum `S`.
  set S := ⨆ (z : {z : Fin d → ℤ // (n - r - 1) ≤ IsingModel.latticeDistance d 0 z ∧ z ≠ 0}),
      correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), z.val} with hSdef
  have hSbdd : BddAbove (Set.range
      (fun z : {z : Fin d → ℤ // (n - r - 1) ≤ IsingModel.latticeDistance d 0 z ∧ z ≠ 0} =>
        correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), z.val})) := by
    refine ⟨1, ?_⟩
    rintro x ⟨z, rfl⟩
    exact correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _
  -- `S ≥ 0`.
  haveI hSne : Nonempty {z : Fin d → ℤ // (n - r - 1) ≤ IsingModel.latticeDistance d 0 z ∧ z ≠ 0} :=
    shell_nonempty hd (by omega)
  have hSnonneg : 0 ≤ S := by
    rw [hSdef]
    exact le_ciSup_of_le hSbdd (Classical.arbitrary _)
      (correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _)
  haveI hLne : Nonempty {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0} :=
    shell_nonempty hd (by omega)
  apply ciSup_le
  rintro ⟨y, hyn, hy0⟩
  -- Per shell point `y`: apply the ball-boundary inequality.
  have hx : r + 1 < IsingModel.latticeDistance d 0 y := by omega
  have hbb := ball_boundary_tight_infinite d hd r hr Λ p hf hh y hx
  -- Bound each boundary endpoint's far correlation by `S`.
  have hfar : ∀ {w : Fin d → ℤ}, IsingModel.latticeDistance d 0 w ≤ r + 1 →
      correlationInfinite (IsingModel.latticeGraph d) Λ p {w, y} ≤ S := by
    intro w hw
    -- corr∞{w, y} = corr∞{0, y - w} by translation invariance.
    have hvadd : correlationInfinite (IsingModel.latticeGraph d) Λ p
        (vaddFinset (-w) ({w, y} : Finset (Fin d → ℤ)))
        = correlationInfinite (IsingModel.latticeGraph d) Λ p ({w, y} : Finset (Fin d → ℤ)) :=
      correlationInfinite_latticeGraph_vaddFinset_of_translationInvariant d Λ (-w) p hf {w, y}
    rw [vaddFinset_pair] at hvadd
    simp only [vadd_eq_add, neg_add_cancel, neg_add_eq_sub] at hvadd
    -- hvadd : corr∞{0, y - w} = corr∞{w, y}
    rw [← hvadd]
    -- distance of `y - w` to the origin.
    have hd_eq : IsingModel.latticeDistance d 0 (y - w) = IsingModel.latticeDistance d w y := by
      unfold IsingModel.latticeDistance
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Pi.sub_apply, Pi.zero_apply, zero_sub, Int.natAbs_neg]
      rw [show w i - y i = -(y i - w i) from by ring, Int.natAbs_neg]
    have htri := IsingModel.latticeDistance_triangle d 0 w y
    have hdist_yw : n - r - 1 ≤ IsingModel.latticeDistance d 0 (y - w) := by
      rw [hd_eq]; omega
    have hne_yw : y - w ≠ 0 := by
      intro h
      rw [h] at hdist_yw
      simp only [IsingModel.latticeDistance_self] at hdist_yw
      omega
    rw [hSdef]
    exact le_ciSup_of_le hSbdd ⟨y - w, hdist_yw, hne_yw⟩ le_rfl
  -- Aggregate over the boundary-edge sum.
  refine le_trans hbb ?_
  have hsum : (∑ e ∈ latticeBallBoundaryEdges d r,
      Sym2.lift ⟨fun k l =>
        correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {l, y}
        + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {k, y},
      fun k l => by ring⟩ e)
      ≤ (∑ e ∈ latticeBallBoundaryEdges d r,
          Sym2.lift ⟨fun k l =>
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
              + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l},
          fun k l => by ring⟩ e) * S := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun e he => ?_)
    obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
    obtain ⟨hdk, hdl⟩ := latticeBallBoundaryEdges_dist_le he
    have hly : correlationInfinite (IsingModel.latticeGraph d) Λ p {l, y} ≤ S := hfar hdl
    have hky : correlationInfinite (IsingModel.latticeGraph d) Λ p {k, y} ≤ S := hfar hdk
    have h0k : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k} :=
      correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
    have h0l : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l} :=
      correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
    nlinarith [mul_le_mul_of_nonneg_left hly h0k, mul_le_mul_of_nonneg_left hky h0l]
  calc p.β * p.J * (∑ e ∈ latticeBallBoundaryEdges d r,
          Sym2.lift ⟨fun k l =>
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
              * correlationInfinite (IsingModel.latticeGraph d) Λ p {l, y}
            + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l}
              * correlationInfinite (IsingModel.latticeGraph d) Λ p {k, y},
          fun k l => by ring⟩ e)
      ≤ p.β * p.J * ((∑ e ∈ latticeBallBoundaryEdges d r,
          Sym2.lift ⟨fun k l =>
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
              + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l},
          fun k l => by ring⟩ e) * S) := mul_le_mul_of_nonneg_left hsum hβJ
    _ = contractionFactor d Λ p r * S := by rw [contractionFactor]; ring

end Ambient
end IsingModel
