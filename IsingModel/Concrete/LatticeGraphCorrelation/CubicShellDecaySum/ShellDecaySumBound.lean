import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellInfiniteVolumeBound
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.Contraction
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.Contraction.Factor
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.Contraction.Iterated
import IsingModel.Concrete.CubicExhaustion
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.CorrelationInfinite.Bounds
import IsingModel.AmbientLatticeSum.PerStageIncrement
import IsingModel.BallBoundarySimonLieb.Tight
import IsingModel.AmbientLattice.Defs.Core
import IsingModel.Lattice
import IsingModel.Basic

/-!
# Cubic-shell decay sum (1/4): shell decay-sum bound

Structural split (1/4) of `Concrete.LatticeGraphCorrelation.CubicShellDecaySum`.  This child
holds the geometric core of the cubic-shell estimate: the termwise application of the
infinite-volume spatial exponential decay to the diagonal-free cubic-shell bound, the
geometric decay of a `contractionFactor` power at a fresh cubic vertex, the fresh-vertex
property of a straddle edge, the resulting per-stage shell bound in
`card • (2 · cf^{(k+1−R)/(r₀+2)})` form, the cubic shell edge-count bound
`d·(2(k+1)+1)^d`, and their combination into the polynomial × geometric shell bound.  See
the `Concrete.LatticeGraphCorrelation.CubicShellDecaySum` facade module for the full
contents overview.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- **Cubic-shell tight bound by a spatial-decay sum** (Issue #2965, Phase B): in
the high-temperature regime `contractionFactor d (cubicExhaustion d) p r₀ < 1`, for
sites `r, s ∈ box_n` on no edge of `E₀`, the tight ball-boundary derivative bound is
dominated by `β·J` times the edge sum of products of `contractionFactor` powers,
each exponent the lattice distance from `r`/`s` to a cut vertex divided by `r₀+2`:
`derivBoundTight … E₀ … ≤ β·J·∑_{⟨a,b⟩∈E₀}[cf^{d(r,a)/(r₀+2)}·cf^{d(s,b)/(r₀+2)} +
cf^{d(r,b)/(r₀+2)}·cf^{d(s,a)/(r₀+2)}]`. Chains
`derivBoundTight_inducedGraph_cubic_le_infiniteVolume_sum` with the per-pair decay
`correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair` applied
termwise (the distinctness `r ≠ a.val` etc. follows from `r, s` being on no
`E₀`-edge). The cross-product-only structure ensures every factor decays. -/
theorem derivBoundTight_inducedGraph_cubic_le_decay_sum (d : ℕ) (hd : 1 ≤ d) (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d (cubicExhaustion d) p r₀ < 1)
    (n : ℕ) (E₀ : Finset (Sym2 (↑(cubicBox d n) : Type _)))
    {r s : Fin d → ℤ} (hr : r ∈ cubicBox d n) (hs : s ∈ cubicBox d n)
    (hsep : ∀ e ∈ E₀, ¬ Sym2.Mem (⟨r, hr⟩ : (↑(cubicBox d n) : Type _)) e ∧
      ¬ Sym2.Mem (⟨s, hs⟩ : (↑(cubicBox d n) : Type _)) e) :
    derivBoundTight (inducedGraph (latticeGraph d) (cubicBox d n)) E₀ p ⟨r, hr⟩ ⟨s, hs⟩
      ≤ p.β * p.J * ∑ e ∈ E₀, Sym2.lift ⟨fun a b =>
          contractionFactor d (cubicExhaustion d) p r₀ ^
              (latticeDistance d r a.val / (r₀ + 2)) *
            contractionFactor d (cubicExhaustion d) p r₀ ^
              (latticeDistance d s b.val / (r₀ + 2)) +
          contractionFactor d (cubicExhaustion d) p r₀ ^
              (latticeDistance d r b.val / (r₀ + 2)) *
            contractionFactor d (cubicExhaustion d) p r₀ ^
              (latticeDistance d s a.val / (r₀ + 2)),
          fun a b => by ring⟩ e := by
  refine (derivBoundTight_inducedGraph_cubic_le_infiniteVolume_sum d p hf n E₀ hr hs).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  obtain ⟨hrmem, hsmem⟩ := hsep _ he
  have hr_a : r ≠ a.val := fun h => hrmem (Sym2.mem_iff.mpr (Or.inl (Subtype.ext h)))
  have hr_b : r ≠ b.val := fun h => hrmem (Sym2.mem_iff.mpr (Or.inr (Subtype.ext h)))
  have hs_a : s ≠ a.val := fun h => hsmem (Sym2.mem_iff.mpr (Or.inl (Subtype.ext h)))
  have hs_b : s ≠ b.val := fun h => hsmem (Sym2.mem_iff.mpr (Or.inr (Subtype.ext h)))
  have hcf_nonneg : 0 ≤ contractionFactor d (cubicExhaustion d) p r₀ :=
    contractionFactor_nonneg d (cubicExhaustion d) p hf r₀
  have dra := correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair d hd r₀ hr₀
    (cubicExhaustion d) p hf hh hα hr_a
  have drb := correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair d hd r₀ hr₀
    (cubicExhaustion d) p hf hh hα hr_b
  have dsa := correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair d hd r₀ hr₀
    (cubicExhaustion d) p hf hh hα hs_a
  have dsb := correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair d hd r₀ hr₀
    (cubicExhaustion d) p hf hh hα hs_b
  refine add_le_add
    (mul_le_mul dra dsb (correlationInfinite_nonneg _ _ _ hf _) (pow_nonneg hcf_nonneg _))
    (mul_le_mul drb dsa (correlationInfinite_nonneg _ _ _ hf _) (pow_nonneg hcf_nonneg _))

/-- **A `contractionFactor` power at a fresh cubic vertex decays at least
geometrically in the stage.** For `x ∈ box_R`, `w ∈ box_{k+1} \ box_k`, `R ≤ k`,
and `cf = contractionFactor … r₀ < 1`, the decay power `cf^{d(x,w)/(r₀+2)}` is at
most `cf^{(k+1−R)/(r₀+2)}` (the fresh vertex recedes from `x` at unit speed, so its
distance is `≥ k+1−R`, and `cf ≤ 1` is decreasing in the exponent). -/
theorem cf_pow_fresh_le {d : ℕ} {r₀ k R : ℕ} (p : IsingParams ℝ)
    (hf : Ferromagnetic p)
    (hα : contractionFactor d (cubicExhaustion d) p r₀ < 1)
    {x w : Fin d → ℤ} (hx : x ∈ cubicBox d R) (hRk : R ≤ k)
    (hw1 : w ∈ cubicBox d (k + 1)) (hw2 : w ∉ cubicBox d k) :
    contractionFactor d (cubicExhaustion d) p r₀ ^ (latticeDistance d x w / (r₀ + 2))
      ≤ contractionFactor d (cubicExhaustion d) p r₀ ^ ((k + 1 - R) / (r₀ + 2)) :=
  pow_le_pow_of_le_one
    (contractionFactor_nonneg d (cubicExhaustion d) p hf r₀) (le_of_lt hα)
    (Nat.div_le_div_right (latticeDistance_ge_of_mem_cubicBox_succ_not_mem hx hRk hw1 hw2))

/-- A straddle edge of the `box_k`-slice has at least one endpoint outside
`box_k` (hence a fresh vertex of `box_{k+1} \ box_k`): the straddle predicate says
the two endpoints lie on opposite sides of `· ∈ box_k`, so they cannot both be in
`box_k`. -/
theorem straddle_fresh_vertex {d k : ℕ} {a b : (↑(cubicBox d (k + 1)) : Type _)}
    (hstr : straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))
      (Quot.mk (Sym2.Rel _) (a, b))) :
    a.val ∉ cubicBox d k ∨ b.val ∉ cubicBox d k := by
  simp only [straddlePred, Sym2.lift_mk, Finset.mem_subtype] at hstr
  by_contra h
  simp only [not_or, not_not] at h
  exact hstr ⟨fun _ => h.2, fun _ => h.1⟩

/-- **Cubic-shell tight bound geometric in the stage** (Issue #2965, Phase B): for
`d ≥ 1`, ferromagnetic zero-field parameters, high temperature
(`cf = contractionFactor … r₀ < 1`), and a pair `r, s ∈ box_R` (`R ≤ k`) on no cut
edge of the `box_k`-slice, the tight per-stage bound over the cubic shell is at most
`β·J` times the shell cardinality times `2·cf^{(k+1−R)/(r₀+2)}`. Combines the
decay-sum bound `derivBoundTight_inducedGraph_cubic_le_decay_sum` with the
fresh-vertex distance growth `cf_pow_fresh_le`: each straddle edge has a fresh
endpoint (`straddle_fresh_vertex`) whose decay factor carries the geometric
`cf^{(k+1−R)/(r₀+2)}`, the other factor being `≤ 1`. With the shell cardinality
polynomial in `k` and `cf < 1`, this gives a summable per-stage increment. -/
theorem derivBoundTight_cubic_shell_le_card_pow (d : ℕ) (hd : 1 ≤ d) (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d (cubicExhaustion d) p r₀ < 1)
    (k R : ℕ) (hRk : R ≤ k)
    {r s : Fin d → ℤ} (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hsep : ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem (⟨r, cubicBox_mono d (by omega) hr⟩ : (↑(cubicBox d (k + 1)) : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, cubicBox_mono d (by omega) hs⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e) :
    derivBoundTight (inducedGraph (latticeGraph d) (cubicBox d (k + 1)))
        ((inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
          (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1))))) p
        ⟨r, cubicBox_mono d (by omega) hr⟩ ⟨s, cubicBox_mono d (by omega) hs⟩
      ≤ p.β * p.J *
          (((inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
            (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1))))).card •
          (2 * contractionFactor d (cubicExhaustion d) p r₀ ^ ((k + 1 - R) / (r₀ + 2)))) := by
  set cf := contractionFactor d (cubicExhaustion d) p r₀ with hcf
  have hcf_nonneg : 0 ≤ cf := contractionFactor_nonneg d (cubicExhaustion d) p hf r₀
  have hcf_le_one : cf ≤ 1 := le_of_lt hα
  have hRk1 : R ≤ k + 1 := by omega
  refine (derivBoundTight_inducedGraph_cubic_le_decay_sum d hd r₀ hr₀ p hf hh hα (k + 1) _
    (cubicBox_mono d hRk1 hr) (cubicBox_mono d hRk1 hs) hsep).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_le_card_nsmul
  intro e he
  obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  have hstr : straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))
      (Quot.mk (Sym2.Rel _) (a, b)) := (Finset.mem_filter.mp he).2
  have hpow_nonneg : ∀ m : ℕ, 0 ≤ cf ^ m := fun m => pow_nonneg hcf_nonneg m
  have hle1 : ∀ y z : Fin d → ℤ, cf ^ (latticeDistance d y z / (r₀ + 2)) ≤ 1 :=
    fun _ _ => pow_le_one₀ hcf_nonneg hcf_le_one
  rcases straddle_fresh_vertex hstr with hfa | hfb
  · -- `a` is the fresh vertex
    have hra := cf_pow_fresh_le p hf hα hr hRk a.property hfa
    have hsa := cf_pow_fresh_le p hf hα hs hRk a.property hfa
    calc
      cf ^ (latticeDistance d r a.val / (r₀ + 2)) * cf ^ (latticeDistance d s b.val / (r₀ + 2))
          + cf ^ (latticeDistance d r b.val / (r₀ + 2))
            * cf ^ (latticeDistance d s a.val / (r₀ + 2))
        ≤ cf ^ ((k + 1 - R) / (r₀ + 2)) * 1 + 1 * cf ^ ((k + 1 - R) / (r₀ + 2)) :=
          add_le_add
            (mul_le_mul hra (hle1 s b.val) (hpow_nonneg _) (hpow_nonneg _))
            (mul_le_mul (hle1 r b.val) hsa (hpow_nonneg _) zero_le_one)
      _ = 2 * cf ^ ((k + 1 - R) / (r₀ + 2)) := by ring
  · -- `b` is the fresh vertex
    have hrb := cf_pow_fresh_le p hf hα hr hRk b.property hfb
    have hsb := cf_pow_fresh_le p hf hα hs hRk b.property hfb
    calc
      cf ^ (latticeDistance d r a.val / (r₀ + 2)) * cf ^ (latticeDistance d s b.val / (r₀ + 2))
          + cf ^ (latticeDistance d r b.val / (r₀ + 2))
            * cf ^ (latticeDistance d s a.val / (r₀ + 2))
        ≤ 1 * cf ^ ((k + 1 - R) / (r₀ + 2)) + cf ^ ((k + 1 - R) / (r₀ + 2)) * 1 :=
          add_le_add
            (mul_le_mul (hle1 r a.val) hsb (hpow_nonneg _) zero_le_one)
            (mul_le_mul hrb (hle1 s a.val) (hpow_nonneg _) (hpow_nonneg _))
      _ = 2 * cf ^ ((k + 1 - R) / (r₀ + 2)) := by ring

/-- **Cubic shell edge-count bound**: the number of cut edges of the `box_k`-slice
inside `box_{k+1}` is at most `d·(2(k+1)+1)^d` (the shell is a subset of the
induced-graph edge set, which the handshake bound
`inducedLatticeGraph_card_edgeFinset_le` controls by `d·|box_{k+1}|`, and
`|box_{k+1}| = (2(k+1)+1)^d` by `card_cubicBox`). -/
theorem cubic_shell_card_le (d k : ℕ) :
    (((inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1))))).card : ℝ)
      ≤ (d : ℝ) * (2 * (k + 1) + 1) ^ d := by
  calc (((inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
          (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1))))).card : ℝ)
      ≤ ((inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.card : ℝ) := by
        exact_mod_cast Finset.card_filter_le _ _
    _ ≤ (d : ℝ) * Fintype.card (↑(cubicBox d (k + 1)) : Type _) :=
        inducedLatticeGraph_card_edgeFinset_le d (cubicBox d (k + 1))
    _ = (d : ℝ) * (2 * (k + 1) + 1) ^ d := by
        rw [Fintype.card_coe, card_cubicBox]; push_cast; ring

/-- **Geometric per-stage shell bound in polynomial × geometric form** (Issue
#2965, Phase B): combining the geometric shell bound
`derivBoundTight_cubic_shell_le_card_pow` with the shell edge-count bound
`cubic_shell_card_le`, the tight ball-boundary derivative bound over the cubic shell
is at most `β·J · 2·d·(2(k+1)+1)^d · cf^{(k+1−R)/(r₀+2)}` — a fixed polynomial in
`k` times a geometric factor `cf^{·/(r₀+2)}` with `cf < 1`, the `M·(2k+3)^d·ratio^k`
shape required by the volume-convergence-rate capstone. Chains directly with the
tight per-stage correlation increment
`correlationAlongExhaustion_cubic_succ_sub_le_derivBoundTight` (see
`correlationAlongExhaustion_cubic_succ_sub_le_poly_pow`) now that the outer
induced-lattice-graph edge-set instance is the shared canonical one. -/
theorem derivBoundTight_cubic_shell_le_poly_pow (d : ℕ) (hd : 1 ≤ d)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d (cubicExhaustion d) p r₀ < 1)
    (k R : ℕ) (hRk : R ≤ k)
    {r s : Fin d → ℤ} (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hsep : ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem (⟨r, cubicBox_mono d (by omega) hr⟩ : (↑(cubicBox d (k + 1)) : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, cubicBox_mono d (by omega) hs⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e) :
    derivBoundTight (inducedGraph (latticeGraph d) (cubicBox d (k + 1)))
        ((inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
          (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1))))) p
        ⟨r, cubicBox_mono d (by omega) hr⟩ ⟨s, cubicBox_mono d (by omega) hs⟩
      ≤ p.β * p.J * (2 * (d * (2 * (k + 1) + 1) ^ d) *
          contractionFactor d (cubicExhaustion d) p r₀ ^ ((k + 1 - R) / (r₀ + 2))) := by
  have h2 := derivBoundTight_cubic_shell_le_card_pow d hd r₀ hr₀ p hf hh hα k R hRk hr hs hsep
  have hcard := cubic_shell_card_le d k
  have hpow_nonneg : 0 ≤ 2 * contractionFactor d (cubicExhaustion d) p r₀ ^
      ((k + 1 - R) / (r₀ + 2)) :=
    mul_nonneg (by norm_num)
      (pow_nonneg (contractionFactor_nonneg d (cubicExhaustion d) p hf r₀) _)
  have hβJ : 0 ≤ p.β * p.J := mul_nonneg hf.hβ.le hf.hJ
  refine h2.trans ?_
  rw [nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ hβJ
  calc _
      ≤ ((d : ℝ) * (2 * (k + 1) + 1) ^ d) *
          (2 * contractionFactor d (cubicExhaustion d) p r₀ ^ ((k + 1 - R) / (r₀ + 2))) :=
        mul_le_mul_of_nonneg_right hcard hpow_nonneg
    _ = 2 * ((d : ℝ) * (2 * (k + 1) + 1) ^ d) *
          contractionFactor d (cubicExhaustion d) p r₀ ^ ((k + 1 - R) / (r₀ + 2)) := by ring

end Ambient
end IsingModel
