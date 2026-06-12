import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellInfiniteVolumeBound
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.Contraction

/-!
# Cubic-shell tight `derivBoundTight` bounded by a spatial-decay sum (Issue #2965, Phase B)

Applies the infinite-volume spatial exponential decay
`correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair` termwise to
the diagonal-free cubic-shell bound
`derivBoundTight_inducedGraph_cubic_le_infiniteVolume_sum`, replacing each
infinite-volume two-point correlation `g{x,y}` by its decay bound
`(contractionFactor)^{dist(x,y)/(r₀+2)}`.

Because the tight bound carries only the cross products
`g{r,a}·g{s,b} + g{r,b}·g{s,a}` (no diagonal `g{r,s}·g{a,b}` term), every factor
genuinely decays in the distance from `r`/`s` to the cut vertices, so this is the
diagonal-free decay-sum input from which a geometric per-stage rate is extracted
(the remaining shell-edge distance/counting aggregation is downstream).

## Main declaration

* `IsingModel.Ambient.derivBoundTight_inducedGraph_cubic_le_decay_sum`.
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

/-- **Polynomial × geometric per-stage correlation increment** (Issue #2965,
Phase B): combining the tight cubic per-stage increment
`correlationAlongExhaustion_cubic_succ_sub_le_derivBoundTight` with the
polynomial × geometric shell bound `derivBoundTight_cubic_shell_le_poly_pow`, the
successive correlation difference along the cubic exhaustion is bounded by
`β·J · 2·d·(2(k+1)+1)^d · cf^{(k+1−R)/(r₀+2)}` — a fixed polynomial in `k` times a
geometric factor `cf^{·/(r₀+2)}` with `cf < 1`, i.e. the `M·(2k+3)^d·ratio^k` form
of the per-stage increment. (The two shell terms compose directly now that the
outer induced-lattice-graph edge-set instance is the shared canonical one; see the
lowered-priority `Fintype edgeSet` fallback instances in `CubicPerStageIncrement`
and `CubicShellInfiniteVolumeBound`.) -/
theorem correlationAlongExhaustion_cubic_succ_sub_le_poly_pow (d : ℕ) (hd : 1 ≤ d)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d (cubicExhaustion d) p r₀ < 1)
    (k R : ℕ) (hRk : R ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hsep : ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem (⟨r, cubicBox_mono d (by omega) hr⟩ : (↑(cubicBox d (k + 1)) : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, cubicBox_mono d (by omega) hs⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e) :
    correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} (k + 1)
        - correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} k
      ≤ p.β * p.J * (2 * (d * (2 * (k + 1) + 1) ^ d) *
          contractionFactor d (cubicExhaustion d) p r₀ ^ ((k + 1 - R) / (r₀ + 2))) :=
  (correlationAlongExhaustion_cubic_succ_sub_le_derivBoundTight d p hf hh hrs k
    (cubicBox_mono d hRk hr) (cubicBox_mono d hRk hs) hsep).trans
    (derivBoundTight_cubic_shell_le_poly_pow d hd r₀ hr₀ p hf hh hα k R hRk hr hs hsep)

/-- **Abs form of cubic per-stage correlation increment** (Issue #3054). Combines
`correlationAlongExhaustion_cubic_succ_sub_le_poly_pow` (the one-sided ≤ form)
with the ferromagnetic monotonicity
`correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone`
(`c_k ≤ c_{k+1}` for ferromagnetic; here applied with `Λ.mono (Nat.le_succ k)`)
to give the two-sided abs bound shape required by the `h_real_inc` slots of the
poly-geometric CE-route bundle constructors (PRs #3099-#3105). -/
theorem abs_correlationAlongExhaustion_cubic_succ_sub_le_poly_pow (d : ℕ) (hd : 1 ≤ d)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d (cubicExhaustion d) p r₀ < 1)
    (k R : ℕ) (hRk : R ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hsep : ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem (⟨r, cubicBox_mono d (by omega) hr⟩ : (↑(cubicBox d (k + 1)) : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, cubicBox_mono d (by omega) hs⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e) :
    |correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} k
        - correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} (k + 1)|
      ≤ p.β * p.J * (2 * (d * (2 * (k + 1) + 1) ^ d) *
          contractionFactor d (cubicExhaustion d) p r₀ ^ ((k + 1 - R) / (r₀ + 2))) := by
  have hmono :=
    correlationAlongExhaustion_monotone (latticeGraph d) (cubicExhaustion d) p hf {r, s}
      (Nat.le_succ k)
  have hub :=
    correlationAlongExhaustion_cubic_succ_sub_le_poly_pow d hd r₀ hr₀ p hf hh hα k R hRk hrs hr hs
      hsep
  -- Since c_k ≤ c_{k+1}, c_k - c_{k+1} ≤ 0, so |c_k - c_{k+1}| = c_{k+1} - c_k.
  have hsub_nn :
      0 ≤ correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} (k + 1)
          - correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} k :=
    sub_nonneg.mpr hmono
  rw [abs_sub_comm]
  exact (abs_of_nonneg hsub_nn).trans_le hub

/-- **Cubic abs increment in direct correlation form** (Issue #3054). Rewrites
`abs_correlationAlongExhaustion_cubic_succ_sub_le_poly_pow` in the direct
`correlation (inducedGraph (latticeGraph d) (cubicBox d _)) ⟨J, 0, β⟩ (liftFinset {r, s} _)`
form, matching exactly the shape required by the `h_real_inc` slots of the
poly-geometric CE-route bundle constructors (PRs #3099-#3105). Uses
`correlationAlongExhaustion_eq_correlation_inducedGraph` to unfold both stages. -/
theorem abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow (d : ℕ) (hd : 1 ≤ d)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (J β : ℝ)
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hα : contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ < 1)
    (k R : ℕ) (hRk : R ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hsep : ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem (⟨r, cubicBox_mono d (by omega) hr⟩ : (↑(cubicBox d (k + 1)) : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, cubicBox_mono d (by omega) hs⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e)
    (hcov_k : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume k) :
    |correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume k))
          (⟨J, 0, β⟩ : IsingParams ℝ) (liftFinset {r, s} hcov_k) -
        correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume (k + 1)))
          (⟨J, 0, β⟩ : IsingParams ℝ)
          (liftFinset {r, s} (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k))))|
      ≤ β * J * (2 * (d * (2 * (k + 1) + 1) ^ d) *
          contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
            ((k + 1 - R) / (r₀ + 2))) := by
  have heq_k :
      correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} k
        = correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume k))
          (⟨J, 0, β⟩ : IsingParams ℝ) (liftFinset {r, s} hcov_k) :=
    correlationAlongExhaustion_of_subset (latticeGraph d)
      (cubicExhaustion d) _ hcov_k
  have heq_k1 :
      correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} (k + 1)
        = correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume (k + 1)))
          (⟨J, 0, β⟩ : IsingParams ℝ)
          (liftFinset {r, s} (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k)))) :=
    correlationAlongExhaustion_of_subset (latticeGraph d)
      (cubicExhaustion d) _
      (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k)))
  rw [← heq_k, ← heq_k1]
  exact abs_correlationAlongExhaustion_cubic_succ_sub_le_poly_pow d hd r₀ hr₀
    (⟨J, 0, β⟩ : IsingParams ℝ) hf rfl hα k R hRk hrs hr hs hsep

/-- **High-temperature simplification of the cubic abs increment** (Issue #3054).
Under the high-temperature condition `β · J · 2 · d ≤ 1`, the `β · J · 2 · d`
prefactor in `abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow` is
absorbed, leaving the clean poly·geometric bound
`(2k+3)^d · cf^{(k+1-R)/(r₀+2)}`. This is the form directly compatible with
the `R_inc_seq k := (2k+3)^d · ratio^k` shape required by the poly-geometric
CE-route bundle constructors (PRs #3099-#3105). Positivity of the right-hand
side uses `contractionFactor_nonneg`. -/
theorem abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow_high_temp (d : ℕ) (hd : 1 ≤ d)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (J β : ℝ)
    (hβJ2d : β * J * (2 * d) ≤ 1)
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hα : contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ < 1)
    (k R : ℕ) (hRk : R ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hsep : ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem (⟨r, cubicBox_mono d (by omega) hr⟩ : (↑(cubicBox d (k + 1)) : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, cubicBox_mono d (by omega) hs⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e)
    (hcov_k : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume k) :
    |correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume k))
          (⟨J, 0, β⟩ : IsingParams ℝ) (liftFinset {r, s} hcov_k) -
        correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume (k + 1)))
          (⟨J, 0, β⟩ : IsingParams ℝ)
          (liftFinset {r, s} (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k))))|
      ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d *
        contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
          ((k + 1 - R) / (r₀ + 2)) := by
  have hbound :=
    abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow d hd r₀ hr₀ J β hf hα k R hRk hrs hr hs
      hsep
      hcov_k
  have hcf_nn :
      (0 : ℝ) ≤ contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ :=
    contractionFactor_nonneg d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf r₀
  -- Simplify the indexing: (2 * ((k : ℝ) + 1) + 1) = ((2 * k + 3 : ℕ) : ℝ)
  have hidx : (2 * ((k : ℝ) + 1) + 1) = ((2 * k + 3 : ℕ) : ℝ) := by push_cast; ring
  -- Build the simplification inequality.
  have hcf_pow_nn :
      0 ≤ contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
            ((k + 1 - R) / (r₀ + 2)) :=
    pow_nonneg hcf_nn _
  have hpow_nn : (0 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d := pow_nonneg (by positivity) _
  have hprod_nn :
      (0 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d *
            contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((k + 1 - R) / (r₀ + 2)) := mul_nonneg hpow_nn hcf_pow_nn
  -- Rearrange the cubic bound RHS to extract β·J·2·d factor and the matching prefactor.
  -- p.β · p.J · (2 · (d · (2(k+1)+1)^d) · cf^...)
  --   = (β · J · 2 · d) · ((2k+3)^d · cf^...)
  refine hbound.trans ?_
  -- Show: β * J * (2 * (d * (2(k+1)+1)^d) * cf^...) ≤ (2k+3)^d * cf^...
  have hrhs_eq :
      β * J * (2 * ((d : ℝ) * (2 * ((k : ℝ) + 1) + 1) ^ d) *
            contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((k + 1 - R) / (r₀ + 2)))
      = (β * J * (2 * d)) *
          (((2 * k + 3 : ℕ) : ℝ) ^ d *
            contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((k + 1 - R) / (r₀ + 2))) := by
    rw [hidx]; ring
  rw [hrhs_eq]
  calc β * J * (2 * (d : ℝ)) *
          (((2 * k + 3 : ℕ) : ℝ) ^ d *
            contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((k + 1 - R) / (r₀ + 2)))
      ≤ 1 *
          (((2 * k + 3 : ℕ) : ℝ) ^ d *
            contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((k + 1 - R) / (r₀ + 2))) :=
        mul_le_mul_of_nonneg_right hβJ2d hprod_nn
    _ = ((2 * k + 3 : ℕ) : ℝ) ^ d *
            contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((k + 1 - R) / (r₀ + 2)) := one_mul _

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

/-- **Floor-power → geometric bound** (Issue #3054, Step A). For `0 < cf < 1`
and `m ≥ 1`, the natural-power `cf^⌊n/m⌋` is bounded above by `(1/cf) · ρ^n`
where `ρ := cf^(1/m)` (real power) — i.e., a clean geometric upper bound with
ratio `ρ < 1`. The floor adjustment costs at most a factor `1/cf`.

Key conversion needed to translate the cubic real-axis increment bound
`cf^⌊(k+1-R)/(r₀+2)⌋` (step-wise geometric in `k`) into the `ratio^k` shape
required by the poly-geometric CE-route bundle constructors. -/
theorem cf_pow_natDiv_le_geometric (cf : ℝ) (hcf_pos : 0 < cf) (hcf_lt_one : cf < 1)
    (m : ℕ) (hm : 0 < m) :
    let ρ := cf ^ ((1 : ℝ) / m)
    0 < ρ ∧ ρ < 1 ∧ ∀ n : ℕ, cf ^ (n / m) ≤ (1 / cf) * ρ ^ n := by
  -- Set ρ := cf^(1/m), M := 1/cf.
  refine ⟨?_, ?_, ?_⟩
  · -- 0 < cf^(1/m)
    exact Real.rpow_pos_of_pos hcf_pos _
  · -- cf^(1/m) < 1
    have hm_pos : (0 : ℝ) < 1 / m := by
      have hm_pos' : (0 : ℝ) < m := by exact_mod_cast hm
      positivity
    exact Real.rpow_lt_one hcf_pos.le hcf_lt_one hm_pos
  · intro n
    -- Strategy: cf^(n/m : ℕ) = Real.rpow cf (n/m : ℕ : ℝ)
    --        ≤ Real.rpow cf ((n : ℝ)/m - 1) since (n/m : ℕ : ℝ) ≥ (n : ℝ)/m - 1
    --        = cf⁻¹ * Real.rpow cf ((n : ℝ)/m)
    --        = cf⁻¹ * (cf^(1/m))^n
    --        = (1/cf) * ρ^n
    have hm_pos_real : (0 : ℝ) < m := by exact_mod_cast hm
    have h_floor_le : ((n : ℝ) / m - 1) ≤ ((n / m : ℕ) : ℝ) := by
      -- (n/m : ℕ) * m + (n % m) = n, n % m < m, so (n/m : ℕ) * m > n - m, i.e.,
      -- (n/m : ℕ) > n/m - 1 (real).
      have h_div_add : (n / m : ℕ) * m + n % m = n := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod n m
      have h_mod_lt : (n % m : ℕ) < m := Nat.mod_lt n hm
      have h_div_real : ((n / m : ℕ) : ℝ) * m = (n : ℝ) - ((n % m : ℕ) : ℝ) := by
        have hcast : (((n / m : ℕ) * m + n % m : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast h_div_add
        push_cast at hcast
        linarith
      have h_mod_lt_real : ((n % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast h_mod_lt
      -- Want: (n : ℝ)/m - 1 ≤ ((n / m : ℕ) : ℝ)
      -- Equivalently: ((n : ℝ)/m - 1) * m ≤ ((n / m : ℕ) : ℝ) * m
      -- LHS = (n : ℝ) - m, RHS = (n : ℝ) - (n % m : ℝ) > (n : ℝ) - m. ✓
      have hgoal : ((n : ℝ) / m - 1) * m ≤ ((n / m : ℕ) : ℝ) * m := by
        rw [h_div_real]
        have : ((n : ℝ) / m - 1) * m = (n : ℝ) - m := by field_simp
        rw [this]
        linarith
      exact le_of_mul_le_mul_right hgoal hm_pos_real
    -- Use rpow_natCast to convert nat-power to rpow.
    rw [show cf ^ (n / m) = (cf : ℝ) ^ ((n / m : ℕ) : ℝ) by rw [Real.rpow_natCast]]
    -- Apply rpow monotonicity (decreasing for cf < 1)
    have h_step1 :
        (cf : ℝ) ^ ((n / m : ℕ) : ℝ) ≤ cf ^ ((n : ℝ) / m - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hcf_pos hcf_lt_one.le h_floor_le
    refine h_step1.trans ?_
    -- cf^((n:ℝ)/m - 1) = (1/cf) * cf^((n:ℝ)/m) = (1/cf) * (cf^(1/m))^n
    have h_rhs :
        cf ^ ((n : ℝ) / m - 1) = (1 / cf) * (cf ^ ((1 : ℝ) / m)) ^ n := by
      rw [Real.rpow_sub hcf_pos, Real.rpow_one]
      rw [show ((n : ℝ) / m) = ((1 : ℝ) / m) * n by ring]
      rw [Real.rpow_mul hcf_pos.le]
      rw [Real.rpow_natCast]
      ring
    rw [h_rhs]

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

/-- **Cubic abs in clean geometric high-temperature form** (Issue #3054, Step
A+B composition). Combines `abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow_high_temp`
(#3116), `hsep_of_cubicBox_R_succ_le_k` (#3118 — auto-discharges `hsep`), and
`cf_pow_natDiv_le_geometric` (#3119 — floor → geometric) to produce the cubic
real-axis abs increment bound in the clean form

    |c_k − c_{k+1}| ≤ (1/cf) · (2k+3)^d · ρ_R^{k+1−R}

with explicit `ρ_R := cf^{1/(r₀+2)} ∈ (0, 1)`. This is the direct
poly·geometric shape compatible with the `R_inc_seq k := M · (2k+3)^d · ρ_R^k`
input of `CERouteIccPolyGeometricIncrement_of_canonical_radius_sequence`
(PR #3104, modulo a constant shift `ρ_R^{1−R}`). The cubic high-temperature
hypothesis automatically discharges `hsep` via the threshold `R + 1 ≤ k`,
removing the only combinatorial side-condition. -/
theorem abs_correlation_inducedGraph_cubic_succ_sub_le_geometric_high_temp (d : ℕ) (hd : 1 ≤ d)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (J β : ℝ)
    (hβJ2d : β * J * (2 * d) ≤ 1)
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hcf_pos : 0 < contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀)
    (hα : contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ < 1)
    (k R : ℕ) (hRk : R + 1 ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hcov_k : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume k) :
    |correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume k))
          (⟨J, 0, β⟩ : IsingParams ℝ) (liftFinset {r, s} hcov_k) -
        correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume (k + 1)))
          (⟨J, 0, β⟩ : IsingParams ℝ)
          (liftFinset {r, s} (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k))))|
      ≤ (1 / contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀) *
          (((2 * k + 3 : ℕ) : ℝ) ^ d *
            (contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((1 : ℝ) / (r₀ + 2))) ^ (k + 1 - R)) := by
  -- Step 1: apply the high-temp simplification + auto-discharged hsep.
  have hsep := hsep_of_cubicBox_R_succ_le_k d k R hRk hr hs
  have hbound :=
    abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow_high_temp d hd r₀ hr₀ J β hβJ2d hf hα
      k R (by omega) hrs hr hs hsep hcov_k
  -- Step 2: apply Step A (floor → geometric) to the cf^... factor.
  -- cf_pow_natDiv_le_geometric gives cf^((k+1-R)/(r₀+2)) ≤ (1/cf) · ρ_R^(k+1-R)
  have hm_pos : 0 < r₀ + 2 := by omega
  obtain ⟨_, _, hgeom⟩ :=
    cf_pow_natDiv_le_geometric
      (contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀)
      hcf_pos hα (r₀ + 2) hm_pos
  have hcf_step := hgeom (k + 1 - R)
  -- Combine: bound ≤ (2k+3)^d · cf^... ≤ (2k+3)^d · (1/cf) · ρ_R^(k+1-R)
  refine hbound.trans ?_
  have hpoly_nn : (0 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d := pow_nonneg (by positivity) _
  have hstep : ((2 * k + 3 : ℕ) : ℝ) ^ d *
        contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
          ((k + 1 - R) / (r₀ + 2))
      ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d *
          ((1 / contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀) *
            (contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((1 : ℝ) / ((r₀ + 2 : ℕ) : ℝ))) ^ (k + 1 - R)) :=
    mul_le_mul_of_nonneg_left hcf_step hpoly_nn
  refine hstep.trans ?_
  have hcast : ((r₀ + 2 : ℕ) : ℝ) = ((r₀ : ℝ) + 2) := by push_cast; ring
  rw [hcast]
  ring_nf
  exact le_refl _

/-- **Cubic abs uniformized via `cf_max`** (Issue #3054, Step C). The
high-temperature cubic abs increment bound (#3116) with the per-β contraction
factor `cf(β)` replaced by an upper bound `cf_max < 1` valid over the
high-temperature Icc. This is the shape required for the `h_real_inc` slot of
the poly-geometric CE-route bundle constructors, where `R_inc_seq k` must be
independent of β_re.

Given a uniform upper bound `cf_max < 1` on `contractionFactor d (cubicExhaustion d)
⟨J, 0, β_re⟩ r₀` over the relevant β_re range, the cubic abs increment is
bounded by the β_re-independent sequence
`R_inc_seq k := (2k+3)^d · cf_max^{(k+1-R)/(r₀+2)}`. -/
theorem abs_correlation_inducedGraph_cubic_succ_sub_le_uniform_cf_max
    (d : ℕ) (hd : 1 ≤ d) (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (J : ℝ)
    (cf_max : ℝ) (hcf_max_lt_one : cf_max < 1)
    {β_re : ℝ} (hβ_re_lt : β_re * J * (2 * d) ≤ 1)
    (hf : Ferromagnetic (⟨J, 0, β_re⟩ : IsingParams ℝ))
    (h_cf_max : contractionFactor d (cubicExhaustion d) (⟨J, 0, β_re⟩ : IsingParams ℝ) r₀ ≤ cf_max)
    (k R : ℕ) (hRk : R + 1 ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hcov_k : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume k) :
    |correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume k))
          (⟨J, 0, β_re⟩ : IsingParams ℝ) (liftFinset {r, s} hcov_k) -
        correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume (k + 1)))
          (⟨J, 0, β_re⟩ : IsingParams ℝ)
          (liftFinset {r, s} (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k))))|
      ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d * cf_max ^ ((k + 1 - R) / (r₀ + 2)) := by
  -- Derive the per-β_re bound first.
  have h_cf_lt_one :
      contractionFactor d (cubicExhaustion d) (⟨J, 0, β_re⟩ : IsingParams ℝ) r₀ < 1 :=
    lt_of_le_of_lt h_cf_max hcf_max_lt_one
  have hsep := hsep_of_cubicBox_R_succ_le_k d k R hRk hr hs
  have hbound :=
    abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow_high_temp d hd r₀ hr₀ J β_re hβ_re_lt hf
      h_cf_lt_one k R (by omega) hrs hr hs hsep hcov_k
  -- Bound cf^((k+1-R)/(r₀+2)) ≤ cf_max^((k+1-R)/(r₀+2)) using x ≤ y, both in (0, 1) ⇒ x^p ≤ y^p.
  refine hbound.trans ?_
  have hpoly_nn : (0 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d := pow_nonneg (by positivity) _
  have h_cf_nn : (0 : ℝ) ≤ contractionFactor d (cubicExhaustion d)
      (⟨J, 0, β_re⟩ : IsingParams ℝ) r₀ :=
    contractionFactor_nonneg d (cubicExhaustion d) (⟨J, 0, β_re⟩ : IsingParams ℝ) hf r₀
  have h_cf_pow_le_max_pow :
      contractionFactor d (cubicExhaustion d) (⟨J, 0, β_re⟩ : IsingParams ℝ) r₀ ^
          ((k + 1 - R) / (r₀ + 2))
        ≤ cf_max ^ ((k + 1 - R) / (r₀ + 2)) :=
    pow_le_pow_left₀ h_cf_nn h_cf_max _
  exact mul_le_mul_of_nonneg_left h_cf_pow_le_max_pow hpoly_nn

/-- **Cubic abs uniform geometric high-temperature** (Issue #3054, Step A + Step C
composition). Combines `abs_correlation_inducedGraph_cubic_succ_sub_le_uniform_cf_max`
(#3122, Step C — uniformizing the per-β contraction factor via `cf_max`) with
`cf_pow_natDiv_le_geometric` (#3119, Step A — floor → geometric conversion) to
produce the fully-simplified bound

    |c_k − c_{k+1}| ≤ (1/cf_max) · (2k+3)^d · ρ_R_max^{k+1−R}

with explicit `ρ_R_max := cf_max^{1/(r₀+2)} ∈ (0, 1)`. β_re-independent
(everything controlled by `cf_max`) and fully geometric in `k` (no nat-floor).
This is the cleanest cubic real-axis abs increment expression compatible with
the `R_inc_seq k` input slot of the poly-geometric CE-route bundle
constructors (PRs #3099-#3105). -/
theorem abs_correlation_inducedGraph_cubic_succ_sub_le_uniform_geometric_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (J : ℝ)
    (cf_max : ℝ) (hcf_max_pos : 0 < cf_max) (hcf_max_lt_one : cf_max < 1)
    {β_re : ℝ} (hβ_re_lt : β_re * J * (2 * d) ≤ 1)
    (hf : Ferromagnetic (⟨J, 0, β_re⟩ : IsingParams ℝ))
    (h_cf_max : contractionFactor d (cubicExhaustion d) (⟨J, 0, β_re⟩ : IsingParams ℝ) r₀ ≤ cf_max)
    (k R : ℕ) (hRk : R + 1 ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hcov_k : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume k) :
    |correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume k))
          (⟨J, 0, β_re⟩ : IsingParams ℝ) (liftFinset {r, s} hcov_k) -
        correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume (k + 1)))
          (⟨J, 0, β_re⟩ : IsingParams ℝ)
          (liftFinset {r, s} (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k))))|
      ≤ (1 / cf_max) * ((2 * k + 3 : ℕ) : ℝ) ^ d *
          (cf_max ^ ((1 : ℝ) / ((r₀ + 2 : ℕ) : ℝ))) ^ (k + 1 - R) := by
  -- Step 1: Step C bound — (2k+3)^d · cf_max^((k+1-R)/(r₀+2))
  have hstep_c :=
    abs_correlation_inducedGraph_cubic_succ_sub_le_uniform_cf_max d hd r₀ hr₀ J cf_max
      hcf_max_lt_one
      hβ_re_lt hf h_cf_max k R hRk hrs hr hs hcov_k
  refine hstep_c.trans ?_
  -- Step 2: Step A on cf_max — cf_max^((k+1-R)/(r₀+2)) ≤ (1/cf_max) · ρ_R_max^(k+1-R)
  have hm_pos : 0 < r₀ + 2 := by omega
  obtain ⟨_, _, hgeom⟩ :=
    cf_pow_natDiv_le_geometric cf_max hcf_max_pos hcf_max_lt_one (r₀ + 2) hm_pos
  have hcf_geom := hgeom (k + 1 - R)
  -- Bound (2k+3)^d · cf_max^((k+1-R)/(r₀+2)) ≤ (2k+3)^d · (1/cf_max) · ρ_R_max^(k+1-R)
  have hpoly_nn : (0 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d := pow_nonneg (by positivity) _
  have hstep : ((2 * k + 3 : ℕ) : ℝ) ^ d * cf_max ^ ((k + 1 - R) / (r₀ + 2))
      ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d *
          ((1 / cf_max) * (cf_max ^ ((1 : ℝ) / ((r₀ + 2 : ℕ) : ℝ))) ^ (k + 1 - R)) :=
    mul_le_mul_of_nonneg_left hcf_geom hpoly_nn
  refine hstep.trans ?_
  ring_nf
  exact le_refl _

end Ambient
end IsingModel
