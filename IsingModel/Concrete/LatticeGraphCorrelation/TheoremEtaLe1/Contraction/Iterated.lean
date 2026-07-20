import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.BallDefs
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.BallBoundaryInfinite
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationVadd
import IsingModel.Concrete.LatticeSphereCard
import IsingModel.TranslationInvariance.Truncated
import IsingModel.LatticeExpSum
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.Contraction.ShellSup

/-!
# Theorem eta-le-1 split — Phase 7: iterated contraction bound and decay corollaries

Part of the split eta<=1 polynomial-to-exponential decay layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Phase 7: Iterated contraction bound (axiom) -/

/-- **Shell supremum iterated bound** (axiom, iterated application of `shellSup_contraction`):

Fix `r : ℕ` and `α = contractionFactor d Λ p r` with `α < 1`. Set step size `s = r + 2`.
For all `k : ℕ` and all `n ≥ k * s`:

  `⨆ {|y| ≥ n} corr∞{0, y} ≤ α^k`

**Proof sketch (deferred)**: By induction on `k`.
- Base `k = 0`: the sup is `≤ 1 = α^0` from `correlationInfinite_le_one`.
- Step: for `n ≥ (k+1) * s = k * s + r + 2 > r + 1`,
  apply `shellSup_contraction` at `n` to get
  `sup(n) ≤ α * sup(n - r - 1)`.
  Since `n - r - 1 ≥ k * s`, the inductive hypothesis gives `sup(n - r - 1) ≤ α^k`.
  Thus `sup(n) ≤ α * α^k = α^(k+1)`.

Reference: Glimm–Jaffe §17.8 proof of Thm 17.8.1, p. 317. -/
theorem shellSup_iterated_bound (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (_hα : contractionFactor d Λ p r < 1)
    (k : ℕ) : ∀ n : ℕ, k * (r + 2) ≤ n →
    ⨆ (y : {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
        correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val}
      ≤ (contractionFactor d Λ p r) ^ k := by
  induction k with
  | zero =>
    intro n _
    simp only [pow_zero]
    -- For any n and d ≥ 1, the index type is nonempty:
    -- take y = (n+1, 0, ..., 0), which has latticeDistance = n+1 ≥ n and y ≠ 0.
    haveI hnem : Nonempty {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0} := by
      let y₀ : Fin d → ℤ := fun i => if i = ⟨0, by omega⟩ then (n : ℤ) + 1 else 0
      refine ⟨⟨y₀, ?_, ?_⟩⟩
      · -- n ≤ latticeDistance d 0 y₀
        unfold IsingModel.latticeDistance y₀
        simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg]
        let f : Fin d → ℕ := fun i =>
          (if i = (⟨0, by omega⟩ : Fin d) then (n : ℤ) + 1 else 0).natAbs
        have hle : f (⟨0, by omega⟩ : Fin d) ≤ ∑ i : Fin d, f i :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
        have hf0 : f (⟨0, by omega⟩ : Fin d) = n + 1 := by
          simp only [f, ite_true]; norm_cast
        calc n ≤ n + 1 := Nat.le_succ n
          _ = f (⟨0, by omega⟩ : Fin d) := hf0.symm
          _ ≤ ∑ i : Fin d, f i := hle
      · -- y₀ ≠ 0
        intro h
        have := congrFun h (⟨0, by omega⟩ : Fin d)
        simp only [y₀, ite_true, Pi.zero_apply] at this
        omega
    apply ciSup_le
    rintro ⟨y, -, -⟩
    exact correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _
  | succ k ih =>
    intro n hn
    -- n ≥ (k+1)*(r+2) ≥ r+2 > r+1
    have hn_gt : r + 1 < n := by
      have h1 : (k + 1) * (r + 2) ≥ r + 2 := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
      omega
    -- Apply shellSup_contraction
    have hstep : k * (r + 2) ≤ n - r - 1 := by
      have h1 : (k + 1) * (r + 2) = k * (r + 2) + (r + 2) := by ring
      omega
    calc ⨆ (y : {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val}
        ≤ contractionFactor d Λ p r *
          ⨆ (y : {y : Fin d → ℤ // (n - r - 1) ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
              correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val} :=
              shellSup_contraction d hd r hr Λ p hf hh n hn_gt
      _ ≤ contractionFactor d Λ p r * (contractionFactor d Λ p r) ^ k :=
          mul_le_mul_of_nonneg_left (ih (n - r - 1) hstep) (contractionFactor_nonneg d Λ p hf r)
      _ = (contractionFactor d Λ p r) ^ (k + 1) := by rw [pow_succ]; ring

/-- **Pointwise spatial exponential decay of the infinite-volume correlation**:
the shell-iterated bound specializes to a per-point estimate
`⟨σ_0σ_y⟩^∞ ≤ (contractionFactor d Λ p r)^{dist(0,y) / (r+2)}` for every `y ≠ 0`,
where the exponent is the natural-number division `dist(0,y) / (r+2)`.

Since `(dist(0,y) / (r+2)) · (r+2) ≤ dist(0,y)`, the point `y` lies in the
distance-`dist(0,y)` shell, so its correlation is bounded by the shell supremum,
which `shellSup_iterated_bound` controls by `(contractionFactor)^{dist/(r+2)}`.
This is the prefactor-free spatial exponential decay in the form used by the
finite-volume convergence-rate program (Issue #2931, Phase 3a/3b′). -/
theorem correlationInfinite_latticeGraph_le_contractionFactor_pow_dist
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d Λ p r < 1) {y : Fin d → ℤ} (hy : y ≠ 0) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y}
      ≤ (contractionFactor d Λ p r) ^ (IsingModel.latticeDistance d 0 y / (r + 2)) := by
  set k := IsingModel.latticeDistance d 0 y / (r + 2) with hk
  have hkr : k * (r + 2) ≤ IsingModel.latticeDistance d 0 y := Nat.div_mul_le_self _ _
  have hbound :=
    shellSup_iterated_bound d hd r hr Λ p hf hh hα k (IsingModel.latticeDistance d 0 y) hkr
  have hbdd :
      BddAbove (Set.range (fun z : {z : Fin d → ℤ //
          IsingModel.latticeDistance d 0 y ≤ IsingModel.latticeDistance d 0 z ∧ z ≠ 0} =>
        correlationInfinite (IsingModel.latticeGraph d) Λ p
          {(0 : Fin d → ℤ), z.val})) := by
    refine ⟨1, ?_⟩
    rintro x ⟨z, rfl⟩
    exact correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _
  have hle :
      correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y}
        ≤ ⨆ (z : {z : Fin d → ℤ //
            IsingModel.latticeDistance d 0 y ≤ IsingModel.latticeDistance d 0 z ∧ z ≠ 0}),
          correlationInfinite (IsingModel.latticeGraph d) Λ p
            {(0 : Fin d → ℤ), z.val} :=
    le_ciSup hbdd ⟨y, le_rfl, hy⟩
  exact hle.trans hbound

/-- **Pointwise spatial exponential decay for an arbitrary pair**: translation
invariance extends the anchored bound to any distinct pair `i ≠ j`,
`⟨σ_iσ_j⟩^∞ ≤ (contractionFactor d Λ p r)^{dist(i,j) / (r+2)}`.

The correlation is translation invariant
(`correlationInfinite_vaddFinset_of_translationInvariant`), so
`⟨σ_iσ_j⟩^∞ = ⟨σ_0σ_{j-i}⟩^∞`, and the ℓ¹ lattice distance is likewise
translation invariant, `dist(i,j) = dist(0, j-i)`; the anchored bound
`correlationInfinite_latticeGraph_le_contractionFactor_pow_dist` then applies at
`y = j - i ≠ 0`.  This is the per-pair prefactor-free spatial decay used by the
finite-volume convergence-rate program (Issue #2931, Phase 3a/3b′). -/
theorem correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d Λ p r < 1) {i j : Fin d → ℤ} (hij : i ≠ j) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
      ≤ (contractionFactor d Λ p r) ^ (IsingModel.latticeDistance d i j / (r + 2)) := by
  -- Translation invariance: `⟨σ_iσ_j⟩^∞ = ⟨σ_0σ_{j-i}⟩^∞`.
  have htrans :
      correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
        = correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), j - i} := by
    rw [show ({i, j} : Finset (Fin d → ℤ)) = vaddFinset i {(0 : Fin d → ℤ), j - i} from by
      rw [vaddFinset_pair]; simp [vadd_eq_add]]
    exact correlationInfinite_vaddFinset_of_translationInvariant
      (IsingModel.latticeGraph d) Λ i p hf {(0 : Fin d → ℤ), j - i}
  -- The ℓ¹ distance is translation invariant: `dist(i,j) = dist(0, j-i)`.
  have hdist : IsingModel.latticeDistance d i j
      = IsingModel.latticeDistance d 0 (j - i) := by
    unfold IsingModel.latticeDistance
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Pi.zero_apply, zero_sub, Pi.sub_apply]
    congr 1; ring
  -- `j - i ≠ 0` since `i ≠ j`.
  have hjmi_ne : j - i ≠ 0 := fun h => hij (by
    have hji : j = i + (j - i) := by abel
    rw [h, add_zero] at hji; exact hji.symm)
  rw [htrans, hdist]
  exact correlationInfinite_latticeGraph_le_contractionFactor_pow_dist
    d hd r hr Λ p hf hh hα hjmi_ne

/-- **Uniform clustering at large distance**: when the contraction factor is
`< 1`, the infinite-volume pair correlation is uniformly small at large lattice
distance — for every `ε > 0` there is `R` such that
`⟨σ_iσ_j⟩^∞ ≤ ε` for all pairs with `dist(i,j) ≥ R`.

Since `contractionFactor d Λ p r < 1`, some power `(contractionFactor)^m < ε`;
taking `R = (m+1)(r+2)` forces `dist(i,j)/(r+2) ≥ m`, so the per-pair spatial
decay bound `correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair`
gives `⟨σ_iσ_j⟩^∞ ≤ (contractionFactor)^{dist/(r+2)} ≤ (contractionFactor)^m < ε`.
This is the uniform clustering property of the infinite-volume measure
(Issue #2931, Phase 3a). -/
theorem correlationInfinite_latticeGraph_uniform_decay_of_contractionFactor_lt_one
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d Λ p r < 1) :
    ∀ ε > (0 : ℝ), ∃ R : ℕ, ∀ i j : Fin d → ℤ,
      R ≤ IsingModel.latticeDistance d i j →
        correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} ≤ ε := by
  intro ε hε
  have hcf0 : 0 ≤ contractionFactor d Λ p r := contractionFactor_nonneg d Λ p hf r
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hα
  refine ⟨(m + 1) * (r + 2), fun i j hR => ?_⟩
  by_cases hij : i = j
  · exfalso
    rw [hij, IsingModel.latticeDistance_self] at hR
    have : 0 < (m + 1) * (r + 2) := Nat.mul_pos (Nat.succ_pos m) (by omega)
    omega
  · have hbound :=
      correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair
        d hd r hr Λ p hf hh hα hij
    have hexp : m ≤ IsingModel.latticeDistance d i j / (r + 2) := by
      have hge : (m + 1) ≤ IsingModel.latticeDistance d i j / (r + 2) := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < r + 2)]
        exact hR
      omega
    have hmono :
        (contractionFactor d Λ p r) ^ (IsingModel.latticeDistance d i j / (r + 2))
          ≤ (contractionFactor d Λ p r) ^ m :=
      pow_le_pow_of_le_one hcf0 hα.le hexp
    calc correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
        ≤ (contractionFactor d Λ p r) ^ (IsingModel.latticeDistance d i j / (r + 2)) := hbound
      _ ≤ (contractionFactor d Λ p r) ^ m := hmono
      _ ≤ ε := hm.le

/-- **The infinite-volume correlation kernel vanishes at infinity (cofinite)**:
when the contraction factor is `< 1`, `y ↦ ⟨σ_0σ_y⟩^∞` tends to `0` along the
cofinite filter on `ℤ^d`.

This is the `C₀`/clustering form of the uniform large-distance decay: for every
`ε > 0` the exceptional set `{y : ε ≤ ⟨σ_0σ_y⟩^∞}` is contained in the finite
lattice ball `{y : dist(0,y) ≤ R}` (by
`correlationInfinite_latticeGraph_uniform_decay_of_contractionFactor_lt_one` and
the finiteness of lattice balls `latticeDistance_le_finite`), hence finite, so
the values are eventually below `ε`.  Part of Issue #2931. -/
theorem correlationInfinite_latticeGraph_tendsto_cofinite_zero
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d Λ p r < 1) :
    Filter.Tendsto
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y})
      Filter.cofinite (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR⟩ :=
    correlationInfinite_latticeGraph_uniform_decay_of_contractionFactor_lt_one
      d hd r hr Λ p hf hh hα (ε / 2) (by linarith)
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (IsingModel.latticeDistance_le_finite d 0 R) ?_
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  by_contra hcontra
  have hge : R ≤ IsingModel.latticeDistance d 0 y := le_of_lt (not_le.mp hcontra)
  have hcorr_le := hR 0 y hge
  have hcorr_nn := correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf
    {(0 : Fin d → ℤ), y}
  apply hy
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hcorr_nn]
  linarith

/-- **Finite susceptibility from the contraction factor**: when
`0 < contractionFactor d Λ p r < 1`, the infinite-volume correlation kernel
`y ↦ ⟨σ_0σ_y⟩^∞` is summable over `ℤ^d`, i.e. the magnetic susceptibility
`χ = ∑_y ⟨σ_0σ_y⟩^∞` is finite.

The per-pair spatial decay `⟨σ_0σ_y⟩^∞ ≤ (contractionFactor)^{dist(0,y)/(r+2)}`
is dominated by `(1/contractionFactor)·exp(-m·dist(0,y))` with
`m = -log(contractionFactor)/(r+2) > 0` (using
`(cf)^{⌊dist/(r+2)⌋} ≤ (cf)^{dist/(r+2)-1} = (1/cf)·exp(-m·dist)`), and the
exponential kernel is summable over the lattice by `summable_exp_neg_dist`; the
comparison test concludes.  Part of Issue #2931. -/
theorem correlationInfinite_latticeGraph_susceptibility_summable
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hcf_pos : 0 < contractionFactor d Λ p r) (hα : contractionFactor d Λ p r < 1) :
    Summable
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y}) := by
  set cf := contractionFactor d Λ p r with hcfdef
  set m := -Real.log cf / (r + 2 : ℝ) with hmdef
  have hr2_pos : (0 : ℝ) < (r + 2 : ℝ) := by positivity
  have hlog_neg : Real.log cf < 0 := Real.log_neg hcf_pos hα
  have hm_pos : 0 < m := by
    rw [hmdef]; exact div_pos (by linarith [hlog_neg]) hr2_pos
  have hmaj_sum :
      Summable (fun y : Fin d → ℤ =>
        (1 / cf) * Real.exp (-m * (IsingModel.latticeDistance d 0 y : ℝ))) :=
    (summable_exp_neg_dist hm_pos d 0).mul_left (1 / cf)
  refine Summable.of_nonneg_of_le
    (fun y => correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _)
    (fun y => ?_) hmaj_sum
  by_cases hy : y = 0
  · -- `dist(0,0) = 0`: majorant is `1/cf ≥ 1 ≥ correlation`.
    subst hy
    have hone : correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), 0} ≤ 1 :=
      correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _
    have hinv : (1 : ℝ) ≤ 1 / cf := by
      rw [le_div_iff₀ hcf_pos]; linarith
    have hdist0 : IsingModel.latticeDistance d 0 (0 : Fin d → ℤ) = 0 :=
      IsingModel.latticeDistance_self d 0
    rw [hdist0]
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    linarith
  · have hbound :=
      correlationInfinite_latticeGraph_le_contractionFactor_pow_dist d hd r hr Λ p hf hh hα hy
    -- `cf^q ≤ (1/cf)·exp(-m·dist)` with `q = dist/(r+2)`.
    set n := IsingModel.latticeDistance d 0 y with hndef
    have hq_real : ((n / (r + 2) : ℕ) : ℝ) ≥ (n : ℝ) / (r + 2 : ℝ) - 1 := by
      have hlt : n < (n / (r + 2) + 1) * (r + 2) := by
        have hmod := Nat.mod_lt n (show 0 < r + 2 by omega)
        have hdm := Nat.div_add_mod n (r + 2)
        nlinarith [hmod, hdm]
      have hlt' : (n : ℝ) < ((n / (r + 2) : ℕ) : ℝ) * (r + 2 : ℝ) + (r + 2 : ℝ) := by
        have := (Nat.cast_lt (α := ℝ)).2 hlt
        push_cast at this ⊢; nlinarith [this]
      rw [ge_iff_le, sub_le_iff_le_add, div_le_iff₀ hr2_pos]
      nlinarith [hlt']
    have hcfle1 : cf ≤ 1 := hα.le
    -- `cf^(q:ℕ) = cf^(q:ℝ) ≤ cf^((n/(r+2)) - 1)` (base in (0,1], exponent larger).
    have hstep1 :
        cf ^ (n / (r + 2)) ≤ cf ^ ((n : ℝ) / (r + 2 : ℝ) - 1) := by
      rw [← Real.rpow_natCast cf (n / (r + 2))]
      exact Real.rpow_le_rpow_of_exponent_ge hcf_pos hcfle1 hq_real
    have hstep2 :
        cf ^ ((n : ℝ) / (r + 2 : ℝ) - 1)
          = (1 / cf) * Real.exp (-m * (n : ℝ)) := by
      rw [Real.rpow_sub hcf_pos, Real.rpow_one, Real.rpow_def_of_pos hcf_pos,
        one_div, div_eq_mul_inv, mul_comm (cf⁻¹) (Real.exp (-m * (n : ℝ)))]
      congr 1
      congr 1
      rw [hmdef]; ring
    calc correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y}
        ≤ cf ^ (n / (r + 2)) := hbound
      _ ≤ cf ^ ((n : ℝ) / (r + 2 : ℝ) - 1) := hstep1
      _ = (1 / cf) * Real.exp (-m * (n : ℝ)) := hstep2

/-- **Finite susceptibility from any basepoint**: by translation invariance, the
correlation kernel `y ↦ ⟨σ_xσ_y⟩^∞` is summable over `ℤ^d` for every basepoint
`x` (when `0 < contractionFactor < 1`).  The susceptibility
`∑_y ⟨σ_xσ_y⟩^∞` is finite and independent of the basepoint, since
`⟨σ_xσ_y⟩^∞ = ⟨σ_0σ_{y-x}⟩^∞` and summability is invariant under the
reindexing `y ↦ y - x`.  Part of Issue #2931. -/
theorem correlationInfinite_latticeGraph_susceptibility_summable_basepoint
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hcf_pos : 0 < contractionFactor d Λ p r) (hα : contractionFactor d Λ p r < 1)
    (x : Fin d → ℤ) :
    Summable
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {x, y}) := by
  have hbase :=
    correlationInfinite_latticeGraph_susceptibility_summable d hd r hr Λ p hf hh hcf_pos hα
  have heq :
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {x, y})
        = (fun y =>
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y - x}) := by
    funext y
    rw [show ({x, y} : Finset (Fin d → ℤ)) = vaddFinset x {(0 : Fin d → ℤ), y - x} from by
      rw [vaddFinset_pair]; simp [vadd_eq_add]]
    exact (correlationInfinite_vaddFinset_of_translationInvariant
      (IsingModel.latticeGraph d) Λ x p hf {(0 : Fin d → ℤ), y - x})
  rw [heq]
  exact ((Equiv.subRight x).summable_iff
    (f := fun z => correlationInfinite (IsingModel.latticeGraph d) Λ p
      {(0 : Fin d → ℤ), z})).mpr hbase

/-- **Unconditional strong-high-temperature uniform clustering**: in the explicit
regime `βJ · 2 · (d · (2(r+1)+1)^d) < 1`, the infinite-volume correlation is
uniformly small at large distance — for every `ε > 0` there is `R` with
`⟨σ_iσ_j⟩^∞ ≤ ε` for all pairs at distance `≥ R` — with no polynomial-decay
hypothesis (the contraction factor is `< 1` by
`contractionFactor_lt_one_of_high_temp`).  Part of Issue #2931, Phase 3a. -/
theorem correlationInfinite_latticeGraph_uniform_decay_of_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    ∀ ε > (0 : ℝ), ∃ R : ℕ, ∀ i j : Fin d → ℤ,
      R ≤ IsingModel.latticeDistance d i j →
        correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} ≤ ε :=
  correlationInfinite_latticeGraph_uniform_decay_of_contractionFactor_lt_one
    d hd r hr Λ p hf hh (contractionFactor_lt_one_of_high_temp d Λ p hf r hht)

/-- **Unconditional strong-high-temperature clustering (cofinite form)**: in the
explicit regime `βJ · 2 · (d · (2(r+1)+1)^d) < 1`, the correlation kernel
`y ↦ ⟨σ_0σ_y⟩^∞` tends to `0` along the cofinite filter, with no polynomial-decay
hypothesis.  Part of Issue #2931, Phase 3a. -/
theorem correlationInfinite_latticeGraph_tendsto_cofinite_zero_of_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    Filter.Tendsto
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y})
      Filter.cofinite (nhds 0) :=
  correlationInfinite_latticeGraph_tendsto_cofinite_zero
    d hd r hr Λ p hf hh (contractionFactor_lt_one_of_high_temp d Λ p hf r hht)

/-- **Fully explicit unconditional high-temperature distance decay**: in the
regime `H := βJ · 2 · (d · (2(r+1)+1)^d) < 1`, every distinct pair satisfies
`⟨σ_iσ_j⟩^∞ ≤ H^{dist(i,j)/(r+2)}` — a prefactor-free geometric decay with an
explicit base `H` depending only on `βJ`, `d`, `r` (no contraction factor in the statement and
no polynomial-decay hypothesis; the underlying ball-boundary shell-contraction
axiom `shellSup_contraction` (now a proven theorem) is still used).

The contraction factor is bounded by `H` (`contractionFactor_le_high_temp_const`)
and is `< 1` (`contractionFactor_lt_one_of_high_temp`), so the per-pair bound
`correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair` composes
with base monotonicity `cf^q ≤ H^q` (`pow_le_pow_left₀`).  Part of Issue #2931,
Phase 3a. -/
theorem correlationInfinite_latticeGraph_le_explicit_pow_dist
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1)
    {i j : Fin d → ℤ} (hij : i ≠ j) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
      ≤ (p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))))
          ^ (IsingModel.latticeDistance d i j / (r + 2)) := by
  have hcf_lt : contractionFactor d Λ p r < 1 :=
    contractionFactor_lt_one_of_high_temp d Λ p hf r hht
  have hbound :=
    correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair
      d hd r hr Λ p hf hh hcf_lt hij
  have hmono :
      (contractionFactor d Λ p r) ^ (IsingModel.latticeDistance d i j / (r + 2))
        ≤ (p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))))
            ^ (IsingModel.latticeDistance d i j / (r + 2)) :=
    pow_le_pow_left₀ (contractionFactor_nonneg d Λ p hf r)
      (contractionFactor_le_high_temp_const d Λ p hf r) _
  exact hbound.trans hmono

/-- **Summability of the floor-power geometric lattice kernel**: for `0 < c < 1`,
the function `y ↦ c^{⌊dist(0,y)/(r+2)⌋}` is summable over `ℤ^d`.

It is dominated by `(1/c)·exp(-m·dist(0,y))` with `m = -log(c)/(r+2) > 0` (using
`c^{⌊q⌋} ≤ c^{q-1} = (1/c)·exp(-m·dist)`), and the exponential kernel is summable
by `summable_exp_neg_dist`.  This is the reusable core behind both the
contraction-factor and explicit-base susceptibility bounds (Issue #2931). -/
theorem summable_pow_div_latticeDistance (d r : ℕ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    Summable (fun y : Fin d → ℤ => c ^ (IsingModel.latticeDistance d 0 y / (r + 2))) := by
  set m := -Real.log c / (r + 2 : ℝ) with hmdef
  have hr2_pos : (0 : ℝ) < (r + 2 : ℝ) := by positivity
  have hlog_neg : Real.log c < 0 := Real.log_neg hc0 hc1
  have hm_pos : 0 < m := by rw [hmdef]; exact div_pos (by linarith [hlog_neg]) hr2_pos
  have hmaj_sum :
      Summable (fun y : Fin d → ℤ =>
        (1 / c) * Real.exp (-m * (IsingModel.latticeDistance d 0 y : ℝ))) :=
    (summable_exp_neg_dist hm_pos d 0).mul_left (1 / c)
  refine Summable.of_nonneg_of_le (fun y => pow_nonneg hc0.le _) (fun y => ?_) hmaj_sum
  set n := IsingModel.latticeDistance d 0 y with hndef
  have hq_real : ((n / (r + 2) : ℕ) : ℝ) ≥ (n : ℝ) / (r + 2 : ℝ) - 1 := by
    have hlt : n < (n / (r + 2) + 1) * (r + 2) := by
      have hmod := Nat.mod_lt n (show 0 < r + 2 by omega)
      have hdm := Nat.div_add_mod n (r + 2)
      nlinarith [hmod, hdm]
    have hcast : (n : ℝ) < (((n / (r + 2) : ℕ) : ℝ) + 1) * ((r : ℝ) + 2) := by
      have := (Nat.cast_lt (α := ℝ)).2 hlt
      push_cast at this; linarith [this]
    rw [ge_iff_le, sub_le_iff_le_add, div_le_iff₀ hr2_pos]
    nlinarith [hcast]
  have hstep1 : c ^ (n / (r + 2)) ≤ c ^ ((n : ℝ) / (r + 2 : ℝ) - 1) := by
    rw [← Real.rpow_natCast c (n / (r + 2))]
    exact Real.rpow_le_rpow_of_exponent_ge hc0 hc1.le hq_real
  have hstep2 :
      c ^ ((n : ℝ) / (r + 2 : ℝ) - 1) = (1 / c) * Real.exp (-m * (n : ℝ)) := by
    rw [Real.rpow_sub hc0, Real.rpow_one, Real.rpow_def_of_pos hc0,
      one_div, div_eq_mul_inv, mul_comm (c⁻¹) (Real.exp (-m * (n : ℝ)))]
    congr 1
    congr 1
    rw [hmdef]; ring
  calc c ^ (n / (r + 2)) ≤ c ^ ((n : ℝ) / (r + 2 : ℝ) - 1) := hstep1
    _ = (1 / c) * Real.exp (-m * (n : ℝ)) := hstep2

/-- **Unconditional finite susceptibility at strong high temperature**: under
`0 < βJ` and the explicit condition `H := βJ · 2 · (d · (2(r+1)+1)^d) < 1`, the
correlation kernel `y ↦ ⟨σ_0σ_y⟩^∞` is summable (finite susceptibility), with no
polynomial-decay hypothesis and no contraction-factor positivity.

The explicit decay `correlationInfinite_latticeGraph_le_explicit_pow_dist`
dominates the kernel by `H^{dist(0,y)/(r+2)}` with `0 < H < 1`, which is summable
by `summable_pow_div_latticeDistance`.  Part of Issue #2931, Phase 3a. -/
theorem correlationInfinite_latticeGraph_susceptibility_summable_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hβJ_pos : 0 < p.β * p.J)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    Summable
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y}) := by
  set H := p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) with hHdef
  have hH_pos : 0 < H := by
    rw [hHdef]
    have : (0 : ℝ) < 2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ)) := by positivity
    exact mul_pos hβJ_pos this
  have hmaj : Summable (fun y : Fin d → ℤ =>
      H ^ (IsingModel.latticeDistance d 0 y / (r + 2))) :=
    summable_pow_div_latticeDistance d r hH_pos hht
  refine Summable.of_nonneg_of_le
    (fun y => correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _)
    (fun y => ?_) hmaj
  by_cases hy : y = 0
  · subst hy
    have hone : correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), 0} ≤ 1 :=
      correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _
    rw [IsingModel.latticeDistance_self]
    simpa using hone
  · exact correlationInfinite_latticeGraph_le_explicit_pow_dist d hd r hr Λ p hf hh hht
      (Ne.symm hy)

/-- **Unconditional finite susceptibility from any basepoint at high
temperature**: by translation invariance, the correlation kernel
`y ↦ ⟨σ_xσ_y⟩^∞` is summable for every basepoint `x` under `0 < βJ` and
`H := βJ · 2 · (d · (2(r+1)+1)^d) < 1`.  The susceptibility is finite and
basepoint-independent, with no polynomial-decay hypothesis.  Part of Issue #2931,
Phase 3a. -/
theorem correlationInfinite_latticeGraph_susceptibility_summable_high_temp_basepoint
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hβJ_pos : 0 < p.β * p.J)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1)
    (x : Fin d → ℤ) :
    Summable
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {x, y}) := by
  have hbase :=
    correlationInfinite_latticeGraph_susceptibility_summable_high_temp
      d hd r hr Λ p hf hh hβJ_pos hht
  have heq :
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {x, y})
        = (fun y =>
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y - x}) := by
    funext y
    rw [show ({x, y} : Finset (Fin d → ℤ)) = vaddFinset x {(0 : Fin d → ℤ), y - x} from by
      rw [vaddFinset_pair]; simp [vadd_eq_add]]
    exact (correlationInfinite_vaddFinset_of_translationInvariant
      (IsingModel.latticeGraph d) Λ x p hf {(0 : Fin d → ℤ), y - x})
  rw [heq]
  exact ((Equiv.subRight x).summable_iff
    (f := fun z => correlationInfinite (IsingModel.latticeGraph d) Λ p
      {(0 : Fin d → ℤ), z})).mpr hbase

end Ambient
end IsingModel
