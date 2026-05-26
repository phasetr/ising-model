import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.BallDefs

/-!
# Theorem eta-le-1 split — Phases 5-7 contraction factor and iterated contraction bound

Part of the split eta<=1 polynomial-to-exponential decay layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Phase 5: Contraction factor -/

/-- **Contraction factor for radius `r`**: the weighted sum over boundary edges of the
sum of two-point correlations from the origin to each endpoint.

`contractionFactor d Λ p r := p.β * p.J * ∑ e ∈ latticeBallBoundaryEdges d r,`
`  Sym2.lift ⟨fun k l => corr∞{0, k} + corr∞{0, l}, ...⟩ e`

Under translation invariance (at `h = 0`), `corr∞{l, x} = corr∞{0, x - l}`, so the
ball-boundary inequality with `sup_{|x| ≥ n} corr∞{0, x}` bounded by
`contractionFactor * sup_{|y| ≥ n - r - 1} corr∞{0, y}` (see `shellSup_contraction`).

Key property: under `HasPolynomialDecay`, `contractionFactor d Λ p r → 0` as `r → ∞`,
so in particular `contractionFactor < 1` for large enough `r`. -/
noncomputable def contractionFactor (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (r : ℕ) : ℝ :=
  p.β * p.J * ∑ e ∈ latticeBallBoundaryEdges d r,
    Sym2.lift ⟨fun k l =>
      correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
        + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l},
    fun k l => by ring⟩ e

/-- **The contraction factor is non-negative**: `0 ≤ contractionFactor d Λ p r`.

Follows from `p.β * p.J ≥ 0` (ferromagnetic) and
`correlationInfinite ≥ 0` (ferromagnetic). -/
theorem contractionFactor_nonneg (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : ℕ) :
    0 ≤ contractionFactor d Λ p r := by
  unfold contractionFactor
  apply mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_nonneg
  intro e _
  obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  apply add_nonneg
  · exact correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
  · exact correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _

/-- **Polynomial decay implies contraction factor tends to zero** (axiom, sub-step of GJ §17.8):

Under `HasPolynomialDecay d Λ p`, `contractionFactor d Λ p r → 0` as `r → ∞`
along `Filter.atTop`.

**Proof sketch (deferred)**: The boundary `latticeBallBoundaryEdges d r` has
`O(r^{d-1})` edges. Each endpoint `k` (or `l`) at distance `∼ r` from the origin
satisfies `corr∞{0, k} ≤ c * r^{-(d-1)}` by the polynomial decay hypothesis.
The product `O(r^{d-1}) * O(r^{-(d-1)}) * β * J → 0` since the polynomial
decay gives the `o(1)` term: for any `ε > 0`, eventually all summands
`corr∞{0, k} * dist(0, k)^{d-1} ≤ ε`, so
`contractionFactor r ≤ β * J * |∂B_r| * ε * r^{-(d-1)} ≤ C * ε → 0`.

Reference: Glimm–Jaffe §17.8 pp. 317–318. -/
axiom polynomialDecay_contraction_factor_tendsto (d : ℕ) (hd : 1 ≤ d)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hpoly : HasPolynomialDecay d Λ p) :
    Filter.Tendsto (contractionFactor d Λ p) Filter.atTop (nhds 0)

/-! ## Phase 6: Shell-supremum contraction (axiom) -/

/-- **Shell supremum contraction** (axiom, key inductive step of GJ §17.8):

For `n > r + 1`, the supremum of `corr∞{0, y}` over the shell `{y : |y| ≥ n}` satisfies:

  `⨆ {|y| ≥ n} corr∞{0, y} ≤ contractionFactor d Λ p r * ⨆ {|y| ≥ n - r - 1} corr∞{0, y}`

**Proof sketch (deferred)**: For each `y` with `|y| ≥ n > r`, apply
`ball_boundary_tight_infinite` to get:
  `corr∞{0, y} ≤ β * J * Σ_{(k,l)∈Γ_r} [corr∞{0,k} * corr∞{l,y} + corr∞{0,l} * corr∞{k,y}]`
By translation invariance (`correlationInfinite_vaddFinset_of_translationInvariant`
with translation `t = -l`), `corr∞{l, y} = corr∞{0, y - l}`. Boundary edges satisfy
`|k|, |l| ≤ r + 1`, so `|y - l| ≥ |y| - r - 1 ≥ n - r - 1`. Thus
  `corr∞{0, y} ≤ contractionFactor * (⨆ {|z| ≥ n-r-1} corr∞{0, z})`
Taking the `iSup` over `y` gives the claimed inequality.

Reference: Glimm–Jaffe §17.8 proof of Thm 17.8.1, p. 317. -/
axiom shellSup_contraction (d : ℕ) (hd : 1 ≤ d)
    (r : ℕ)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (n : ℕ) (hn : r + 1 < n) :
    ⨆ (y : {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
        correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val}
      ≤ contractionFactor d Λ p r *
        ⨆ (y : {y : Fin d → ℤ // (n - r - 1) ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val}

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
theorem shellSup_iterated_bound (d : ℕ) (hd : 1 ≤ d) (r : ℕ)
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
              shellSup_contraction d hd r Λ p hf hh n hn_gt
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
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d Λ p r < 1) {y : Fin d → ℤ} (hy : y ≠ 0) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y}
      ≤ (contractionFactor d Λ p r) ^ (IsingModel.latticeDistance d 0 y / (r + 2)) := by
  set k := IsingModel.latticeDistance d 0 y / (r + 2) with hk
  have hkr : k * (r + 2) ≤ IsingModel.latticeDistance d 0 y := Nat.div_mul_le_self _ _
  have hbound :=
    shellSup_iterated_bound d hd r Λ p hf hh hα k (IsingModel.latticeDistance d 0 y) hkr
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
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ)
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
    d hd r Λ p hf hh hα hjmi_ne

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
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ)
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
        d hd r Λ p hf hh hα hij
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

end Ambient
end IsingModel
