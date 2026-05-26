import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.BallDefs
import IsingModel.LatticeExpSum

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

/-- **Cardinality bound for the contraction factor**: each boundary-edge summand
`⟨σ_0σ_k⟩^∞ + ⟨σ_0σ_l⟩^∞` is at most `2` (correlations are `≤ 1`), so
`contractionFactor d Λ p r ≤ βJ · 2 · |latticeBallBoundaryEdges d r|`.

Together with `latticeBallBoundaryEdges_card_le` this bounds the contraction
factor by `βJ` times (twice) the cube edge count, the estimate used to make the
contraction factor `< 1` in a strong high-temperature regime (Issue #2931,
Phase 3a). -/
theorem contractionFactor_le_card (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : ℕ) :
    contractionFactor d Λ p r
      ≤ p.β * p.J * (2 * ((latticeBallBoundaryEdges d r).card : ℝ)) := by
  unfold contractionFactor
  have hβJ : 0 ≤ p.β * p.J := mul_nonneg hf.hβ.le hf.hJ
  refine mul_le_mul_of_nonneg_left ?_ hβJ
  calc ∑ e ∈ latticeBallBoundaryEdges d r,
        Sym2.lift ⟨fun k l =>
          correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
            + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l},
        fun k l => by ring⟩ e
      ≤ ∑ _e ∈ latticeBallBoundaryEdges d r, (2 : ℝ) := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
        simp only [Sym2.lift_mk]
        have hk := correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p
          {(0 : Fin d → ℤ), k}
        have hl := correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p
          {(0 : Fin d → ℤ), l}
        linarith
    _ = 2 * ((latticeBallBoundaryEdges d r).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Explicit high-temperature bound for the contraction factor**: chaining the
boundary-edge cardinality bound `latticeBallBoundaryEdges_card_le`, the induced
cube edge count `inducedLatticeGraph_card_edgeFinset_le`, and the cube cardinality
`card_cubicBox`, the contraction factor is bounded by
`βJ · 2 · (d · (2(r+1)+1)^d)`.

This makes the contraction factor explicitly controlled by `βJ` times a fixed
(volume-independent) combinatorial constant depending only on `d` and `r`, the
input for an unconditional strong-high-temperature `contractionFactor < 1`
(Issue #2931, Phase 3a). -/
theorem contractionFactor_le_high_temp_const (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : ℕ) :
    contractionFactor d Λ p r
      ≤ p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) := by
  have hβJ : 0 ≤ p.β * p.J := mul_nonneg hf.hβ.le hf.hJ
  have hcard : ((latticeBallBoundaryEdges d r).card : ℝ)
      ≤ ((inducedGraph (IsingModel.latticeGraph d)
          (cubicBox d (r + 1))).edgeFinset.card : ℝ) := by
    exact_mod_cast latticeBallBoundaryEdges_card_le d r
  have hedge := inducedLatticeGraph_card_edgeFinset_le d (cubicBox d (r + 1))
  have hbox : Fintype.card (↑(cubicBox d (r + 1)) : Type _)
      = (2 * (r + 1) + 1) ^ d := by
    rw [Fintype.card_coe]; exact card_cubicBox d (r + 1)
  rw [hbox] at hedge
  calc contractionFactor d Λ p r
      ≤ p.β * p.J * (2 * ((latticeBallBoundaryEdges d r).card : ℝ)) :=
        contractionFactor_le_card d Λ p hf r
    _ ≤ p.β * p.J *
          (2 * ((inducedGraph (IsingModel.latticeGraph d)
            (cubicBox d (r + 1))).edgeFinset.card : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hβJ
        exact mul_le_mul_of_nonneg_left hcard (by norm_num)
    _ ≤ p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hβJ
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact_mod_cast hedge

/-- **Unconditional strong-high-temperature contraction**: if `βJ` is small
enough that `βJ · 2 · (d · (2(r+1)+1)^d) < 1`, then `contractionFactor d Λ p r < 1`
outright — no polynomial-decay hypothesis needed.

This discharges the `contractionFactor < 1` hypothesis of the spatial-decay /
susceptibility layer in an explicit (volume-independent) strong-high-temperature
regime, via `contractionFactor_le_high_temp_const`.  Part of Issue #2931,
Phase 3a. -/
theorem contractionFactor_lt_one_of_high_temp (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : ℕ)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    contractionFactor d Λ p r < 1 :=
  lt_of_le_of_lt (contractionFactor_le_high_temp_const d Λ p hf r) hht

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
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ)
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
      d hd r Λ p hf hh hα (ε / 2) (by linarith)
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
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ)
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
      correlationInfinite_latticeGraph_le_contractionFactor_pow_dist d hd r Λ p hf hh hα hy
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
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hcf_pos : 0 < contractionFactor d Λ p r) (hα : contractionFactor d Λ p r < 1)
    (x : Fin d → ℤ) :
    Summable
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {x, y}) := by
  have hbase :=
    correlationInfinite_latticeGraph_susceptibility_summable d hd r Λ p hf hh hcf_pos hα
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
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    ∀ ε > (0 : ℝ), ∃ R : ℕ, ∀ i j : Fin d → ℤ,
      R ≤ IsingModel.latticeDistance d i j →
        correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} ≤ ε :=
  correlationInfinite_latticeGraph_uniform_decay_of_contractionFactor_lt_one
    d hd r Λ p hf hh (contractionFactor_lt_one_of_high_temp d Λ p hf r hht)

/-- **Unconditional strong-high-temperature clustering (cofinite form)**: in the
explicit regime `βJ · 2 · (d · (2(r+1)+1)^d) < 1`, the correlation kernel
`y ↦ ⟨σ_0σ_y⟩^∞` tends to `0` along the cofinite filter, with no polynomial-decay
hypothesis.  Part of Issue #2931, Phase 3a. -/
theorem correlationInfinite_latticeGraph_tendsto_cofinite_zero_of_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    Filter.Tendsto
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y})
      Filter.cofinite (nhds 0) :=
  correlationInfinite_latticeGraph_tendsto_cofinite_zero
    d hd r Λ p hf hh (contractionFactor_lt_one_of_high_temp d Λ p hf r hht)

/-- **Fully explicit unconditional high-temperature distance decay**: in the
regime `H := βJ · 2 · (d · (2(r+1)+1)^d) < 1`, every distinct pair satisfies
`⟨σ_iσ_j⟩^∞ ≤ H^{dist(i,j)/(r+2)}` — a prefactor-free geometric decay with an
explicit base `H` depending only on `βJ`, `d`, `r` (no contraction factor and no
polynomial-decay hypothesis).

The contraction factor is bounded by `H` (`contractionFactor_le_high_temp_const`)
and is `< 1` (`contractionFactor_lt_one_of_high_temp`), so the per-pair bound
`correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair` composes
with base monotonicity `cf^q ≤ H^q` (`pow_le_pow_left`).  Part of Issue #2931,
Phase 3a. -/
theorem correlationInfinite_latticeGraph_le_explicit_pow_dist
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ)
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
      d hd r Λ p hf hh hcf_lt hij
  have hmono :
      (contractionFactor d Λ p r) ^ (IsingModel.latticeDistance d i j / (r + 2))
        ≤ (p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))))
            ^ (IsingModel.latticeDistance d i j / (r + 2)) :=
    pow_le_pow_left₀ (contractionFactor_nonneg d Λ p hf r)
      (contractionFactor_le_high_temp_const d Λ p hf r) _
  exact hbound.trans hmono

end Ambient
end IsingModel
