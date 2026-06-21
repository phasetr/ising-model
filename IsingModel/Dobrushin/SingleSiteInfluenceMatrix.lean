import IsingModel.Dobrushin.SingleSiteConditionalDistribution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The single-site Dobrushin influence matrix (GJ §17.1 / Dobrushin uniqueness)

The single-site conditional Gibbs distribution at a free site `x`
(`gibbsExpectationBC_singleton_up_eq_upProb`) is `isingSingleSiteUpProb(a)` with local field
`a = isingLocalField = β·(J·∑_{y∼x} sign(η_y) + h)`. The **Dobrushin influence** of a site `y` on
`x` measures how much changing the boundary spin at `y` moves this conditional law. Because the
local field depends on the boundary only through the neighbour spins, and because flipping one
neighbour
shifts the field by exactly `±2βJ`, the influence is bounded by `tanh(βJ)` for `y ∼ x` and is `0`
otherwise. Summing over the row gives Dobrushin's interaction sum `tanh(βJ)·deg(x)`, and the
uniqueness condition `tanh(βJ)·deg(x) < 1` (the high-temperature regime).

* `singleSiteUpProbBC` — the single-site conditional up-probability as a function of the boundary.
* `isingSingleSiteUpProb_dist_le_tanh_half` — `|upProb a − upProb a'| ≤ tanh(|a−a'|/2)`.
* `singleSiteUpProbBC_eq_of_not_neighbour` — no influence from a non-neighbour (or `x` itself).
* `singleSiteUpProbBC_neighbour_dist_le` / `singleSiteUpProbBC_dist_le` — the influence bound
  `≤ tanh(βJ)` (sharp for a neighbour, trivial otherwise).
* `isingInfluence` — the influence matrix `c_{xy} = tanh(βJ)·[y∼x]`.
* `isingInfluence_rowSum` — the Dobrushin interaction sum `∑_y c_{xy} = deg(x)·tanh(βJ)`.
* `isingDobrushin_condition` — the uniqueness condition `tanh(βJ)·deg(x) < 1` as a clean statement.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The single-site Lipschitz–`tanh` bound**: the single-site up-probability moves by at most
`tanh(|a − a'|/2)` when its local field changes from `a` to `a'`. Obtained from the symmetric flip
bound `isingSingleSiteUpProb_flip_neighbour_dist_le` by centering at the midpoint `(a + a')/2`. -/
theorem isingSingleSiteUpProb_dist_le_tanh_half (a a' : ℝ) :
    |isingSingleSiteUpProb a - isingSingleSiteUpProb a'| ≤ Real.tanh (|a - a'| / 2) := by
  have key := isingSingleSiteUpProb_flip_neighbour_dist_le ((a + a') / 2) (|a - a'| / 2)
    (by positivity)
  rcases abs_cases (a - a') with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [show (a + a') / 2 + |a - a'| / 2 = a by rw [h1]; ring,
      show (a + a') / 2 - |a - a'| / 2 = a' by rw [h1]; ring] at key
    exact key
  · rw [show (a + a') / 2 + |a - a'| / 2 = a' by rw [h1]; ring,
      show (a + a') / 2 - |a - a'| / 2 = a by rw [h1]; ring] at key
    rwa [abs_sub_comm]

/-- **Monotonicity of `tanh`**: `a ≤ b → tanh a ≤ tanh b`. Since `tanh = sinh/cosh` with `cosh > 0`,
the difference `tanh a − tanh b = sinh(a − b)/(cosh a·cosh b)` is nonpositive for `a ≤ b`. (Mathlib
has `sinh_strictMono` but no `tanh` monotonicity lemma.) -/
theorem tanh_le_tanh_of_le {a b : ℝ} (hab : a ≤ b) : Real.tanh a ≤ Real.tanh b := by
  have hca := Real.cosh_pos a
  have hcb := Real.cosh_pos b
  have hdiff : Real.tanh b - Real.tanh a
      = Real.sinh (b - a) / (Real.cosh b * Real.cosh a) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
      div_sub_div _ _ hcb.ne' hca.ne', ← Real.sinh_sub b a]
  have hnum : 0 ≤ Real.sinh (b - a) := Real.sinh_nonneg_iff.mpr (by linarith)
  have : 0 ≤ Real.tanh b - Real.tanh a := by
    rw [hdiff]; exact div_nonneg hnum (by positivity)
  linarith

variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

/-- **The single-site conditional up-probability as a boundary functional**: the probability that
the free spin at `x` is `up`, given the boundary condition `η` off `{x}`. Equal to the
boundary-condition Gibbs expectation of the up-indicator
(`gibbsExpectationBC_singleton_up_eq_upProb`). -/
noncomputable def singleSiteUpProbBC (β J h : ℝ) (x : ι) (η : Config ι) : ℝ :=
  isingSingleSiteUpProb (isingLocalField G β J h x η)

/-- `singleSiteUpProbBC` is the boundary-condition Gibbs expectation of the up-indicator. -/
theorem singleSiteUpProbBC_eq_gibbsExpectationBC (β J h : ℝ) (x : ι) (η : Config ι) :
    singleSiteUpProbBC G β J h x η
      = gibbsExpectationBC G β (fun _ => J) h {x} η
          (fun σ => if σ x = Spin.up then (1 : ℝ) else 0) :=
  (gibbsExpectationBC_singleton_up_eq_upProb G β J h x η).symm

omit [Fintype G.edgeSet] [DecidableEq ι] in
/-- **No influence from a non-neighbour (or from `x` itself)**: if `η` and `η'` agree off `{y}` and
`y` is not a neighbour of `x`, the single-site conditional up-probability at `x` is unchanged (the
local field at `x` depends on the boundary only through the neighbour spins). -/
theorem singleSiteUpProbBC_eq_of_not_neighbour (β J h : ℝ) (x : ι) {y : ι} {η η' : Config ι}
    (hy : y ∉ G.neighborFinset x) (hagree : agreesOff {y} η η') :
    singleSiteUpProbBC G β J h x η = singleSiteUpProbBC G β J h x η' := by
  have hsum : (∑ z ∈ G.neighborFinset x, Spin.sign ℝ (η z))
      = ∑ z ∈ G.neighborFinset x, Spin.sign ℝ (η' z) :=
    Finset.sum_congr rfl fun z hz => by
      have hzy : z ≠ y := fun h => hy (h ▸ hz)
      rw [hagree z (by simpa using hzy)]
  rw [singleSiteUpProbBC, singleSiteUpProbBC, isingLocalField, isingLocalField, hsum]

omit [Fintype G.edgeSet] [DecidableEq ι] in
/-- **The neighbour-sign sum difference is supported at the flipped site**: if `η` and `η'` agree
off `{y}` and `y ∼ x`, the difference of the neighbour-sign sums is `sign(η_y) − sign(η'_y)`. -/
private theorem neighbourSignSum_sub (x : ι) {y : ι} {η η' : Config ι}
    (hy : y ∈ G.neighborFinset x) (hagree : agreesOff {y} η η') :
    (∑ z ∈ G.neighborFinset x, Spin.sign ℝ (η z))
        - ∑ z ∈ G.neighborFinset x, Spin.sign ℝ (η' z)
      = Spin.sign ℝ (η y) - Spin.sign ℝ (η' y) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single y]
  · intro z _ hzy
    rw [hagree z (by simpa using hzy), sub_self]
  · intro hy'; exact absurd hy hy'

omit [Fintype ι] [DecidableEq ι] in
/-- **The spin-sign difference is at most `2` in absolute value**: any two `±1` spin signs differ by
at most `2`. -/
private theorem abs_sign_sub_le_two (s t : Spin) :
    |Spin.sign ℝ s - Spin.sign ℝ t| ≤ 2 := by
  cases s <;> cases t <;> simp [Spin.sign, Spin.toSign] <;> norm_num

omit [Fintype G.edgeSet] [DecidableEq ι] in
/-- **The single-site neighbour influence bound** (GJ §17.1): if `η` and `η'` agree off `{y}` with
`y ∼ x`, the single-site conditional up-probability at `x` moves by at most `tanh(βJ)` (for
`0 ≤ βJ`). This is the Dobrushin influence of a neighbour `y` on the site `x`. -/
theorem singleSiteUpProbBC_neighbour_dist_le {β J : ℝ} (hβJ : 0 ≤ β * J) (h : ℝ) (x : ι)
    {y : ι} {η η' : Config ι} (hy : y ∈ G.neighborFinset x) (hagree : agreesOff {y} η η') :
    |singleSiteUpProbBC G β J h x η - singleSiteUpProbBC G β J h x η'| ≤ Real.tanh (β * J) := by
  refine (isingSingleSiteUpProb_dist_le_tanh_half _ _).trans ?_
  have hfield : isingLocalField G β J h x η - isingLocalField G β J h x η'
      = β * J * (Spin.sign ℝ (η y) - Spin.sign ℝ (η' y)) := by
    rw [isingLocalField, isingLocalField,
      show ∀ S S' : ℝ, β * (J * S + h) - β * (J * S' + h) = β * J * (S - S') from
        fun S S' => by ring, neighbourSignSum_sub G x hy hagree]
  have hle : |isingLocalField G β J h x η - isingLocalField G β J h x η'| / 2 ≤ β * J := by
    rw [hfield, abs_mul, abs_of_nonneg hβJ]
    have h2 := abs_sign_sub_le_two (η y) (η' y)
    nlinarith [abs_nonneg (Spin.sign ℝ (η y) - Spin.sign ℝ (η' y))]
  exact tanh_le_tanh_of_le hle

omit [Fintype G.edgeSet] [DecidableEq ι] in
/-- **The single-site influence bound for any site** (GJ §17.1): for `0 ≤ βJ`, changing the boundary
at a single site `y` moves the single-site conditional up-probability at `x` by at most `tanh(βJ)` —
sharply when `y ∼ x`, and not at all when `y` is a non-neighbour. -/
theorem singleSiteUpProbBC_dist_le {β J : ℝ} (hβJ : 0 ≤ β * J) (h : ℝ) (x : ι)
    {y : ι} {η η' : Config ι} (hagree : agreesOff {y} η η') :
    |singleSiteUpProbBC G β J h x η - singleSiteUpProbBC G β J h x η'| ≤ Real.tanh (β * J) := by
  by_cases hy : y ∈ G.neighborFinset x
  · exact singleSiteUpProbBC_neighbour_dist_le G hβJ h x hy hagree
  · rw [singleSiteUpProbBC_eq_of_not_neighbour G β J h x hy hagree, sub_self, abs_zero]
    calc (0 : ℝ) = Real.tanh 0 := Real.tanh_zero.symm
      _ ≤ Real.tanh (β * J) := tanh_le_tanh_of_le hβJ

/-- **The single-site Dobrushin influence matrix** `c_{xy} = tanh(βJ)·[y ∼ x]`: the influence of the
boundary site `y` on the single-site conditional law at `x`, `tanh(βJ)` when `y` is a neighbour of
`x` and `0` otherwise (justified by `singleSiteUpProbBC_dist_le`). -/
noncomputable def isingInfluence (β J : ℝ) (x y : ι) : ℝ :=
  if y ∈ G.neighborFinset x then Real.tanh (β * J) else 0

omit [Fintype G.edgeSet] in
/-- **The Dobrushin interaction sum (row sum)**: `∑_y c_{xy} = deg(x)·tanh(βJ)`. -/
theorem isingInfluence_rowSum (β J : ℝ) (x : ι) :
    ∑ y, isingInfluence G β J x y = G.degree x * Real.tanh (β * J) := by
  simp only [isingInfluence, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [SimpleGraph.card_neighborFinset_eq_degree]

omit [Fintype G.edgeSet] in
/-- **Dobrushin's uniqueness condition** in the single-site Ising influence form: the interaction
sum `tanh(βJ)·deg(x)` is `< 1`. At high temperature this gives uniqueness of the infinite-volume
Gibbs state and volume-uniform exponential decay of correlations. -/
def isingDobrushin_condition (β J : ℝ) (x : ι) : Prop :=
  Real.tanh (β * J) * G.degree x < 1

omit [Fintype G.edgeSet] in
/-- The Dobrushin condition is exactly the interaction sum being `< 1`. -/
theorem isingDobrushin_condition_iff (β J : ℝ) (x : ι) :
    isingDobrushin_condition G β J x ↔ ∑ y, isingInfluence G β J x y < 1 := by
  rw [isingDobrushin_condition, isingInfluence_rowSum, mul_comm]

end Dobrushin

end IsingModel
