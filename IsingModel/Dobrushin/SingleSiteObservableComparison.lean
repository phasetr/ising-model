import IsingModel.Dobrushin.SingleSiteInfluenceMatrix

/-!
# The single-site conditional expectation of a general observable (GJ §17.1, Issue #4201)

For a single free site `Λ = {x}` with the rest frozen to `η`, the boundary-condition Gibbs
expectation of **any** observable `f` is the two-point convex combination
`⟨f⟩^η_{x} = p·f(η[x↦up]) + (1−p)·f(η[x↦down])`, where `p = singleSiteUpProbBC` is the single-site
up-probability. This is the per-site building block of the Dobrushin comparison theorem: for an
observable `f` that depends on the configuration only through `σ_x` (local at `x`), changing the
boundary at one site moves `⟨f⟩^η_{x}` by at most `tanh(βJ)·|f(η[x↦up]) − f(η[x↦down])|` — the
single-site influence bound lifted from the up-indicator to a general local observable.

* `gibbsExpectationBC_singleton_eq` — the two-point convex-combination formula.
* `isingSingleSiteUpProb_nonneg` / `isingSingleSiteUpProb_le_one` — `p ∈ [0,1]`.
* `LocalAtSite` — the predicate "`f` depends only on `σ_x`".
* `gibbsExpectationBC_singleton_localObs_dist_le` — the single-site comparison bound.

The full multi-site Dobrushin comparison theorem (telescoping over sites) is not formalized here.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The single-site up-probability is nonnegative**. -/
theorem isingSingleSiteUpProb_nonneg (a : ℝ) : 0 ≤ isingSingleSiteUpProb a := by
  rw [isingSingleSiteUpProb]; positivity

/-- **The single-site up-probability is at most `1`** (`e^a ≤ e^a + e^{-a}`). -/
theorem isingSingleSiteUpProb_le_one (a : ℝ) : isingSingleSiteUpProb a ≤ 1 := by
  rw [isingSingleSiteUpProb, div_le_one (by positivity)]
  have : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  linarith

variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

/-- **The single-site conditional expectation of a general observable** (GJ §17.1): for the free
site `{x}` with the rest of the lattice frozen to `η`, the boundary-condition Gibbs expectation of
any observable `f` is the two-point convex combination
`⟨f⟩^η_{x} = p·f(η[x↦up]) + (1−p)·f(η[x↦down])` with `p = singleSiteUpProbBC`. -/
theorem gibbsExpectationBC_singleton_eq (β J h : ℝ) (x : ι) (η : Config ι) (f : Config ι → ℝ) :
    gibbsExpectationBC G β (fun _ => J) h {x} η f
      = singleSiteUpProbBC G β J h x η * f (Function.update η x Spin.up)
        + (1 - singleSiteUpProbBC G β J h x η) * f (Function.update η x Spin.down) := by
  classical
  have hpu : singleSiteUpProbBC G β J h x η
      = gibbsExpectationBC G β (fun _ => J) h {x} η
          (fun σ => if σ x = Spin.up then (1 : ℝ) else 0) :=
    singleSiteUpProbBC_eq_gibbsExpectationBC G β J h x η
  have hpd : 1 - singleSiteUpProbBC G β J h x η
      = gibbsExpectationBC G β (fun _ => J) h {x} η
          (fun σ => if σ x = Spin.down then (1 : ℝ) else 0) :=
    (gibbsExpectationBC_singleton_down_eq G β J h x η).symm
  rw [hpd, hpu, gibbsExpectationBC, gibbsExpectationBC, gibbsExpectationBC,
    sum_F_boltzmannBC_singleton, sum_F_boltzmannBC_singleton, sum_F_boltzmannBC_singleton]
  simp only [Function.update_self, reduceCtorEq, reduceIte]
  ring

/-- **`f` is local at the site `x`**: its value depends on the configuration only through `σ_x`. -/
def LocalAtSite (x : ι) (f : Config ι → ℝ) : Prop :=
  ∀ σ σ' : Config ι, σ x = σ' x → f σ = f σ'

omit [DecidableRel G.Adj] in
/-- **The single-site comparison bound for a local observable** (GJ §17.1): if `f` is local at `x`
and the boundary conditions `η`, `η'` agree off `{y}`, then for `0 ≤ βJ` the single-site conditional
expectations differ by at most `tanh(βJ)·|f(η[x↦up]) − f(η[x↦down])|`. This lifts the single-site
influence bound (`singleSiteUpProbBC_dist_le`) from the up-indicator to a general local observable —
the per-site step of the Dobrushin comparison theorem. -/
theorem gibbsExpectationBC_singleton_localObs_dist_le {β J : ℝ} (hβJ : 0 ≤ β * J) (h : ℝ) (x : ι)
    {y : ι} {η η' : Config ι} (f : Config ι → ℝ) (hf : LocalAtSite x f)
    (hagree : agreesOff {y} η η') :
    |gibbsExpectationBC G β (fun _ => J) h {x} η f
        - gibbsExpectationBC G β (fun _ => J) h {x} η' f|
      ≤ Real.tanh (β * J)
        * |f (Function.update η x Spin.up) - f (Function.update η x Spin.down)| := by
  classical
  rw [gibbsExpectationBC_singleton_eq, gibbsExpectationBC_singleton_eq]
  have hup : f (Function.update η' x Spin.up) = f (Function.update η x Spin.up) :=
    hf _ _ (by rw [Function.update_self, Function.update_self])
  have hdn : f (Function.update η' x Spin.down) = f (Function.update η x Spin.down) :=
    hf _ _ (by rw [Function.update_self, Function.update_self])
  rw [hup, hdn,
    show singleSiteUpProbBC G β J h x η * f (Function.update η x Spin.up)
          + (1 - singleSiteUpProbBC G β J h x η) * f (Function.update η x Spin.down)
        - (singleSiteUpProbBC G β J h x η' * f (Function.update η x Spin.up)
          + (1 - singleSiteUpProbBC G β J h x η') * f (Function.update η x Spin.down))
        = (singleSiteUpProbBC G β J h x η - singleSiteUpProbBC G β J h x η')
          * (f (Function.update η x Spin.up) - f (Function.update η x Spin.down)) by ring,
    abs_mul]
  exact mul_le_mul_of_nonneg_right (singleSiteUpProbBC_dist_le G hβJ h x hagree) (abs_nonneg _)

end Dobrushin

end IsingModel
