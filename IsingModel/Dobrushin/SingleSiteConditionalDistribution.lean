import IsingModel.Dobrushin.SingleSiteConditionalProb
import IsingModel.Dobrushin.SingleSiteConditional

/-!
# The single-site conditional Gibbs distribution (GJ §17.1 / Dobrushin uniqueness)

With the `{x}`-conditioned sum collapse (`sum_indicator_agreesOff_singleton`) and the single-site
Hamiltonian gap (`hamiltonian_update_up_sub_down`) in hand, this file computes the **single-site
conditional Gibbs distribution** at a free site `x` with the rest of the lattice frozen to the
boundary condition `η`:

* the conditional probability that `σ x = up` is `isingSingleSiteUpProb(a)` with local field
  `a = β·(J·∑_{y∼x} sign(η_y) + h)`;
* the conditional probability that `σ x = down` is `1 − isingSingleSiteUpProb(a)`;
* the conditional magnetization `⟨sign(σ_x)⟩` is `tanh(a)`.

These are the per-site building blocks of the single-site Dobrushin influence matrix
`c_{xy} = tanh(βJ)·[y∼x]`, whose row sum `tanh(βJ)·deg < 1` at high temperature gives Dobrushin
uniqueness with volume-uniform exponential decay.

* `isingSingleSiteUpProb_eq_exp_ratio` — `isingSingleSiteUpProb((p−q)/2) = e^p/(e^p + e^q)`.
* `tanh_eq_exp_ratio` — `tanh((p−q)/2) = (e^p − e^q)/(e^p + e^q)`.
* `isingLocalField` — the single-site local field `β·(J·neighbour-sign-sum + h)`.
* `gibbsExpectationBC_singleton_up_eq_upProb` — the up-probability headline.
* `gibbsExpectationBC_singleton_down_eq` — the down-probability `1 − upProb`.
* `gibbsExpectationBC_singleton_sign_eq_tanh` — the conditional magnetization `tanh(a)`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1.
-/

namespace IsingModel

namespace Dobrushin

open Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The single-site up-probability as a Boltzmann ratio**: `isingSingleSiteUpProb((p − q)/2) =
e^p/(e^p + e^q)`. Applied with `p = −β·H(η[x↦up])`, `q = −β·H(η[x↦down])`, this turns the ratio of
single-site Boltzmann weights into the logistic up-probability of the local field. -/
theorem isingSingleSiteUpProb_eq_exp_ratio (p q : ℝ) :
    isingSingleSiteUpProb ((p - q) / 2) = Real.exp p / (Real.exp p + Real.exp q) := by
  rw [isingSingleSiteUpProb, div_eq_div_iff (by positivity) (by positivity), mul_add, mul_add,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1 <;> congr 1 <;> ring

/-- **The hyperbolic tangent as a Boltzmann ratio**: `tanh((p − q)/2) = (e^p − e^q)/(e^p + e^q)`.
Applied with `p = −β·H(η[x↦up])`, `q = −β·H(η[x↦down])`, this gives the conditional magnetization
`⟨sign(σ_x)⟩ = (w_up − w_down)/(w_up + w_down)` as `tanh` of the local field. -/
theorem tanh_eq_exp_ratio (p q : ℝ) :
    Real.tanh ((p - q) / 2) = (Real.exp p - Real.exp q) / (Real.exp p + Real.exp q) := by
  have h := isingSingleSiteUpProb_eq_exp_ratio p q
  rw [isingSingleSiteUpProb_eq_tanh] at h
  have hne : Real.exp p + Real.exp q ≠ 0 := by positivity
  have ht : Real.tanh ((p - q) / 2)
      = 2 * (Real.exp p / (Real.exp p + Real.exp q)) - 1 := by linarith [h]
  rw [ht]
  field_simp
  ring

/-- **The single-site local field** `a = β·(J·∑_{y∼x} sign(η_y) + h)`: the field seen by the spin at
site `x` when the rest of the lattice is frozen to `η`, with constant coupling `J` and field `h`.
Its single-site conditional up-probability is `isingSingleSiteUpProb(a)`. -/
noncomputable def isingLocalField (G : SimpleGraph ι) [DecidableRel G.Adj]
    (β J h : ℝ) (x : ι) (η : Config ι) : ℝ :=
  β * (J * (∑ y ∈ G.neighborFinset x, Spin.sign ℝ (η y)) + h)

variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- **Collapse of a single-site `{x}`-conditioned weighted sum**: for any observable `F`, the
boundary-condition weighted sum over `{x}`-agreeing configurations reduces to the two single-site
updates. A reusable bridge for the up/down/magnetization conditional formulas. -/
private theorem sum_F_boltzmannBC_singleton (β J h : ℝ) (x : ι) (η : Config ι)
    (F : Config ι → ℝ) :
    ∑ σ : Config ι, F σ * boltzmannWeightBC G β (fun _ => J) h {x} η σ
      = F (Function.update η x Spin.up)
          * boltzmannWeightJ G β (fun _ => J) h (Function.update η x Spin.up)
        + F (Function.update η x Spin.down)
          * boltzmannWeightJ G β (fun _ => J) h (Function.update η x Spin.down) := by
  classical
  have hpt : ∀ σ : Config ι, F σ * boltzmannWeightBC G β (fun _ => J) h {x} η σ
      = Set.indicator {σ | agreesOff {x} η σ}
          (fun σ => F σ * boltzmannWeightJ G β (fun _ => J) h σ) σ := by
    intro σ
    unfold boltzmannWeightBC
    by_cases hσ : agreesOff {x} η σ
    · rw [Set.indicator_of_mem hσ, Set.indicator_of_mem hσ]
    · rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem hσ, mul_zero]
  rw [Finset.sum_congr rfl (fun σ _ => hpt σ),
    sum_indicator_agreesOff_singleton x η (fun σ => F σ * boltzmannWeightJ G β (fun _ => J) h σ)]

omit [DecidableRel G.Adj] in
/-- **The constant-coupling single-site Boltzmann weight as `e^{−β·H}`**: rewriting the
inhomogeneous weight at a single-site update through the constant-coupling Hamiltonian bridge. -/
private theorem weight_update_eq_exp (β J h : ℝ) (x : ι) (η : Config ι) (s : Spin) :
    boltzmannWeightJ G β (fun _ => J) h (Function.update η x s)
      = Real.exp (-β * hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) (Function.update η x s)) := by
  rw [boltzmannWeightJ, hamiltonianJ_const_eq_hamiltonian]

/-- **The local field is half the (negated) single-site energy gap**: with `p = −β·H(η[x↦up])`,
`q = −β·H(η[x↦down])`, the local field `a = β·(J·∑_{y∼x} sign(η_y) + h)` equals `(p − q)/2`. This is
the bridge feeding the energy gap into the Boltzmann-ratio helpers. -/
private theorem isingLocalField_eq_gap (β J h : ℝ) (x : ι) (η : Config ι) :
    isingLocalField G β J h x η
      = (-β * hamiltonian G ⟨J, h, β⟩ (Function.update η x Spin.up)
          - -β * hamiltonian G ⟨J, h, β⟩ (Function.update η x Spin.down)) / 2 := by
  have hgap := hamiltonian_update_up_sub_down G (⟨J, h, β⟩ : IsingParams ℝ) x η
  rw [isingLocalField]
  linear_combination (β / 2) * hgap

/-- **The single-site conditional up-probability** (GJ §17.1): conditioning on the boundary `η` off
`{x}`, the probability that the free spin at `x` is `up` is `isingSingleSiteUpProb(a)` with local
field `a = β·(J·∑_{y∼x} sign(η_y) + h)`. This is the lattice realization of the logistic single-site
conditional distribution underlying the Dobrushin influence `tanh(βJ)`. -/
theorem gibbsExpectationBC_singleton_up_eq_upProb (β J h : ℝ) (x : ι) (η : Config ι) :
    gibbsExpectationBC G β (fun _ => J) h {x} η (fun σ => if σ x = Spin.up then (1 : ℝ) else 0)
      = isingSingleSiteUpProb (isingLocalField G β J h x η) := by
  classical
  set wu := boltzmannWeightJ G β (fun _ => J) h (Function.update η x Spin.up) with hwu
  set wd := boltzmannWeightJ G β (fun _ => J) h (Function.update η x Spin.down) with hwd
  have hnum : ∑ σ : Config ι, (if σ x = Spin.up then (1 : ℝ) else 0)
        * boltzmannWeightBC G β (fun _ => J) h {x} η σ = wu := by
    rw [sum_F_boltzmannBC_singleton G β J h x η (fun σ => if σ x = Spin.up then (1 : ℝ) else 0)]
    simp [Function.update_self, hwu]
  have hZ : partitionFunctionBC G β (fun _ => J) h {x} η = wu + wd := by
    rw [partitionFunctionBC]
    have := sum_F_boltzmannBC_singleton G β J h x η (fun _ => (1 : ℝ))
    simpa [hwu, hwd] using this
  rw [gibbsExpectationBC, hnum, hZ]
  rw [weight_update_eq_exp G β J h x η Spin.up] at hwu
  rw [weight_update_eq_exp G β J h x η Spin.down] at hwd
  rw [isingLocalField_eq_gap G β J h x η]
  rw [isingSingleSiteUpProb_eq_exp_ratio, hwu, hwd]
  ring

/-- **The single-site conditional down-probability** (GJ §17.1): the probability that the free spin
at `x` is `down` is `1 − isingSingleSiteUpProb(a)` (the two events are complementary). -/
theorem gibbsExpectationBC_singleton_down_eq (β J h : ℝ) (x : ι) (η : Config ι) :
    gibbsExpectationBC G β (fun _ => J) h {x} η (fun σ => if σ x = Spin.down then (1 : ℝ) else 0)
      = 1 - isingSingleSiteUpProb (isingLocalField G β J h x η) := by
  classical
  have hfun : (fun σ : Config ι => if σ x = Spin.down then (1 : ℝ) else 0)
      = (fun _ : Config ι => (1 : ℝ))
          + fun σ : Config ι => (-1) * (if σ x = Spin.up then (1 : ℝ) else 0) := by
    funext σ
    cases hσ : σ x <;> simp [hσ, Pi.add_apply]
  rw [hfun, gibbsExpectationBC_add, gibbsExpectationBC_const, gibbsExpectationBC_const_mul,
    gibbsExpectationBC_singleton_up_eq_upProb]
  ring

/-- **The single-site conditional magnetization** (GJ §17.1): conditioning on the boundary `η` off
`{x}`, the expected spin sign at the free site `x` is `tanh(a)` with local field
`a = β·(J·∑_{y∼x} sign(η_y) + h)`. This is the per-site magnetization response `m = tanh(a)` and the
source of the Ising Dobrushin influence `tanh(βJ)`. -/
theorem gibbsExpectationBC_singleton_sign_eq_tanh (β J h : ℝ) (x : ι) (η : Config ι) :
    gibbsExpectationBC G β (fun _ => J) h {x} η (fun σ => Spin.sign ℝ (σ x))
      = Real.tanh (isingLocalField G β J h x η) := by
  classical
  set wu := boltzmannWeightJ G β (fun _ => J) h (Function.update η x Spin.up) with hwu
  set wd := boltzmannWeightJ G β (fun _ => J) h (Function.update η x Spin.down) with hwd
  have hnum : ∑ σ : Config ι, Spin.sign ℝ (σ x)
        * boltzmannWeightBC G β (fun _ => J) h {x} η σ = wu - wd := by
    rw [sum_F_boltzmannBC_singleton G β J h x η (fun σ => Spin.sign ℝ (σ x))]
    rw [Function.update_self, Function.update_self, sign_up, sign_down]
    ring
  have hZ : partitionFunctionBC G β (fun _ => J) h {x} η = wu + wd := by
    rw [partitionFunctionBC]
    have := sum_F_boltzmannBC_singleton G β J h x η (fun _ => (1 : ℝ))
    simpa [hwu, hwd] using this
  rw [gibbsExpectationBC, hnum, hZ]
  rw [weight_update_eq_exp G β J h x η Spin.up] at hwu
  rw [weight_update_eq_exp G β J h x η Spin.down] at hwd
  rw [isingLocalField_eq_gap G β J h x η]
  rw [tanh_eq_exp_ratio, hwu, hwd]
  ring

end Dobrushin

end IsingModel
