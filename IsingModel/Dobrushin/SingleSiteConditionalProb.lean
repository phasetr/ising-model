import IsingModel.Dobrushin.SingleSiteConditional
import IsingModel.Inequalities.FKGBoundaryCondition

/-!
# The single-site conditional sum collapse (GJ §17.1 / Dobrushin uniqueness)

The boundary-condition Gibbs expectation over the single free site `Λ = {x}` collapses to a two-term
sum: the only configurations agreeing with `η` off `{x}` are `η` updated at `x` to `up` or `down`.
This is the bookkeeping step toward the single-site conditional probability `(1 + tanh(β·local
field))/2` (combined with the single-site Hamiltonian gap `hamiltonian_update_up_sub_down`).

* `sum_indicator_agreesOff_singleton` — the two-term collapse of a sum over `{x}`-agreeing configs.
* `hamiltonianJ_const_eq_hamiltonian` — the inhomogeneous Hamiltonian with constant coupling `J` is
  the homogeneous Ising Hamiltonian (bridging the boundary-condition weight to the single-site gap).

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1.
-/

namespace IsingModel

namespace Dobrushin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The constant-coupling inhomogeneous Hamiltonian is the homogeneous Ising Hamiltonian**:
`hamiltonianJ G (fun _ => J) h = hamiltonian G ⟨J, h, β⟩`. This bridges the boundary-condition
Boltzmann weight (stated with `hamiltonianJ`) to the single-site Hamiltonian gap
(`hamiltonian_update_up_sub_down`). -/
theorem hamiltonianJ_const_eq_hamiltonian (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (σ : Config ι) :
    hamiltonianJ G (fun _ => J) h σ = hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) σ := by
  rw [hamiltonianJ, hamiltonian]
  congr 1
  rw [interactionEnergyJ, interactionEnergy, neg_mul, Finset.mul_sum]

/-- **Two-term collapse of a `{x}`-conditioned sum**: a sum over all configurations weighted by the
indicator of agreement with `η` off `{x}` reduces to the two single-site updates of `η` at `x`
(a config agreeing with `η` off `{x}` is determined by its value at `x`). -/
theorem sum_indicator_agreesOff_singleton (x : ι) (η : Config ι) (g : Config ι → ℝ) :
    ∑ σ : Config ι, Set.indicator {σ | agreesOff {x} η σ} g σ
      = g (Function.update η x Spin.up) + g (Function.update η x Spin.down) := by
  classical
  have hfilter : ∑ σ : Config ι, Set.indicator {σ | agreesOff {x} η σ} g σ
      = ∑ σ ∈ Finset.univ.filter (fun σ => agreesOff {x} η σ), g σ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Set.indicator_apply]
    rfl
  rw [hfilter, ← sum_spin (fun s => g (Function.update η x s))]
  refine Finset.sum_bij' (fun σ _ => σ x) (fun s _ => Function.update η x s) ?_ ?_ ?_ ?_ ?_
  · intro σ _; exact Finset.mem_univ _
  · intro s _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi =>
      Function.update_of_ne (fun heq => hi (Finset.mem_singleton.mpr heq)) s η⟩
  · -- left inverse: `update η x (σ x) = σ` for `σ` agreeing with `η` off `{x}`
    intro σ hσ
    have hag := (Finset.mem_filter.mp hσ).2
    funext i
    by_cases h : i = x
    · subst h; simp
    · simp only [Function.update_apply, if_neg h]; exact (hag i (by simpa using h)).symm
  · -- right inverse: `(update η x s) x = s`
    intro s _; simp
  · -- value: `g σ = g (update η x (σ x))`
    intro σ hσ
    have hag := (Finset.mem_filter.mp hσ).2
    refine congrArg g (funext fun i => ?_)
    by_cases h : i = x
    · subst h; simp
    · simp only [Function.update_apply, if_neg h]; exact hag i (by simpa using h)

end Dobrushin

end IsingModel
