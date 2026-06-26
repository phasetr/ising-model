import IsingModel.Dobrushin.SiteOscillation
import IsingModel.RealTanhAux

/-!
# The multi-site boundary influence bound (GJ §17.1, Issue #4201)

Toward the Dobrushin comparison theorem: the single-site conditional law at `x` is insensitive to
boundary configurations agreeing on the neighbours of `x`, and more quantitatively, two boundary
configurations `η, η'` agreeing off a set `S` change the conditional up-probability by at most
`#(S ∩ neighbours of x)·tanh(βJ)` — the total influence of the differing boundary neighbours. This
is the "boundary direct term" `b_x` of the comparison telescoping. For an observable local at
`x`, the conditional expectation changes by at most `b_x·siteOsc x f`.

* `singleSiteUpProbBC_eq_of_agreesOn_neighbour` — locality: agreement on the neighbours of `x` ⇒
  equal single-site conditional up-probability.
* `singleSiteUpProbBC_agreesOff_dist_le` — `|p(η) − p(η')| ≤ #(S ∩ nbr(x))·tanh(βJ)` (telescoping
  the single-flip influence bound over the differing neighbours).
* `gibbsExpectationBC_singleton_localObs_agreesOff_dist_le` — the local-observable version.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

omit [Fintype G.edgeSet] [DecidableEq ι] in
/-- **Locality of the single-site conditional law**: if `η` and `η'` agree on every neighbour of
`x`, the single-site conditional up-probabilities at `x` coincide (the local field depends on the
boundary only through the neighbour spins). -/
theorem singleSiteUpProbBC_eq_of_agreesOn_neighbour (β J h : ℝ) (x : ι) {η η' : Config ι}
    (hagree : ∀ z ∈ G.neighborFinset x, η z = η' z) :
    singleSiteUpProbBC G β J h x η = singleSiteUpProbBC G β J h x η' := by
  rw [singleSiteUpProbBC, singleSiteUpProbBC, isingLocalField, isingLocalField,
    Finset.sum_congr rfl fun z hz => by rw [hagree z hz]]

omit [Fintype G.edgeSet] [DecidableEq ι] in
/-- **The telescoped boundary influence** (induction over neighbour sites): for `0 ≤ βJ` and a set
`T ⊆ nbr(x)`, if `σ` agrees with `η` on the neighbours of `x` outside `T`, then the single-site
conditional up-probabilities differ by at most `#T·tanh(βJ)`. Proved by flipping the sites of `T`
one at a time, each flip bounded by the single-neighbour influence. -/
private theorem singleSiteUpProbBC_dist_le_aux {β J : ℝ} (hβJ : 0 ≤ β * J) (h : ℝ) (x : ι)
    (η : Config ι) (T : Finset ι) (hT : T ⊆ G.neighborFinset x) (σ : Config ι)
    (hσ : ∀ z ∈ G.neighborFinset x, z ∉ T → η z = σ z) :
    |singleSiteUpProbBC G β J h x η - singleSiteUpProbBC G β J h x σ|
      ≤ (T.card : ℝ) * Real.tanh (β * J) := by
  classical
  induction T using Finset.induction_on generalizing σ with
  | empty =>
    rw [singleSiteUpProbBC_eq_of_agreesOn_neighbour G β J h x
      (fun z hz => hσ z hz (Finset.notMem_empty z)), sub_self, abs_zero]
    simp
  | @insert a T' ha ih =>
    have haT : a ∈ G.neighborFinset x := hT (Finset.mem_insert_self a T')
    have hT' : T' ⊆ G.neighborFinset x := (Finset.subset_insert a T').trans hT
    set τ := Function.update σ a (η a) with hτ
    have hagrτ : ∀ z ∈ G.neighborFinset x, z ∉ T' → η z = τ z := by
      intro z hz hzT'
      by_cases hza : z = a
      · subst hza; rw [hτ, Function.update_self]
      · rw [hτ, Function.update_of_ne hza]
        exact hσ z hz (fun hzins => hzT' ((Finset.mem_insert.mp hzins).resolve_left hza))
    have hflip : agreesOff {a} σ τ := by
      intro i hi
      have hia : i ≠ a := by simpa using hi
      rw [hτ, Function.update_of_ne hia]
    have h1 := ih hT' τ hagrτ
    have h2 := singleSiteUpProbBC_neighbour_dist_le G hβJ h x haT hflip
    have hcard : ((insert a T').card : ℝ) = (T'.card : ℝ) + 1 := by
      rw [Finset.card_insert_of_notMem ha]; push_cast; ring
    rw [hcard, add_mul, one_mul]
    calc |singleSiteUpProbBC G β J h x η - singleSiteUpProbBC G β J h x σ|
        ≤ |singleSiteUpProbBC G β J h x η - singleSiteUpProbBC G β J h x τ|
          + |singleSiteUpProbBC G β J h x σ - singleSiteUpProbBC G β J h x τ| := by
            rw [show singleSiteUpProbBC G β J h x η - singleSiteUpProbBC G β J h x σ
              = (singleSiteUpProbBC G β J h x η - singleSiteUpProbBC G β J h x τ)
                - (singleSiteUpProbBC G β J h x σ - singleSiteUpProbBC G β J h x τ) by ring]
            exact abs_sub _ _
      _ ≤ (T'.card : ℝ) * Real.tanh (β * J) + Real.tanh (β * J) := add_le_add h1 h2

omit [Fintype G.edgeSet] in
/-- **The multi-site boundary influence bound** (GJ §17.1): for `0 ≤ βJ`, two boundary
configurations agreeing off a set `S` change the single-site conditional up-probability at `x` by at
most
`#(S ∩ nbr(x))·tanh(βJ)` — the total influence of the differing boundary neighbours. -/
theorem singleSiteUpProbBC_agreesOff_dist_le {β J : ℝ} (hβJ : 0 ≤ β * J) (h : ℝ) (x : ι)
    {S : Finset ι} {η η' : Config ι} (hagree : agreesOff S η η') :
    |singleSiteUpProbBC G β J h x η - singleSiteUpProbBC G β J h x η'|
      ≤ ((S ∩ G.neighborFinset x).card : ℝ) * Real.tanh (β * J) := by
  refine singleSiteUpProbBC_dist_le_aux G hβJ h x η (S ∩ G.neighborFinset x)
    Finset.inter_subset_right η' (fun z hz hzSi => ?_)
  by_cases hzS : z ∈ S
  · exact absurd (Finset.mem_inter.mpr ⟨hzS, hz⟩) hzSi
  · exact (hagree z hzS).symm

/-- **The multi-site boundary comparison for a local observable** (GJ §17.1): if `f` is local at `x`
and the boundary configurations `η, η'` agree off `S`, the single-site conditional expectations
differ by at most `#(S ∩ nbr(x))·tanh(βJ)·siteOsc x f`. The boundary-direct term of the Dobrushin
comparison telescoping. -/
theorem gibbsExpectationBC_singleton_localObs_agreesOff_dist_le {β J : ℝ} (hβJ : 0 ≤ β * J) (h : ℝ)
    (x : ι) {S : Finset ι} {η η' : Config ι} (f : Config ι → ℝ) (hf : LocalAtSite x f)
    (hagree : agreesOff S η η') :
    |gibbsExpectationBC G β (fun _ => J) h {x} η f - gibbsExpectationBC G β (fun _ => J) h {x} η' f|
      ≤ ((S ∩ G.neighborFinset x).card : ℝ) * Real.tanh (β * J) * siteOsc x f := by
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
  have htanh : 0 ≤ Real.tanh (β * J) := real_tanh_nonneg hβJ
  exact mul_le_mul (singleSiteUpProbBC_agreesOff_dist_le G hβJ h x hagree)
    (abs_sub_update_le_siteOsc x f η) (abs_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) htanh)

end Dobrushin

end IsingModel
