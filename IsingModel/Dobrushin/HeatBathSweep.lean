import IsingModel.Dobrushin.OscillationPropagation

/-!
# The heat-bath Gibbs sweep and oscillation tracking (GJ §17.1, Issue #4214 §A)

The Dobrushin comparison theorem is proved by the Gibbs-sampler (heat-bath) telescoping: applying
the single-site operators `K_x` over the sites drives the observable's oscillation to zero under the
Dobrushin condition. Because the sweep **order** matters, the sweep is indexed by a `List` of sites,
not a `Finset`.

* `heatBathList` — the composite sweep `K_{x_n} ∘ ⋯ ∘ K_{x_1}` as a left fold over `xs`.
* `gibbsExpectationBC_heatBathList_invariant` — the finite-volume Gibbs measure is invariant under a
  sweep whose sites all lie in the free volume `Λ`.
* `heatBathOscStep` / `heatBathListOscBound` — the **oscillation-vector dynamics**: a single
  heat-bath step sends the oscillation vector `v` to `y ↦ (if y = x then 0 else v y + C_{xy}·v x)`;
  the sweep iterates this.
* `heatBathListOscBound_mono` — the oscillation-vector dynamics is monotone.
* `siteOsc_heatBathList_le_oscBound` — the per-site oscillation of a swept observable is bounded by
  the oscillation-vector dynamics applied to the initial oscillations, the key tracking estimate.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

/-- **The heat-bath Gibbs sweep** over a list of sites `xs`: the composite operator
`K_{x_n} ∘ ⋯ ∘ K_{x_1}`, applied left to right as a fold. -/
noncomputable def heatBathList (β J h : ℝ) (xs : List ι) (f : Config ι → ℝ) : Config ι → ℝ :=
  xs.foldl (fun g x => heatBath G β J h x g) f

omit [DecidableRel G.Adj] in
/-- **Sweep invariance of the finite-volume Gibbs measure** (GJ §17.1): if every site of the sweep
`xs` lies in the free volume `Λ`, then `⟨(K_{x_n}∘⋯∘K_{x_1}) f⟩^η_Λ = ⟨f⟩^η_Λ`. Iterates the
single-site invariance over the list. -/
theorem gibbsExpectationBC_heatBathList_invariant {Λ : Finset ι} (β J h : ℝ) (η : Config ι)
    (xs : List ι) :
    ∀ (f : Config ι → ℝ), (∀ y ∈ xs, y ∈ Λ) →
      gibbsExpectationBC G β (fun _ => J) h Λ η (heatBathList G β J h xs f)
        = gibbsExpectationBC G β (fun _ => J) h Λ η f := by
  induction xs with
  | nil => intro f _; rfl
  | cons x xs ih =>
    intro f hxs
    have htail : ∀ y ∈ xs, y ∈ Λ := fun y hy => hxs y (List.mem_cons.mpr (Or.inr hy))
    have hx : x ∈ Λ := hxs x (List.mem_cons.mpr (Or.inl rfl))
    -- `heatBathList (x :: xs) f` is definitionally `heatBathList xs (heatBath x f)`.
    change gibbsExpectationBC G β (fun _ => J) h Λ η
        (heatBathList G β J h xs (heatBath G β J h x f))
      = gibbsExpectationBC G β (fun _ => J) h Λ η f
    rw [ih (heatBath G β J h x f) htail]
    exact gibbsExpectationBC_heatBath_invariant G x hx β J h η f

/-- **One step of the oscillation-vector dynamics**: a heat-bath step at `x` zeroes the oscillation
at `x` and propagates `C_{xy}·v x` to every other site, `v ↦ (y ↦ if y = x then 0 else v y +
C_{xy}·v x)`. -/
noncomputable def heatBathOscStep (β J : ℝ) (x : ι) (v : ι → ℝ) : ι → ℝ :=
  fun y => if y = x then 0 else v y + isingInfluence G β J x y * v x

/-- **The oscillation-vector dynamics of a sweep**: iterate `heatBathOscStep` over `xs`. -/
noncomputable def heatBathListOscBound (β J : ℝ) (xs : List ι) (v : ι → ℝ) : ι → ℝ :=
  xs.foldl (fun w x => heatBathOscStep G β J x w) v

omit [Fintype G.edgeSet] in
/-- The empty-sweep oscillation bound is the identity. -/
theorem heatBathListOscBound_nil (β J : ℝ) (v : ι → ℝ) :
    heatBathListOscBound G β J [] v = v := rfl

omit [Fintype G.edgeSet] in
/-- The cons-sweep oscillation bound applies one step, then iterates. -/
theorem heatBathListOscBound_cons (β J : ℝ) (x : ι) (xs : List ι) (v : ι → ℝ) :
    heatBathListOscBound G β J (x :: xs) v
      = heatBathListOscBound G β J xs (heatBathOscStep G β J x v) := rfl

omit [Fintype G.edgeSet] in
/-- **Monotonicity of the oscillation-vector dynamics** (GJ §17.1): a pointwise-larger initial
oscillation vector stays pointwise-larger after any sweep (the dynamics is built from nonnegative
`C`-propagation). -/
theorem heatBathListOscBound_mono {β J : ℝ} (hβJ : 0 ≤ β * J) :
    ∀ (xs : List ι) {v w : ι → ℝ}, (∀ z, v z ≤ w z) →
      ∀ y, heatBathListOscBound G β J xs v y ≤ heatBathListOscBound G β J xs w y := by
  intro xs
  induction xs with
  | nil => intro v w hvw y; exact hvw y
  | cons x xs ih =>
    intro v w hvw y
    rw [heatBathListOscBound_cons, heatBathListOscBound_cons]
    refine ih ?_ y
    intro z
    by_cases hzx : z = x
    · simp [heatBathOscStep, hzx]
    · simp only [heatBathOscStep, hzx, if_false]
      exact add_le_add (hvw z)
        (mul_le_mul_of_nonneg_left (hvw x) (isingInfluence_nonneg G hβJ x z))

/-- **The sweep oscillation tracking estimate** (GJ §17.1): the per-site oscillation of a swept
observable is bounded by the oscillation-vector dynamics applied to the initial single-site
oscillations, `siteOsc y (K_{x_n}∘⋯∘K_{x_1} f) ≤ heatBathListOscBound xs (z ↦ siteOsc z f) y`. The
inductive engine of the Dobrushin comparison: at each step the new oscillation at `x` is zero
(`siteOsc_heatBath_self`) and the others grow by at most `C_{xz}·siteOsc x` (`siteOsc_heatBath_le`),
exactly the `heatBathOscStep`. -/
theorem siteOsc_heatBathList_le_oscBound {β J : ℝ} (hβJ : 0 ≤ β * J) (h : ℝ) (xs : List ι) :
    ∀ (f : Config ι → ℝ) (y : ι),
      siteOsc y (heatBathList G β J h xs f)
        ≤ heatBathListOscBound G β J xs (fun z => siteOsc z f) y := by
  induction xs with
  | nil => intro f y; exact le_rfl
  | cons x xs ih =>
    intro f y
    -- both sides unfold definitionally: `heatBathList (x::xs) f = heatBathList xs (heatBath x f)`
    -- and `heatBathListOscBound (x::xs) v = heatBathListOscBound xs (heatBathOscStep x v)`.
    change siteOsc y (heatBathList G β J h xs (heatBath G β J h x f))
      ≤ heatBathListOscBound G β J xs (heatBathOscStep G β J x (fun z => siteOsc z f)) y
    refine le_trans (ih (heatBath G β J h x f) y) ?_
    refine heatBathListOscBound_mono G hβJ xs (fun z => ?_) y
    by_cases hzx : z = x
    · subst hzx
      rw [siteOsc_heatBath_self]
      simp [heatBathOscStep]
    · simp only [heatBathOscStep, hzx, if_false]
      exact siteOsc_heatBath_le G hβJ h x z f

end Dobrushin

end IsingModel
